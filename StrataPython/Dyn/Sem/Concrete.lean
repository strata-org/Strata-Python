/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.MonadProps
public import StrataDyn.Exec.EffectsProps
public import StrataPython.Dyn.Sem.WorldProps
public import StrataPython.Dyn.Sem.StoreProps
public import StrataPython.Dyn.Sem.Basics
public import StrataPython.Dyn.Sem.DictLookup

set_option autoImplicit false

/-!
# The concrete primitives

Each primitive of the record (`Dom.lean`) as a `PyM` computation at its effect, with its proofs
that it satisfies every spec with the laws and stays within that effect.  The instances of the
record at `PyM σ e` lift a primitive to every higher effect (`Level.AtLeast`).

Key theorem: `same_depth`.  The lemmas on where the parts of the world hold refs are in
`MonadProps.lean`; the primitives' properties are in `ConcreteProps.lean`.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec Strata.Dyn.Exec.Effects

@[expose] public section

/-! ## The primitives -/

namespace Prim
variable {σ : Type} [Store σ] [Decode σ]

/-- A new object with the contents `o`; an object's class is never one whose values are always
immediates. -/
def alloc (o : ObjData) : PyM σ .pure true Value :=
  if o.cls.isImmClass then PyM.failure "an object of a class whose values are immediates"
  else
    ⟨fun _ _ _ k _ => do
      let n ← modifyGetThe (ObjStore σ) fun st => (st.size, (st.alloc o.lift).1)
      k (.obj n), by
      intro rs ps S tg V hc s hs hh e' _ β Q QW k ke hk hke
      exact ContOK.modifyGetThe _ hc.store (fun _ _ h => refsOK_alloc_lift o h)
        (fun _ w => same_allocObj s o.lift w)
        (fun _ _ _ h => ⟨immEq_allocObj o.lift h, congrArg (fun n => k (Value.obj n)) h.1⟩)
        (fun _ => hk _),
      by intro _; unfold StartFree; intros; rfl⟩

/-- A new object of the class `cls` with the contents `f id`, for its own id `id`, so that a class
can go first in its own MRO. -/
def allocWith (cls : Value) (f : ObjId → ObjData) : PyM σ .pure true Value :=
  if cls.isImmClass then PyM.failure "an object of a class whose values are immediates"
  else
    ⟨fun _ _ _ k _ => do
      let n ← modifyGetThe (ObjStore σ) fun st =>
        (st.size, (st.alloc ({ f st.size with cls } : ObjData).lift).1)
      k (.obj n), by
      intro rs ps S tg V hc s hs hh e' _ β Q QW k ke hk hke
      refine ContOK.modifyGetThe _ hc.store (fun _ _ h => refsOK_alloc_lift _ h)
        (fun _ w => same_allocObj s _ w) (fun _ w₁ w₂ h => ?_) (fun _ => hk _)
      have hsz : (HasPart.get w₁ : ObjStore σ).size = (HasPart.get w₂ : ObjStore σ).size := h.1
      refine ⟨?_, congrArg (fun n => k (Value.obj n)) hsz⟩
      have := immEq_allocObj ({ f (HasPart.get w₁ : ObjStore σ).size with cls } : ObjData).lift h
      rw [hsz] at this ⊢
      exact this,
      by intro _; unfold StartFree; intros; rfl⟩

/-- The object `id`, if it exists and is not a function object, whose closure no rule may see. -/
def objGet (id : ObjId) : PyM σ .reads true (Option ObjData) :=
  ⟨fun _ _ _ k _ => do
    let st ← getThe (ObjStore σ)
    k ((st.get? id).bind fun o => o.payload.data?.map fun p => { o with payload := p }), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    exact ContOK.getThe (fun _ => hk _) (fun h => absurd h (Level.ne_pure_up he (by decide))),
    by intro _; unfold StartFree; intros; rfl⟩

/-- The class of the object `id`, if it exists. -/
def objClass (id : ObjId) : PyM σ .pure true (Option Value) :=
  ⟨fun _ _ _ k _ => do
    let st ← getThe (ObjStore σ)
    k ((st.get? id).map (·.cls)), by
    intro rs ps S tg V hc s hs hh e' _ β Q QW k ke hk hke
    refine ContOK.getThe (fun _ => hk _) (fun _ w₁ w₂ h => ?_)
    by_cases hid : s.storeSize ≤ id
    · exact congrArg (fun x => k (Option.map (·.cls) x)) (h.2.1 id hid)
    · have := h.2.2.1 id (Nat.lt_of_not_le hid)
      have h' : (w₁.store.get? id).map (·.cls) = (w₂.store.get? id).map (·.cls) := by
        have e := congrArg (Option.map Prod.fst) this
        simpa [Option.map_map, Function.comp_def, Obj.imm] using e
      exact congrArg k h',
    by intro _; unfold StartFree; intros; rfl⟩

/-- The exception being handled. -/
def handledGet : PyM σ .reads true Value :=
  ⟨fun _ _ _ k _ => do
    let h ← getThe Handled
    k h.exc, by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    exact ContOK.getThe (fun _ => hk _) (fun h => absurd h (Level.ne_pure_up he (by decide))),
    by intro _; unfold StartFree; intros; rfl⟩

/-- `k` of the value of the global `name` of `module`, if its cell exists and is defined. -/
def globalGetT {ε : Eff} {E β : Type} [PyLang σ ε] (module name : String)
    (k : Option Value → Sem ε E β) : Sem ε E β := do
  let m ← getThe (Modules σ)
  match m.cell? module name with
  | some r =>
    let v : Value ← readRef r
    k (match v with | .undef _ => none | v => some v)
  | none => k none

/-- The value of the global `name` of `module`, if its cell exists and is defined. -/
def globalGet (module name : String) : PyM σ .reads true (Option Value) :=
  ⟨fun _ _ _ k _ => globalGetT module name k, by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    letI : Refs σ (Modules σ) := modulesRefs tg.value
    letI : TagOf σ Value := tg.value
    have hnp : e' ≠ .pure := Level.ne_pure_up he (by decide)
    refine ⟨fun g => ?_,
      fun N => ⟨fun _ w => .inr (Same.refl s w), (fun h => absurd h hnp), fun w => ?_⟩⟩
    · dsimp only [treeOf, globalGetT, Sem.bind, bind, pure, getThe, MonadStateOf.get,
        Sem.instMonadStateOf, Sem.bindAfter]
      refine Spec.sat_update.mpr fun w hw => ⟨hw, ?_⟩
      split
      · rename_i r hr
        have hv := valid_of_cell? tg.value (hc.modules.1 g w hw) hr
        exact Spec.sat_vis.mpr ⟨hc.heap.3 g r hv, fun g₁ _ _ _ => (hk _).1 g₁⟩
      · exact (hk _).1 g
    · dsimp only [treeOf, globalGetT, Sem.bind, bind, pure, getThe, MonadStateOf.get,
        Sem.instMonadStateOf, Sem.bindAfter]
      split
      · exact ⟨(fun h => absurd h hnp), fun _ => (hk _).2 N⟩
      · exact (hk _).2 N,
    by intro _; unfold StartFree; intros; rfl⟩

/-- Call the function object `id` with `args` and `kwargs`, one Python call deeper and outside any
call bracket, and go on with `k` of its result or `ke` of its exception: the depth is read before
the call and written back after it, so the call leaves it as it found it. -/
def callClosureT {ε : Eff} {E β : Type} [PyLang σ ε] (id : ObjId) (args kwargs : Value)
    (k : Value → Sem ε E β) (ke : Value → Sem ε E β) : Sem ε E β := do
  let st ← getThe (ObjStore σ)
  match ((st.get? id).map (·.payload) : Option (ObjPayload σ)) with
  | some (PayloadG.func f) =>
    -- The callee runs outside any call bracket: a bracket permits only the updates of the
    -- built-in body that opened it, not those of the rules that run in the Python code it calls.
    let d ← modifyGetThe Depth fun d => (d, { d with py := d.py + 1, bracket := 0 })
    let r ← callFn (s := funcSig (ε := ε)) f.closure (args, kwargs)
    modifyThe Depth fun _ => d
    contOf k ke r
  | _ => semanticGap s!"a call of an object that is not a function object is not modelled yet"

omit [Decode σ] in
/-- A change of the depth changes no protected state. -/
theorem same_depth (s : Start) (d : Depth) (w : World σ) :
    Same s w (HasPart.set w d : World σ) :=
  ⟨Nat.le_refl _, fun _ _ _ h => h, Modules.Extends.refl _, rfl, rfl⟩

omit [Decode σ] in
/-- A change of the `repr` guard changes no protected state. -/
theorem same_guard (s : Start) (g : ReprGuard) (w : World σ) :
    Same s w (HasPart.set w g : World σ) :=
  ⟨Nat.le_refl _, fun _ _ _ h => h, Modules.Extends.refl _, rfl, rfl⟩

/-- Call the function object `id` with `args` and `kwargs`, one Python call deeper. -/
def callClosure (id : ObjId) (args kwargs : Value) : PyM σ .calls true Value :=
  ⟨fun _ _ _ k ke => callClosureT id args kwargs k ke, by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    have hnp : e' ≠ .pure := Level.ne_pure_up he (by decide)
    letI : SigOf σ [Value, Value] (Except Value Value) := @funcSig σ _ _ (BEff σ rs) (bInst rs tg)
    have hck := ContOK.cont hk hke
    -- What runs after the call: the depth written back, then `k` or `ke` of the outcome.
    have hrest : ∀ (d : Depth) o, ContOK V s e' Q QW ((modifyThe Depth fun _ => d :
        BTree σ rs ps S Unit) >>= fun _ => contOf k ke o) := fun d o =>
      ContOK.modifyThe _ hc.depth (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_depth s _ w)
        (fun h => absurd h hnp) (hck _)
    refine ContOK.getTheWith hc.store (fun G st hst => ?_) (fun st N => ?_) (fun h => absurd h hnp)
    · -- The closure is read out of a store whose refs are valid, so the call is a valid request.
      dsimp only
      split
      · rename_i f hf
        have hclo := refsOK_closure hst hf
        rw [modifyGetThe_eq (ε := BEff σ rs) (P := Depth)]
        refine Spec.sat_update.mpr fun w hw =>
          ⟨hc.depth.2 G w _ hw (refsOK_nil rfl), Spec.sat_vis.mpr ⟨?_, fun G₁ _ o _ => (hrest _ _).1 G₁⟩⟩
        exact hc.call.1 G f.closure _ hclo (refsOK_nil rfl)
      · exact Spec.sat_fault
    · dsimp only
      split
      · rw [modifyGetThe_eq (ε := BEff σ rs) (P := Depth)]
        refine ContOK.within_update (fun _ w => same_depth s _ w) (fun h => absurd h hnp) ?_ N
        intro _ N
        exact ⟨Level.calls_up he (.inl rfl), fun o => (hrest _ _).2 N⟩
      · trivial,
    by intro _; unfold StartFree; intros; rfl⟩

/-- **The call bracket of a built-in that runs user code**: run `body`, a computation at
`writes`, with a bracket open, so that at `calls` it changes the world only inside the bracket and
stops with the gap `msg` where it would do anything else (`callBracket`), then close the bracket.
Each update that `body` makes counts as part of a call, as CPython's built-in method runs inside a
call of its own. -/
def bracketed {α : Type} (msg : String) (body : PyM σ .writes true α) : PyM σ .calls true α :=
  ⟨fun hs s _ k ke => do
    let d ← modifyGetThe Depth fun d => (d, { d with bracket := d.bracket + 1 })
    let r ← HasBracket.bracket msg
      (body.1 hs s (fun a => .ret (Except.ok a)) (fun x => .ret (Except.error x)))
    modifyThe Depth fun _ => d
    contOf k ke r, by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    have hnp : e' ≠ .pure := Level.ne_pure_up he (by decide)
    have hck := ContOK.cont hk hke
    refine ContOK.modifyGetThe _ hc.depth (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_depth s _ w)
      (fun h => absurd h hnp) (fun d => ?_)
    -- The body's tree, with continuations that return its outcome, satisfies `V` and is within
    -- `writes`.
    have hbody : ContOK V s .writes (fun _ _ => True) (fun _ _ => True)
        (treeOf body.1 rs ps S tg hs s (fun a => .ret (Except.ok a))
          (fun x => .ret (Except.error x))) :=
      body.2.1 rs ps S tg V hc s hs hh .writes (Nat.le_refl _) _ _ _ _
        (fun _ => ⟨fun _ => Spec.sat_ret.mpr trivial, fun _ => trivial⟩)
        (fun _ => ⟨fun _ => Spec.sat_ret.mpr trivial, fun _ => trivial⟩)
    have hx : TreeOK V s e' (callBracket HasInCall.inCall msg
        (treeOf body.1 rs ps S tg hs s (fun a => .ret (Except.ok a))
          (fun x => .ret (Except.error x)))) :=
      ⟨fun g => sat_callBracket _ msg _ (hbody.1 g),
        fun N => Within.lift (Level.le_trans (by decide) he)
          _ (Within.callBracket (sp := spec) msg _ (hbody.2 N))⟩
    exact ContOK.bind hx fun r =>
      ContOK.modifyThe _ hc.depth (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_depth s _ w)
        (fun h => absurd h hnp) (hck r),
    by intro hfr; unfold StartFree; intro ε E _ hs s s' β k ke
       simp only [body.2.2 rfl hs s s']⟩

/-- The depth of Python calls and CPython's C recursion count. -/
def depthGet : PyM σ .reads true Depth :=
  ⟨fun _ _ _ k _ => do
    let d ← getThe Depth
    k d, by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    exact ContOK.getThe (fun _ => hk _) (fun h => absurd h (Level.ne_pure_up he (by decide))),
    by intro _; unfold StartFree; intros; rfl⟩

/-- `body` with `Depth.c` raised by `n`, as CPython's `Py_EnterRecursiveCall` raises its count
around a nested level: a gap when the count would pass `cDepthLimit`, and the count back as it was
when `body` returns or raises. -/
def withDepth {e : Level} {fr : Bool} {α : Type} (hnp0 : e ≠ .pure) (n : Nat)
    (body : PyM σ e fr α) : PyM σ e fr α :=
  ⟨fun hs s _ k ke => do
    let d ← getThe Depth
    if cDepthLimit < d.c + n then semanticGap s!"a C recursion depth over {cDepthLimit}" else
    modifyThe Depth fun d' => { d' with c := d.c + n }
    body.1 hs s (fun a => do modifyThe Depth fun d' => { d' with c := d.c }; k a)
      (fun x => do modifyThe Depth fun d' => { d' with c := d.c }; ke x), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    have hnp : e' ≠ .pure := Level.ne_pure_up he hnp0
    refine ContOK.getThe (fun d => ?_) (fun h => absurd h hnp)
    split
    · exact ContOK.fault _
    · refine ContOK.modifyThe _ hc.depth (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_depth s _ w)
        (fun h => absurd h hnp) ?_
      exact body.2.1 rs ps S tg V hc s hs hh e' he Q QW _ _
        (fun a => ContOK.modifyThe _ hc.depth (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_depth s _ w)
          (fun h => absurd h hnp) (hk a))
        (fun x => ContOK.modifyThe _ hc.depth (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_depth s _ w)
          (fun h => absurd h hnp) (hke x)),
    by intro hfr; unfold StartFree; intro ε E _ hs s s' β k ke
       simp only [body.2.2 hfr hs s s']⟩

/-- The limit of the number of the program's Python frames, the module's included, below CPython's
1000. -/
def pyDepthLimit : Nat := 900

/-- `body` with `Depth.py` raised by `n`, as `n` Python frames: a gap when the count would pass
`pyDepthLimit`, as a call of a function object stops, and the count back as it was when `body`
returns or raises. -/
def withPyDepth {e : Level} {fr : Bool} {α : Type} (hnp0 : e ≠ .pure) (n : Nat)
    (body : PyM σ e fr α) : PyM σ e fr α :=
  ⟨fun hs s _ k ke => do
    let d ← getThe Depth
    if pyDepthLimit < d.py + n then semanticGap s!"Python call depth over {pyDepthLimit}" else
    modifyThe Depth fun d' => { d' with py := d.py + n }
    body.1 hs s (fun a => do modifyThe Depth fun d' => { d' with py := d.py }; k a)
      (fun x => do modifyThe Depth fun d' => { d' with py := d.py }; ke x), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    have hnp : e' ≠ .pure := Level.ne_pure_up he hnp0
    refine ContOK.getThe (fun d => ?_) (fun h => absurd h hnp)
    split
    · exact ContOK.fault _
    · refine ContOK.modifyThe _ hc.depth (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_depth s _ w)
        (fun h => absurd h hnp) ?_
      exact body.2.1 rs ps S tg V hc s hs hh e' he Q QW _ _
        (fun a => ContOK.modifyThe _ hc.depth (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_depth s _ w)
          (fun h => absurd h hnp) (hk a))
        (fun x => ContOK.modifyThe _ hc.depth (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_depth s _ w)
          (fun h => absurd h hnp) (hke x)),
    by intro hfr; unfold StartFree; intro ε E _ hs s s' β k ke
       simp only [body.2.2 hfr hs s s']⟩

/-- What `Py_ReprEnter` finds for the key `key` in the guard `g` (`ReprEntry`): an object by its id;
a tuple is `unknown` when a tuple with the same items is in the guard, and fresh otherwise, since
a tuple with other items is another tuple. -/
def reprEntryOf (g : ReprGuard) : ReprKey → ReprEntry
  | .obj id => if g.active.any (fun | .obj i => i == id | _ => false) then .hit else .fresh
  -- Comparing `nodes` first keeps a chain of nested tuples from comparing deeply at each level.
  | .tuple xs n =>
    if g.active.any (fun | .tuple ys n' => n' == n && ys == xs | _ => false) then .unknown else .fresh

/-- The key of `v` in the `repr` guard: an object by its id, any other value (a tuple) by its items. -/
def reprKeyOf : Value → ReprKey
  | .obj id => .obj id
  | .tuple xs => .tuple xs (Value.tuple xs).nodes
  | v => .tuple #[v] (Value.tuple #[v]).nodes

/-- What `Py_ReprEnter` finds for `key` in the `repr` guard. -/
def reprCheck (key : ReprKey) : PyM σ .reads true ReprEntry :=
  ⟨fun _ _ _ k _ => do
    let g ← getThe ReprGuard
    k (reprEntryOf g key), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    exact ContOK.getThe (fun _ => hk _) (fun h => absurd h (Level.ne_pure_up he (by decide))),
    by intro _; unfold StartFree; intros; rfl⟩

/-- `body` with `key` entered in the `repr` guard, as `Py_ReprEnter` enters it, and the guard back
as it was when `body` returns or raises (`Py_ReprLeave`). -/
def withRepr {e : Level} {fr : Bool} {α : Type} (hnp0 : e ≠ .pure) (key : ReprKey)
    (body : PyM σ e fr α) : PyM σ e fr α :=
  ⟨fun hs s _ k ke => do
    let g ← modifyGetThe ReprGuard fun g => (g, { active := g.active.push key })
    body.1 hs s (fun a => do modifyThe ReprGuard fun _ => g; k a)
      (fun x => do modifyThe ReprGuard fun _ => g; ke x), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    have hnp : e' ≠ .pure := Level.ne_pure_up he hnp0
    refine ContOK.modifyGetThe _ hc.guard (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_guard s _ w)
      (fun h => absurd h hnp) (fun g => ?_)
    exact body.2.1 rs ps S tg V hc s hs hh e' he Q QW _ _
      (fun a => ContOK.modifyThe _ hc.guard (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_guard s _ w)
        (fun h => absurd h hnp) (hk a))
      (fun x => ContOK.modifyThe _ hc.guard (fun _ _ _ => refsOK_nil rfl) (fun _ w => same_guard s _ w)
        (fun h => absurd h hnp) (hke x)),
    by intro hfr; unfold StartFree; intro ε E _ hs s s' β k ke
       simp only [body.2.2 hfr hs s s']⟩

/-- Set the exception being handled. -/
def setHandled (v : Value) : PyM σ .writes true Unit :=
  ⟨fun _ _ _ k _ => do
    modifyThe Handled fun _ => ⟨v⟩
    k (), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    obtain rfl := Level.writes_up he rfl
    exact ContOK.modifyThe _ hc.handled (fun _ _ _ => refsOK_nil rfl) (fun h => absurd rfl h) (fun h => nomatch h)
      (hk _),
    by intro _; unfold StartFree; intros; rfl⟩

/-- Write `text` to standard output. -/
def writeOut (text : String) : PyM σ .writes true Unit :=
  ⟨fun _ _ _ k _ => do
    modifyThe Output fun o => ⟨o.pieces.push text⟩
    k (), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    obtain rfl := Level.writes_up he rfl
    exact ContOK.modifyThe _ hc.out (fun _ _ _ => refsOK_nil rfl) (fun h => absurd rfl h) (fun h => nomatch h)
      (hk _),
    by intro _; unfold StartFree; intros; rfl⟩

/-- A number below `n + 1`, chosen: by the oracle when running, and any of them in a proof. -/
def choose (n : Nat) : PyM σ .reads true Nat :=
  ⟨fun _ _ _ k _ => .choose fun i => k (i % (n + 1)), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    exact ⟨fun g => Spec.sat_choose.mpr fun i => (hk _).1 g,
      fun N => ⟨Level.ne_pure_up he (by decide), fun i => (hk _).2 N⟩⟩,
    by intro _; unfold StartFree; intros; rfl⟩

/-- The contents of the object `id`, made since the start, if it exists and is not a function
object: a model invariant (`PyM.failure`) for an older object. -/
def ownData (id : ObjId) : PyM σ .pure false (Option ObjData) :=
  ⟨fun _ s _ k _ => if s.storeSize ≤ id then do
      let st ← getThe (ObjStore σ)
      k ((st.get? id).bind fun o => o.payload.data?.map fun p => { o with payload := p })
    else modelInvariant "a write to an object older than the operation", by
    intro rs ps S tg V hc s hs hh e' _ β Q QW k ke hk hke
    show ContOK V s e' Q QW (if s.storeSize ≤ id then _ else _)
    split
    · rename_i hid
      refine ContOK.getThe (fun st => hk _) (fun _ w₁ w₂ h => ?_)
      rw [show (HasPart.get w₁ : ObjStore σ).get? id = (HasPart.get w₂ : ObjStore σ).get? id
        from h.2.1 id hid]
    · exact ContOK.fault _,
    fun h => Bool.noConfusion h⟩

/-- Change the payload of the object `id`, made since the start, by `f`, in place: a
model invariant (`PyM.failure`) for an older object.  A container's write reads nothing of the old payload
after its last read, so that the payload is not shared and `f` changes it in place. -/
def modifyOwnPayload (id : ObjId) (f : ObjPayload σ → ObjPayload σ) (hf : KeepsClosures f) :
    PyM σ .pure false Unit :=
  ⟨fun _ s _ k _ => if s.storeSize ≤ id then do
      modifyThe (ObjStore σ) fun st => st.update id fun o => { o with payload := f o.payload }
      k ()
    else modelInvariant "a write to an object older than the operation", by
    intro rs ps S tg V hc s hs hh e' _ β Q QW k ke hk hke
    show ContOK V s e' Q QW (if s.storeSize ≤ id then _ else _)
    split
    · rename_i hid
      exact ContOK.modifyThe _ hc.store (fun _ _ h => refsOK_update id _ (keepsClosures_obj hf) h)
        (fun _ w => same_updObj hid _ w)
        (fun _ _ _ h => immEq_updObj hid _ h) (hk _)
    · exact ContOK.fault _,
    fun h => Bool.noConfusion h⟩

/-- Change the payload of the object `id` by `f`, in place. -/
def modifyPayload (id : ObjId) (f : ObjPayload σ → ObjPayload σ) (hf : KeepsClosures f) :
    PyM σ .writes true Unit :=
  ⟨fun _ _ _ k _ => do
    modifyThe (ObjStore σ) fun st => st.update id fun o => { o with payload := f o.payload }
    k (), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    obtain rfl := Level.writes_up he rfl
    exact ContOK.modifyThe _ hc.store (fun _ _ h => refsOK_update id _ (keepsClosures_obj hf) h)
      (fun h => absurd rfl h) (fun h => nomatch h)
      (hk _),
    by intro _; unfold StartFree; intros; rfl⟩

/-- The dict table of the object `id`, which the operation made: a model invariant (`PyM.failure`)
for an older object, or one that is not a dict. -/
def ownDict (id : ObjId) : PyM σ .pure false DictTable := do
  match ← ownData id with
  | some { payload := .dict t, .. } => pure t
  | _ => PyM.failure s!"object {id} is not a dict"

/-- A new list of the elements `xs`. -/
def allocList (xs : Array Value) : PyM σ .pure true Value :=
  alloc ⟨.builtin .list, none, #[], .list xs 0⟩

/-- The elements of the object `id`'s list part, and its resize count. -/
def listOf (d : Option ObjData) : Option (Array Value × Nat) :=
  match d with
  | some { payload := .list xs n, .. } => some (xs, n)
  | _ => none

/-- A change of a list's elements and resize count: whether it applies to a list of a given
length, and the change, which runs in place on a list that is not shared. -/
structure ListChange where
  ok : Nat → Bool
  run : Array Value → Nat → Array Value × Nat

/-- `xs` with element `i` set to `v`. -/
def ListChange.set (i : Nat) (v : Value) : ListChange :=
  ⟨(i < ·), fun xs n => (xs.setIfInBounds i v, n)⟩

/-- `xs` with `v` appended: its length changes. -/
def ListChange.append (v : Value) : ListChange := ⟨fun _ => true, fun xs n => (xs.push v, n + 1)⟩

/-- `xs` with the elements from `lo` to `hi` replaced by `ys`; the resize count moves when the
length changes.  A splice that reaches the end of the list runs in place: the list is cut at `lo`,
then `ys` is appended. -/
def ListChange.splice (lo hi : Nat) (ys : Array Value) : ListChange :=
  ⟨fun size => lo ≤ hi && hi ≤ size, fun xs n =>
    (if hi = xs.size then xs.shrink lo ++ ys
      else xs.extract 0 lo ++ ys ++ xs.extract hi xs.size,
      if hi - lo = ys.size then n else n + 1)⟩

/-- A preallocation for `k` more elements: the resize count moves when `k > 0`. -/
def ListChange.reserve (k : Nat) : ListChange :=
  ⟨fun _ => true, fun xs n => (xs, if k > 0 then n + 1 else n)⟩

/-- Apply `f` to the list `l`, which the operation made. -/
def listChangeNew (l : Value) (f : ListChange) : PyM σ .pure false Unit := do
  let .obj id := l | PyM.failure "a list write to a value that is not an object"
  let some (xs, _) := listOf (← ownData id) | PyM.failure s!"object {id} is not a list"
  if !f.ok xs.size then PyM.failure "a list write out of range"
  modifyOwnPayload id (PayloadG.modList f.run) (keepsClosures_modList _)

/-- Apply `f` to the list `l`. -/
def listChange (l : Value) (f : ListChange) : PyM σ .writes true Unit := do
  let .obj id := l | PyM.failure "a list write to a value that is not an object"
  let some (xs, _) := listOf (← (objGet id).lift (by decide)) |
    PyM.failure s!"object {id} is not a list"
  if !f.ok xs.size then PyM.failure "a list write out of range"
  modifyPayload id (PayloadG.modList f.run) (keepsClosures_modList _)

/-- `type(v)`. -/
def classOf (v : Value) : PyM σ .reads true Value := do
  match v with
  | .obj id =>
    match ← (objClass id).lift (by decide) with
    | some c => pure c
    | none => PyM.failure s!"object {id} does not exist"
  | v =>
    match v.classOfImm with
    | some c => pure c
    | none => PyM.gap "type() of an unassigned value"

/-- `v` as an immediate; `none` for an object or an unassigned value. -/
def immView (v : Value) : PyM σ .pure true (Option (Imm Value)) :=
  match v with
  | .obj _ | .undef _ => pure none
  | v => match v.toImm? with
    | some i => pure (some i)
    | none => PyM.failure "a symbolic int whose source holds an object's address"

/-- The hash of the address of the object `v`. -/
def addrHash (v : Value) : PyM σ .pure true Hash :=
  match v with
  | .obj id => pure (.symbolic (.addr id))
  | _ => PyM.gap "the address hash of a value that is not an object is not modelled yet"

/-- A new exception of the class `cls` with the arguments `args`, the fields `fields` and the
`__context__` `context`, and the opaque traceback. -/
def allocExc (cls : Value) (args : Array Value) (fields : Array (String × Value))
    (context : Value) : PyM σ .pure true Value :=
  alloc ⟨cls, none, #[], .exc { args := .tuple args, context, traceback := .traceback, fields }⟩

/-- A new empty dict. -/
def allocDict : PyM σ .pure true Value := alloc ⟨.builtin .dict, none, #[], .dict .empty⟩

/-- A new exception of the class `cls` with the arguments `args` and the fields `fields`, its
`__context__` the exception being handled, raised. -/
def raiseNew {α : Type} (cls : Value) (args : Array Value) (fields : Array (String × Value)) :
    PyM σ .reads true α := do
  let h ← handledGet
  let x ← (allocExc cls args fields h).lift (by decide)
  throw x

/-- The stronger of two key classes, in the order `builtin`, `symHash`, `user`. -/
def _root_.StrataPython.Dyn.Sem.KeyClass.join (a b : KeyClass) : KeyClass :=
  if compare a b == .lt then b else a

/-- The key class of `v`, decided by what can't change: an object of exactly a built-in type is
`builtin`, except a frozenset, which compares its members and counts as `user`; any other object
is `user`; a tuple or a slice takes the strongest class of its members. -/
def keyClassOf (v : Value) : PyM σ .pure true KeyClass :=
  match v with
  | .obj id => do
    match ← objClass id with
    | some (.builtin b) => pure (if b == .frozenset then .user else .builtin)
    | some _ => pure .user
    | none => PyM.failure s!"object {id} does not exist"
  | .tuple xs => xs.attach.foldlM (fun acc ⟨x, _⟩ => do pure (acc.join (← keyClassOf x))) .builtin
  | .slice a b c => do pure (((← keyClassOf a).join (← keyClassOf b)).join (← keyClassOf c))
  | .symHash _ => pure .symHash
  | _ => pure .builtin
termination_by sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ xs›; omega)

/-- Whether `v` holds tuples or slices nested more than `n` deep. -/
def _root_.StrataPython.Dyn.Sem.Value.deeperThan : Nat → Value → Bool
  | 0, .tuple _ | 0, .slice .. => true
  | n + 1, .tuple xs => xs.any (·.deeperThan n)
  | n + 1, .slice a b c => a.deeperThan n || b.deeperThan n || c.deeperThan n
  | _, _ => false

/-- The depth of nested tuples and slices that a key of a dict or set may have.  CPython compares
nested keys until its C recursion limit, near a depth of 10000, and then raises `RecursionError`;
a deeper key stops with a gap.  The primitives compare a key's levels without counting them on
`Depth.c`: a key's comparison needs at most `keyDepth + 1` levels, fewer than the 995 between
`cDepthLimit` and CPython's limit, so a comparison that the model finishes doesn't raise in
CPython. -/
def keyDepth : Nat := 900

/-- The key class and the hash of the key `k`: `h?` is the hash combinator's result for a key
that is or holds an object, and `none` for a key whose hash is computed here; a given hash must
equal the one computed here.  A key nested deeper than `keyDepth` is a gap. -/
def probeOf (k : Value) (h? : Option Hash) : PyM σ .pure true (KeyClass × Hash) := do
  if k.deeperThan keyDepth then PyM.gap "a key nested deeper than the model follows"
  let kc ← keyClassOf k
  match k.immHash, h? with
  | .hash h, none => pure (kc, h)
  | .hash h, some h' =>
    if h == h' then pure (kc, h) else PyM.failure "a given hash that differs from the key's own"
  | .needsStore, some h | .unknown, some h => pure (kc, h)
  | .needsStore, none => match k with
    | .obj _ => PyM.failure "an object key without its hash"
    | _ => PyM.gap "the hash of a key that holds an object is not modelled yet"
  | .unhashable, _ => PyM.gap "an unhashable dict key is not modelled yet"
  | .unknown, none => PyM.gap "the hash of this dict key is not modelled yet"

/-- The dict table of the object `id`. -/
def dictOf (id : ObjId) : PyM σ .reads true DictTable := do
  match ← objGet id with
  | some { payload := .dict t, .. } => pure t
  | _ => PyM.failure s!"object {id} is not a dict"

/-- Whether the dict table `t` holds no key of class `user` or `symHash`, from its group counts:
then a read of a `str` key compares no key that can run user code, and draws no choice. -/
def _root_.StrataPython.Dyn.Sem.DictTable.plainKeys (t : DictTable) : Bool :=
  [HashKind.exact, .addr, .otherSymbolic].all fun k =>
    t.groupCount k .user == 0 && t.groupCount k .symHash == 0

/-- The value of the `str` key `name` in the dict table `t`, for a table whose keys are
`plainKeys`: only an exact `str` equals it, and the other keys of its hash compare without code. -/
def _root_.StrataPython.Dyn.Sem.DictTable.strEntry? (t : DictTable) (name : String) :
    Option Value :=
  let k : Value := .str (.ofString name)
  (t.positions (strHash (.ofString name))).toList.findSome? fun i =>
    (t.entry? i).bind fun en => if en.key == k then some (t.value i) else none

/-- The dict table of the dict object `id`, if its keys are `plainKeys`. -/
def plainDict? (id : ObjId) : PyM σ .reads true (Option DictTable) := do
  match ← objGet id with
  | some { payload := .dict t, .. } => pure (if t.plainKeys then some t else none)
  | _ => pure none

/-- The entry `name` of the class object `c`'s namespace: `some none` when there is none, and
`none` when it can't be read without running code (a gapped name, or a namespace with a key of
class `user` or `symHash`). -/
def nsEntry? (c : ClassObj) (name : String) : PyM σ .reads true (Option (Option Value)) := do
  if c.gapped.contains name then return none
  return (← plainDict? c.ns).map (·.strEntry? name)

/-- The classes of the MRO of the class `cls`, if every class of it but its last is a class object
of the store without slots of its own, and the last is `object`: then its instances have
`object`'s layout. -/
def plainMro? (cls : Value) : PyM σ .reads true (Option (Array ClassObj)) := do
  let .obj cid := cls | return none
  let some { payload := .cls c, .. } ← objGet cid | return none
  let some (.builtin .«object») := c.mro.back? | return none
  let mut out : Array ClassObj := #[]
  for b in c.mro.pop do
    let .obj bid := b | return none
    let some { payload := .cls bc, .. } ← objGet bid | return none
    if !bc.slots.isEmpty then return none
    out := out.push bc
  return some out

/-- The entry `name` of the first class of `mro` that has one: `some none` when none has, and
`none` when a namespace can't be read. -/
def mroEntry? (mro : Array ClassObj) (name : String) :
    PyM σ .reads true (Option (Option Value)) := do
  for c in mro do
    match ← nsEntry? c name with
    | none => return none
    | some (some v) => return some (some v)
    | some none => pure ()
  return some none

/-- Whether `v` is the generated native `key` (`dataclasses.__eq__` or `dataclasses.__hash__`)
of the class `cls` itself: its first captured value is `cls`.  Its captured values, if so. -/
def generatedOf? (v : Value) (key : String) (cls : ObjId) :
    PyM σ .reads true (Option (Array Value)) := do
  let .obj nid := v | return none
  let some { payload := .native f, .. } ← objGet nid | return none
  if f.key != key then return none
  match (f.captured[generatedClsSlot]? : Option Value) with
  | some (.obj c) => return if c == cls then some f.captured else none
  | _ => return none

/-- Whether a class attribute `v` under a compared name is read without running code: no
attribute at all, or an immediate whose class has no `__get__` (`None`, `NotImplemented`,
`Ellipsis`, a `bool`, an `int`, a `float`, a `str`, a `bytes`, a tuple, a `range` or a `slice`).
Only its kind matters: the object's own `__dict__` holds every compared field and wins over such an
attribute, so its contents are never read. -/
def plainClassAttr (v : Option Value) : Bool :=
  match v with
  | none => true
  | some v => match v with
    | .none | .notImplemented | .ellipsis | .bool _ | .int _ | .float _ | .str _ | .bytes _
    | .tuple _ | .range .. | .slice .. => true
    | _ => false

/-- `NotImplemented` as the generated `__eq__` of a class of module `module` reads it: the
module's global, then the builtins'; `none` when the builtins can't be read without running
code. -/
def notImplementedOf? (module : String) : PyM σ .reads true (Option Value) := do
  if let some v ← globalGet module "NotImplemented" then return some v
  return (← plainDict? 0).bind (·.strEntry? "NotImplemented")

/-- The compared field names and their values of the object `id`, if its class `cls` passes every
check of a dataclass whose equality is fixed and runs no user code: its `__eq__` and `__hash__`
are its own generated natives; its MRO holds user classes with `object`'s layout, then `object`;
no class of it but `object` defines `__getattribute__`, `__getattr__` or `__class__`, or has an
attribute under a compared name that `plainClassAttr` rejects; `NotImplemented` is the constant; and
every compared field is in the object's own `__dict__`, whose keys are `plainKeys`. -/
def dataclassFields? (id : ObjId) (cls : Value) : PyM σ .reads true (Option (Array Value)) := do
  let .obj cid := cls | return none
  let some mro ← plainMro? cls | return none
  let some (some eqv) ← mroEntry? mro "__eq__" | return none
  let some (some hashv) ← mroEntry? mro "__hash__" | return none
  let some eqCap ← generatedOf? eqv generatedEqKey cid | return none
  let some _ ← generatedOf? hashv generatedHashKey cid | return none
  let some (.tuple namesV) := (eqCap[generatedNamesSlot]? : Option Value) | return none
  let some (.str modS) := (eqCap[generatedModuleSlot]? : Option Value) | return none
  let names := namesV.filterMap fun | .str s => some s.s | _ => none
  if names.size != namesV.size then return none
  for n in #["__getattribute__", "__getattr__", "__class__"] do
    let some none ← mroEntry? mro n | return none
  for n in names do
    for c in mro do
      let some e ← nsEntry? c n | return none
      if !plainClassAttr e then return none
  let some .notImplemented ← notImplementedOf? modS.s | return none
  let some { dict := some did, .. } ← objGet id | return none
  let some t ← plainDict? did | return none
  let mut vals : Array Value := #[]
  for n in names do
    let some v := t.strEntry? n | return none
    vals := vals.push v
  return some vals

/-- The number of values that one lookup's `structuralKeys` may enter, over all its keys; past it,
the answer is `false`, which keeps the lookup's gap.  It bounds the walk's time and stack. -/
def structuralBudget : Nat := 4096

/-- What `structuralKeys` keeps across its keys: the answers of the objects already checked, and
how many more values it may enter. -/
structure StructuralWalk where
  memo : Std.HashMap ObjId Bool := ∅
  left : Nat := structuralBudget

/-- `structuralKeys` of one value, with `fuel` levels of objects and tuples; an object met again
while it is still being checked (on `path`) is not structural, as `==` on it would recurse without
end. -/
def structuralWalk : Nat → Array ObjId → StructuralWalk → Value →
    PyM σ .reads true (Bool × StructuralWalk)
  | 0, _, w, _ => pure (false, w)
  | fuel + 1, path, w, v => do
    if w.left == 0 then return (false, w)
    let w := { w with left := w.left - 1 }
    -- A tuple or a `slice` is walked here, not by `Value.structuralImm?`, so that the budget
    -- counts every element: a tuple whose two members are one tuple, at each of n levels, is a
    -- tree of 2^n values.
    match v with
      | .tuple xs => do
        let mut w := w
        for x in xs do
          let (r, w') ← structuralWalk fuel path w x
          w := w'
          if !r then return (false, w)
        return (true, w)
      | .slice a b c => do
        let mut w := w
        for x in [a, b, c] do
          let (r, w') ← structuralWalk fuel path w x
          w := w'
          if !r then return (false, w)
        return (true, w)
      | .obj id => do
        if let some r := w.memo[id]? then return (r, w)
        if path.contains id then return (false, w)
        let no := { w with memo := w.memo.insert id false }
        let some cls ← objClass id |>.lift Level.AtLeast.le | return (false, no)
        let some vals ← dataclassFields? id cls | return (false, no)
        let mut w := w
        for x in vals do
          let (r, w') ← structuralWalk fuel (path.push id) w x
          w := w'
          if !r then return (false, { w with memo := w.memo.insert id false })
        return (true, { w with memo := w.memo.insert id true })
      | v => return (v.structuralImm? == some true, w)

/-- **Whether the equality of the probe `k` and of each of the keys `ks` is fixed and runs no user
code**, read from the store without running code: each is a value that `Value.structuralImm?`
admits, a tuple or a `slice` of such values, or an instance of a dataclass that `dataclassFields?`
admits whose compared field values are structural in turn.  One walk checks them all and keeps
each object's answer, so an object shared by several keys is checked once.  An object first
checked within `keyDepth` levels is accepted again when a deeper path reaches it, so the walk
doesn't bound how deep a comparison recurses.  The generated `__eq__` charges a Python frame at
each level, so a comparison that recurses too deep stops with a gap at `pyDepthLimit`.  Past
`structuralBudget` values in all, the answer is `false`. -/
def structuralKeys (k : Value) (ks : List Value) : PyM σ .reads true Bool := do
  let mut w : StructuralWalk := {}
  for v in k :: ks do
    let (r, w') ← structuralWalk keyDepth #[] w v
    w := w'
    if !r then return false
  return true

section
variable {e : Level} {fr : Bool}

/-- The position of the entry `k` in the dict that `read` gives, as `dictLookup` finds it, with
the key's class and hash. -/
def dictLocate (read : PyM σ e fr DictTable) (choose? : Option (Nat → PyM σ e fr Nat))
    (k : Value) (h? : Option Hash) (eq : Value → PyM σ e fr Bool)
    (structural : Value → List Value → PyM σ e fr Bool := fun _ _ => pure false) :
    PyM σ e fr (Option Nat × KeyClass × Hash) := do
  let t ← read
  let (kc, h) ← (probeOf k h?).relax.lift Level.AtLeast.le
  let ops : LookupOps (PyM σ e fr) := ⟨PyM.gap, choose?, eq, (·.keysVersion) <$> read, structural⟩
  pure (← dictLookup ops t k kc h, kc, h)

/-- The value of the entry `k` of the dict `d`, as `dictLookup` finds it, read after the lookup,
whose comparisons may change it. -/
def dictFind [Level.AtLeast .reads e] (d k : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) : PyM σ e fr (Option Value) := do
  let .obj id := d | PyM.failure "a dict lookup in a value that is not an object"
  let read : PyM σ e fr DictTable := (dictOf id).relax.lift Level.AtLeast.le
  match (← dictLocate read (some fun n => (choose n).relax.lift Level.AtLeast.le) k h? eq
      fun v vs => (structuralKeys v vs).relax.lift Level.AtLeast.le).1 with
  | some i => pure (some ((← read).value i))
  | none => pure none

/-- Set the entry `k` of the dict that `read` gives to `v`, with `modify`: replace the value of the
key that `dictLookup` finds, or add the key.  The change applies to the table as it is after the
lookup, whose comparisons may change the values. -/
def dictSetWith (read : PyM σ e fr DictTable) (modify : (DictTable → DictTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (k v : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) (structural : Value → List Value → PyM σ e fr Bool := fun _ _ => pure false) :
    PyM σ e fr Unit := do
  -- CPython converts a table of `str` keys before the lookup, whose comparisons may raise.
  modify (·.noteKey k)
  match (← dictLocate read choose? k h? eq structural) with
  | (some i, _, _) => modify (·.setValue i v)
  | (none, kc, h) => modify (·.insertNew ⟨h, k, kc⟩ v)

/-- Delete the entry `k` of the dict that `read` gives, with `modify`, and give its value. -/
def dictDeleteWith (read : PyM σ e fr DictTable) (modify : (DictTable → DictTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (k : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) (structural : Value → List Value → PyM σ e fr Bool := fun _ _ => pure false) :
    PyM σ e fr (Option Value) := do
  match (← dictLocate read choose? k h? eq structural).1 with
  | some i =>
    let v := (← read).value i
    modify (·.deleteAt i)
    pure (some v)
  | none => pure none

/-- Remove the last entry of the dict that `read` gives, with `modify`, and give it. -/
def dictPopitemWith (read : PyM σ e fr DictTable)
    (modify : (DictTable → DictTable) → PyM σ e fr Unit) : PyM σ e fr (Option (Value × Value)) := do
  match (← read).popitemAt? with
  | some (i, en, v) =>
    modify (·.removePopped i)
    pure (some (en.key, v))
  | none => pure none

/-- `dictSetWith` on a dict that the operation made; where a choice would be needed at `pure`,
a gap. -/
def dictSetNew (d k v : Value) (h? : Option Hash) (eq : Value → PyM σ e false Bool) :
    PyM σ e false Unit := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  dictSetWith ((ownDict id).lift Level.AtLeast.le) (fun f => (modifyOwnPayload id (PayloadG.modDict f) (keepsClosures_modDict _)).lift Level.AtLeast.le)
    (if h : Level.reads.le e then some fun n => (choose n).relax.lift h else none) k v h? eq
    (if h : Level.reads.le e then fun x xs => (structuralKeys x xs).relax.lift h else fun _ _ => pure false)

end

/-- `dictDeleteWith` on a dict that the operation made. -/
def dictDeleteNew {e : Level} (d k : Value) (h? : Option Hash) (eq : Value → PyM σ e false Bool) :
    PyM σ e false (Option Value) := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  dictDeleteWith ((ownDict id).lift Level.AtLeast.le)
    (fun f => (modifyOwnPayload id (PayloadG.modDict f) (keepsClosures_modDict _)).lift Level.AtLeast.le)
    (if h : Level.reads.le e then some fun n => (choose n).relax.lift h else none) k h? eq
    (if h : Level.reads.le e then fun x xs => (structuralKeys x xs).relax.lift h else fun _ _ => pure false)

/-- `dictPopitemWith` on a dict that the operation made. -/
def dictPopitemNew {e : Level} (d : Value) : PyM σ e false (Option (Value × Value)) := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  dictPopitemWith ((ownDict id).lift Level.AtLeast.le)
    (fun f => (modifyOwnPayload id (PayloadG.modDict f) (keepsClosures_modDict _)).lift Level.AtLeast.le)

/-- `dictSetWith` on any dict. -/
def dictSet {fr : Bool} (d k v : Value) (h? : Option Hash) (eq : Value → PyM σ .writes fr Bool) :
    PyM σ .writes fr Unit := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  dictSetWith ((dictOf id).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modDict f) (keepsClosures_modDict _)).relax)
    (some fun n => (choose n).relax.lift (by decide)) k v h? eq
    fun x xs => (structuralKeys x xs).relax.lift (by decide)

/-- `dictDeleteWith` on any dict. -/
def dictDelete {fr : Bool} (d k : Value) (h? : Option Hash) (eq : Value → PyM σ .writes fr Bool) :
    PyM σ .writes fr (Option Value) := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  dictDeleteWith ((dictOf id).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modDict f) (keepsClosures_modDict _)).relax)
    (some fun n => (choose n).relax.lift (by decide)) k h? eq
    fun x xs => (structuralKeys x xs).relax.lift (by decide)

/-- `dictPopitemWith` on any dict. -/
def dictPopitem {fr : Bool} (d : Value) : PyM σ .writes fr (Option (Value × Value)) := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  dictPopitemWith ((dictOf id).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modDict f) (keepsClosures_modDict _)).relax)

/-- Empty the dict `d`. -/
def dictClear (d : Value) : PyM σ .writes true Unit := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  let _ ← (dictOf id).lift (by decide)
  modifyPayload id (PayloadG.modDict (·.clear)) (keepsClosures_modDict _)

/-- The dict table of `d`. -/
def dictTable (d : Value) : PyM σ .reads true DictTable := do
  let .obj id := d | PyM.failure "a dict read of a value that is not an object"
  dictOf id

/-- Position `i` of the entry array of the dict `d`. -/
def dictEntryAt (d : Value) (i : Nat) : PyM σ .reads true (EntryAt Value) := do
  let t ← dictTable d
  if i < t.entries.size then
    match t.entry? i with
    | some en => pure (.entry en.key (t.value i) en.hash)
    | none => pure .hole
  else pure .past

/-- A new dict with the table `t`. -/
def allocDictOf (t : DictTable) : PyM σ .pure true Value :=
  alloc ⟨.builtin .dict, none, #[], .dict t⟩

/-- A new dict with the live entries of `d` at the positions `i` with `keep i`, in order. -/
def allocDictFrom (d : Value) (keep : Nat → Bool) : PyM σ .reads true Value := do
  let t ← dictTable d
  let kept := t.live.zipIdx.filterMap fun ((en, v), i) => if keep i then some (en, v) else none
  (allocDictOf (kept.foldl (fun acc (en, v) => acc.insertNew en v) .empty)).lift (by decide)

/-! ## Sets -/

/-- The table of a set or frozenset payload, and whether it is a frozenset. -/
def setOf (d : Option ObjData) : Option (SetTable × Bool) :=
  match d with
  | some { payload := .set t, .. } => some (t, false)
  | some { payload := .frozenset t _, .. } => some (t, true)
  | _ => none

/-- The payload of a set with the table `t`; a frozenset is `closed` or still open. -/
def setData (t : SetTable) (frozen : Bool) (closed : Bool := true) : PayloadData :=
  if frozen then .frozenset t closed else .set t

/-- The table of the set `s`, and whether it is a frozenset. -/
def setRead (s : Value) : PyM σ .reads true (SetTable × Bool) := do
  let .obj id := s | PyM.failure "a set read of a value that is not an object"
  let some r := setOf (← objGet id) | PyM.failure s!"object {id} is not a set"
  pure r

/-- A new set with the table `t`; a frozenset is `closed` or still open. -/
def allocSetOf (t : SetTable) (frozen : Bool) (closed : Bool := true) : PyM σ .pure true Value :=
  alloc ⟨.builtin (if frozen then .frozenset else .set), none, #[], setData t frozen closed⟩

/-- A new empty set; a frozenset is open, to be filled and then closed (`setFreeze`). -/
def allocSet (frozen inexact : Bool) : PyM σ .pure true Value :=
  allocSetOf { SetTable.empty with inexact } frozen (closed := false)

/-- `t` resized when its dummies fill more than a quarter of its slots (`fill - used > mask / 4`),
for `used * 4` members (`used * 2` above 50,000): the last step of CPython's
`set_difference_update_internal`. -/
def _root_.StrataPython.Dyn.Sem.SetTable.trim (t : SetTable) : SetTable :=
  if t.fill - t.used > t.mask / 4 then t.resize (if t.used > 50000 then t.used * 2 else t.used * 4)
  else t

/-- `t` resized for `n` more members, as `set_merge` and `set_update_internal` resize a set before
they add the members of another set or of a dict. -/
def _root_.StrataPython.Dyn.Sem.SetTable.reserve (t : SetTable) (n : Nat) : SetTable :=
  if (t.fill + n) * 5 ≥ t.mask * 3 then t.resize ((t.used + n) * 2) else t

/-- Whether a member of the set table `t` may run user code when compared. -/
def _root_.StrataPython.Dyn.Sem.SetTable.hasUser (t : SetTable) : Bool :=
  [HashKind.exact, .addr, .otherSymbolic].any fun k => t.groupCount k .user != 0

/-- The kinds of the members of the set table `t`, for `WalkKinds.mayRunUser`. -/
def _root_.StrataPython.Dyn.Sem.SetTable.walkKinds (t : SetTable) : WalkKinds :=
  { userAddr := t.groupCount .addr .user != 0,
    userOther := t.groupCount .exact .user != 0 || t.groupCount .otherSymbolic .user != 0,
    nonAddr := t.kindGroupCount .exact != 0 || t.kindGroupCount .otherSymbolic != 0 }

/-- The kinds of the keys of the dict table `t`, for `WalkKinds.mayRunUser`. -/
def _root_.StrataPython.Dyn.Sem.DictTable.walkKinds (t : DictTable) : WalkKinds :=
  { userAddr := t.groupCount .addr .user != 0,
    userOther := t.groupCount .exact .user != 0 || t.groupCount .otherSymbolic .user != 0,
    nonAddr := t.kindGroupCount .exact != 0 || t.kindGroupCount .otherSymbolic != 0 }

/-- Whether a key of the dict table `t` may run user code when compared. -/
def _root_.StrataPython.Dyn.Sem.DictTable.hasUser (t : DictTable) : Bool :=
  [HashKind.exact, .addr, .otherSymbolic].any fun k => t.groupCount k .user != 0

/-- `t`, resized as `set_merge` first resizes a set before merging `src` into it. -/
def _root_.StrataPython.Dyn.Sem.SetTable.mergeResize (t src : SetTable) : SetTable :=
  t.reserve src.used

/-- The table of the set `t`, which has no entries or dummies, with the members of `src` merged
in: `set_merge`'s copy of the slots when the sizes agree and `src` has no dummies, and else its
`set_insert_clean` of each member. -/
def _root_.StrataPython.Dyn.Sem.SetTable.copyInto (t src : SetTable) : SetTable :=
  let inexact := t.inexact || src.inexact
  if t.mask == src.mask && src.fill == src.used then
    { slots := src.slots, fill := src.fill, used := src.used, finger := t.finger, inexact,
      version := t.version + 1, groups := .build src.slots, kindGroups := .build src.slots }
  else
    let slots := src.slots.foldl (fun acc x => match x with
      | .entry h _ _ => SetTable.insertClean acc h.placement x
      | _ => acc) t.slots
    { slots, fill := src.used, used := src.used, finger := t.finger, inexact,
      version := t.version + 1, groups := .build slots, kindGroups := .build slots }

/-- The table of the set `t` with the members of `src` merged in, for a `t` without entries or
dummies: `set_merge`'s two paths that compare nothing, after its resize. -/
def _root_.StrataPython.Dyn.Sem.SetTable.mergeIntoEmpty (t src : SetTable) : SetTable :=
  (t.mergeResize src).copyInto src

section
variable {e : Level} {fr : Bool}

/-- The slot of the member `k` in the set that `read` gives, as `setLookup` finds it, with the
key's class and hash. -/
def setLocate (read : PyM σ e fr SetTable) (choose? : Option (Nat → PyM σ e fr Nat))
    (k : Value) (h? : Option Hash) (eq : Value → PyM σ e fr Bool)
    (structural : Value → List Value → PyM σ e fr Bool := fun _ _ => pure false) :
    PyM σ e fr (Option Nat × KeyClass × Hash) := do
  let t ← read
  let (kc, h) ← (probeOf k h?).relax.lift Level.AtLeast.le
  let ops : LookupOps (PyM σ e fr) := ⟨PyM.gap, choose?, eq, pure 0, structural⟩
  let unchanged : PyM σ e fr Bool := (fun t' => t'.version == t.version) <$> read
  pure (← setLookup ops unchanged t k kc h, kc, h)

/-- Add `k` to the set that `read` gives, with `modify`, unless it is there. -/
def setAddWith (read : PyM σ e fr SetTable) (modify : (SetTable → SetTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (k : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) (structural : Value → List Value → PyM σ e fr Bool := fun _ _ => pure false) :
    PyM σ e fr Unit := do
  let (found, kc, h) ← setLocate read choose? k h? eq structural
  if found.isSome then return
  let some s := (← read).search h | PyM.failure "a set table without an empty slot"
  modify (·.addNew s h k kc)

/-- Remove `k` from the set that `read` gives, with `modify`; whether it was there. -/
def setDiscardWith (read : PyM σ e fr SetTable) (modify : (SetTable → SetTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (k : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) (structural : Value → List Value → PyM σ e fr Bool := fun _ _ => pure false) :
    PyM σ e fr Bool := do
  match (← setLocate read choose? k h? eq structural).1 with
  | some i =>
    modify (·.discardAt i)
    pure true
  | none => pure false

/-- `set.pop` of the set that `read` gives, with `modify`. -/
def setPopWith (read : PyM σ e fr SetTable) (modify : (SetTable → SetTable) → PyM σ e fr Unit) :
    PyM σ e fr (Option Value) := do
  let t ← read
  -- `pop` takes the first member from the finger on, in table order, which is CPython's only for an
  -- exact layout.
  if !t.exactLayout && t.used ≥ 2 then
    PyM.gap "set.pop of a set whose order is not CPython's is not modelled yet"
  match t.popAt? with
  | some (i, _, k) =>
    modify (·.removePopped i)
    pure (some k)
  | none => pure none

/-- A gap if walking the table `src` while comparing with the members of `t` could run user code:
CPython walks the live table, which user code may change, and the model walks `src` as it was. -/
def walkGuard (src t : SetTable) : PyM σ e fr Unit := do
  if WalkKinds.mayRunUser [src.walkKinds, t.walkKinds] then
    PyM.gap "a walk of a set whose comparisons may run user code is not modelled yet"

/-- After members were added in the order of the table `src`, mark the set that `read` gives
inexact if that order is not CPython's. -/
def markWalk (src : SetTable) (modify : (SetTable → SetTable) → PyM σ e fr Unit) :
    PyM σ e fr Unit := do
  if src.inexact && src.used ≥ 2 then modify ({ · with inexact := true })

/-- CPython's `set_merge` of the table `src` into the set that `read` gives, with `modify`. -/
def setMergeWith (read : PyM σ e fr SetTable) (modify : (SetTable → SetTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (src : SetTable)
    (eq : Value → Value → PyM σ e fr Bool) : PyM σ e fr Unit := do
  if src.used == 0 then return
  modify (·.mergeResize src)
  if (← read).fill == 0 then return ← modify (·.copyInto src)
  walkGuard src (← read)
  for (_, h, k) in src.active do setAddWith read modify choose? k (some h) (eq k)
  markWalk src modify

/-- CPython's `set_difference_update_internal` of the table `src` into the set that `read`
gives: each member of `src` discarded, in `src`'s order, then the dummies resized away when they
fill more than a quarter of the table; the set is emptied if `src` is that set (`same`). -/
def setSubtractWith (read : PyM σ e fr SetTable) (modify : (SetTable → SetTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (src : SetTable) (same : Bool)
    (eq : Value → Value → PyM σ e fr Bool) : PyM σ e fr Unit := do
  if same then return ← modify (·.clear)
  walkGuard src (← read)
  for (_, h, k) in src.active do discard <| setDiscardWith read modify choose? k (some h) (eq k)
  modify (·.trim)

/-- CPython's `set_symmetric_difference_update` of the table `src` into the set that `read`
gives: each member of `src`, in `src`'s order, discarded if the set has it and else added; the set
is emptied if `src` is that set (`same`). -/
def setSymUpdateWith (read : PyM σ e fr SetTable) (modify : (SetTable → SetTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (src : SetTable) (same : Bool)
    (eq : Value → Value → PyM σ e fr Bool) : PyM σ e fr Unit := do
  if same then return ← modify (·.clear)
  walkGuard src (← read)
  for (_, h, k) in src.active do
    if !(← setDiscardWith read modify choose? k (some h) (eq k)) then
      setAddWith read modify choose? k (some h) (eq k)
  markWalk src modify

end

/-- The table of the set `id`, which the operation made, and whether it is a frozenset. -/
def ownSet (id : ObjId) : PyM σ .pure false (SetTable × Bool) := do
  let d ← ownData id
  if d matches some { payload := .frozenset _ true, .. } then
    PyM.failure s!"a write to the closed frozenset {id}"
  let some r := setOf d | PyM.failure s!"object {id} is not a set"
  pure r

/-- The table of the set `id`, to change it, and whether it is a frozenset: a model invariant
(`PyM.failure`) for a frozenset unless `af`, which the writes to new objects at `PyM σ .writes true`
pass. -/
def mutSet (id : ObjId) (af : Bool) : PyM σ .reads true (SetTable × Bool) := do
  match ← objGet id with
  | some { payload := .set t, .. } => pure (t, false)
  | some { payload := .frozenset t false, .. } =>
    if af then pure (t, true) else PyM.failure s!"a write to the frozenset {id}"
  | some { payload := .frozenset _ true, .. } => PyM.failure s!"a write to the closed frozenset {id}"
  | _ => PyM.failure s!"object {id} is not a set"

/-- Close the frozenset `s`, which the operation made open: from then on it takes no writes. A
closed one stays closed. -/
def setFreeze (s : Value) : PyM σ .writes true Unit := do
  let .obj id := s | PyM.failure "a frozenset that is not an object"
  match ← (objGet id).lift (by decide) with
  | some { payload := .frozenset _ _, .. } =>
    modifyPayload id (fun
      | .frozenset t _ => .frozenset t true
      | q => q) (by keeps_closures)
  | _ => PyM.failure s!"object {id} is not a frozenset"

/-- The object id of `s`. -/
def setId {e : Level} {fr : Bool} (s : Value) : PyM σ e fr ObjId :=
  match s with
  | .obj id => pure id
  | _ => PyM.failure "a set operation on a value that is not an object"

section
variable {e : Level}

/-- The choices at the level `e`, if it allows them. -/
def choicesAt (e : Level) : Option (Nat → PyM σ e false Nat) :=
  if h : Level.reads.le e then some fun n => (choose n).relax.lift h else none

/-- `setAddWith` on a set that the operation made. -/
def setAddNew (s k : Value) (h? : Option Hash) (eq : Value → PyM σ e false Bool) :
    PyM σ e false Unit := do
  let id ← setId s
  let _ ← (ownSet id).lift Level.AtLeast.le
  setAddWith (Prod.fst <$> (ownSet id).lift Level.AtLeast.le)
    (fun f => (modifyOwnPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).lift Level.AtLeast.le) (choicesAt e) k h? eq
    (if h : Level.reads.le e then fun x xs => (structuralKeys x xs).relax.lift h else fun _ _ => pure false)

/-- `setDiscardWith` on a set that the operation made. -/
def setDiscardNew (s k : Value) (h? : Option Hash) (eq : Value → PyM σ e false Bool) :
    PyM σ e false Bool := do
  let id ← setId s
  let _ ← (ownSet id).lift Level.AtLeast.le
  setDiscardWith (Prod.fst <$> (ownSet id).lift Level.AtLeast.le)
    (fun f => (modifyOwnPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).lift Level.AtLeast.le) (choicesAt e) k h? eq
    (if h : Level.reads.le e then fun x xs => (structuralKeys x xs).relax.lift h else fun _ _ => pure false)

/-- `setPopWith` on a set that the operation made. -/
def setPopNew (s : Value) : PyM σ e false (Option Value) := do
  let id ← setId s
  let _ ← (ownSet id).lift Level.AtLeast.le
  setPopWith (Prod.fst <$> (ownSet id).lift Level.AtLeast.le)
    (fun f => (modifyOwnPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).lift Level.AtLeast.le)

/-- The table of the set `s`, at a level that reads; a gap at `pure`. -/
def setReadAt (s : Value) : PyM σ e false (SetTable × Bool) :=
  if h : Level.reads.le e then (setRead s).relax.lift h
  else PyM.gap "reading a set at the level pure"

/-- `setMergeWith` of the set `src` into the set `s`, which the operation made. -/
def setMergeNew (s src : Value) (eq : Value → Value → PyM σ e false Bool) :
    PyM σ e false Unit := do
  let id ← setId s
  let (st, _) ← setReadAt src
  if src == s then return
  let _ ← (ownSet id).lift Level.AtLeast.le
  setMergeWith (Prod.fst <$> (ownSet id).lift Level.AtLeast.le)
    (fun f => (modifyOwnPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).lift Level.AtLeast.le) (choicesAt e) st eq

/-- `setSubtractWith` of the set `src` from the set `s`, which the operation made. -/
def setSubtractNew (s src : Value) (eq : Value → Value → PyM σ e false Bool) :
    PyM σ e false Unit := do
  let id ← setId s
  let (st, _) ← setReadAt src
  let _ ← (ownSet id).lift Level.AtLeast.le
  setSubtractWith (Prod.fst <$> (ownSet id).lift Level.AtLeast.le)
    (fun f => (modifyOwnPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).lift Level.AtLeast.le) (choicesAt e) st (src == s) eq

/-- `setSymUpdateWith` of the set `src` into the set `s`, which the operation made. -/
def setSymUpdateNew (s src : Value) (eq : Value → Value → PyM σ e false Bool) :
    PyM σ e false Unit := do
  let id ← setId s
  let (st, _) ← setReadAt src
  let _ ← (ownSet id).lift Level.AtLeast.le
  setSymUpdateWith (Prod.fst <$> (ownSet id).lift Level.AtLeast.le)
    (fun f => (modifyOwnPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).lift Level.AtLeast.le) (choicesAt e) st (src == s) eq

/-- Resize the set `s`, which the operation made, for `n` more members. -/
def setReserveNew (s : Value) (n : Nat) : PyM σ e false Unit := do
  let id ← setId s
  let _ ← (ownSet id).lift Level.AtLeast.le
  (modifyOwnPayload id (PayloadG.modSet (·.reserve n)) (keepsClosures_modSet _)).lift Level.AtLeast.le

/-- Resize the set `s`, which the operation made, if its dummies fill more than a quarter of it. -/
def setTrimNew (s : Value) : PyM σ e false Unit := do
  let id ← setId s
  let _ ← (ownSet id).lift Level.AtLeast.le
  (modifyOwnPayload id (PayloadG.modSet (·.trim)) (keepsClosures_modSet _)).lift Level.AtLeast.le

/-- Empty the set `s`, which the operation made. -/
def setClearNew (s : Value) : PyM σ e false Unit := do
  let id ← setId s
  let _ ← (ownSet id).lift Level.AtLeast.le
  (modifyOwnPayload id (PayloadG.modSet (·.clear)) (keepsClosures_modSet _)).lift Level.AtLeast.le

/-- Close the frozenset `s`, which the operation made. -/
def setFreezeNew (s : Value) : PyM σ e false Unit := do
  let .obj id := s | PyM.failure "a frozenset that is not an object"
  match ← (ownData id).lift Level.AtLeast.le with
  | some { payload := .frozenset _ _, .. } =>
    (modifyOwnPayload id (fun
      | .frozenset t _ => .frozenset t true
      | q => q) (by keeps_closures)).lift Level.AtLeast.le
  | _ => PyM.failure s!"object {id} is not a frozenset"

/-- Give the set `s`, which the operation made, the table of the set `t`, `inexact` included,
keeping its own finger. -/
def setReplaceNew (s t : Value) : PyM σ e false Unit := do
  let id ← setId s
  let (tt, _) ← setReadAt t
  let _ ← (ownSet id).lift Level.AtLeast.le
  -- The set's own version goes on counting, so that a lookup never sees an old version again.
  (modifyOwnPayload id (PayloadG.modSet fun old => { tt with finger := old.finger, version := old.version + 1 })
    (keepsClosures_modSet _)).lift Level.AtLeast.le

end

section
variable {fr : Bool}

/-- `setAddWith` on any set; a frozenset only if `af`. -/
def setAdd (af : Bool) (s k : Value) (h? : Option Hash) (eq : Value → PyM σ .writes fr Bool) :
    PyM σ .writes fr Unit := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  setAddWith ((Prod.fst <$> mutSet id af).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).relax)
    (some fun n => (choose n).relax.lift (by decide)) k h? eq
    fun x xs => (structuralKeys x xs).relax.lift (by decide)

/-- `setDiscardWith` on any set; a frozenset only if `af`. -/
def setDiscard (af : Bool) (s k : Value) (h? : Option Hash) (eq : Value → PyM σ .writes fr Bool) :
    PyM σ .writes fr Bool := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  setDiscardWith ((Prod.fst <$> mutSet id af).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).relax)
    (some fun n => (choose n).relax.lift (by decide)) k h? eq
    fun x xs => (structuralKeys x xs).relax.lift (by decide)

/-- `setPopWith` on any set; a frozenset only if `af`. -/
def setPop (af : Bool) (s : Value) : PyM σ .writes fr (Option Value) := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  setPopWith ((Prod.fst <$> mutSet id af).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).relax)

/-- `setMergeWith` of the set `src` into any set `s`; a frozenset only if `af`. -/
def setMerge (af : Bool) (s src : Value) (eq : Value → Value → PyM σ .writes fr Bool) : PyM σ .writes fr Unit := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  let (st, _) ← (setRead src).relax.lift (by decide)
  if src == s then return
  setMergeWith ((Prod.fst <$> mutSet id af).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).relax)
    (some fun n => (choose n).relax.lift (by decide)) st eq

/-- `setSubtractWith` of the set `src` from any set `s`; a frozenset only if `af`. -/
def setSubtract (af : Bool) (s src : Value) (eq : Value → Value → PyM σ .writes fr Bool) :
    PyM σ .writes fr Unit := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  let (st, _) ← (setRead src).relax.lift (by decide)
  setSubtractWith ((Prod.fst <$> mutSet id af).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).relax)
    (some fun n => (choose n).relax.lift (by decide)) st (src == s) eq

/-- `setSymUpdateWith` of the set `src` into any set `s`; a frozenset only if `af`. -/
def setSymUpdate (af : Bool) (s src : Value) (eq : Value → Value → PyM σ .writes fr Bool) :
    PyM σ .writes fr Unit := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  let (st, _) ← (setRead src).relax.lift (by decide)
  setSymUpdateWith ((Prod.fst <$> mutSet id af).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).relax)
    (some fun n => (choose n).relax.lift (by decide)) st (src == s) eq

/-- Resize any set `s` for `n` more members; a frozenset only if `af`. -/
def setReserve (af : Bool) (s : Value) (n : Nat) : PyM σ .writes fr Unit := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  (modifyPayload id (PayloadG.modSet (·.reserve n)) (keepsClosures_modSet _)).relax

/-- Resize any set `s` if its dummies fill more than a quarter of it; a frozenset only if `af`. -/
def setTrim (af : Bool) (s : Value) : PyM σ .writes fr Unit := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  (modifyPayload id (PayloadG.modSet (·.trim)) (keepsClosures_modSet _)).relax

/-- Empty any set `s`; a frozenset only if `af`. -/
def setClear (af : Bool) (s : Value) : PyM σ .writes fr Unit := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  (modifyPayload id (PayloadG.modSet (·.clear)) (keepsClosures_modSet _)).relax

/-- Give any set `s` the table of the set `t`; a frozenset only if `af`. -/
def setReplace (af : Bool) (s t : Value) : PyM σ .writes fr Unit := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  let (tt, _) ← (setRead t).relax.lift (by decide)
  -- The set's own version goes on counting, so that a lookup never sees an old version again.
  (modifyPayload id (PayloadG.modSet fun old => { tt with finger := old.finger, version := old.version + 1 })
    (keepsClosures_modSet _)).relax

end

/-- What the set `s` holds, if it is a set or a frozenset. -/
def setViewOf (s : Value) : PyM σ .reads true (Option (SetView Value)) := do
  let .obj id := s | pure none
  let d ← objGet id
  -- An open frozenset is not a value yet: its maker must close it (`setFreeze`) before it escapes.
  if d matches some { payload := .frozenset _ false, .. } then
    PyM.failure s!"a read of the frozenset {id}, which is still open"
  let some (t, _) := setOf d | pure none
  pure (some ⟨(t.active.map fun (_, h, k) => (k, h)).toArray, t.exactLayout,
    (t.kindGroupCount .exact, t.kindGroupCount .addr, t.kindGroupCount .otherSymbolic)⟩)

/-- Whether `s` is a set whose order the model knows: `setViewOf`'s `exact`, without its walk. -/
def setExactOf (s : Value) : PyM σ .reads true Bool := do
  let .obj id := s | pure false
  let d ← objGet id
  if d matches some { payload := .frozenset _ false, .. } then
    PyM.failure s!"a read of the frozenset {id}, which is still open"
  let some (t, _) := setOf d | pure false
  pure t.exactLayout

/-- A new set with the members of `s`, as `set_merge` into an empty set puts them. -/
def setCopy (s : Value) (frozen : Bool) : PyM σ .reads true Value := do
  let (t, _) ← setRead s
  (allocSetOf (SetTable.empty.mergeIntoEmpty t) frozen).lift (by decide)

/-- Slot `i` of the table of the set `s`. -/
def setSlotAt (s : Value) (i : Nat) : PyM σ .reads true (SlotAt Value) := do
  let (t, _) ← setRead s
  if t.inexact then PyM.gap "a slot of a set whose layout is inexact"
  if i ≥ t.slots.size then return .past
  match t.slot i with
  | .entry h k _ => pure (.entry k h)
  | _ => pure .hole

/-! ## Objects other than containers -/

/-- The payload of a new object `id` with the contents `o`, if its references are objects where
they must be (a class's namespace). -/
def newPayload (id : ObjId) : NewObj Value → Option PayloadData
  | .cls c => match c.ns with
    | .obj n => some <| .cls
        { name := c.name, qualname := c.qualname, «module» := c.module, bases := c.bases,
          mro := #[.obj id] ++ c.mroTail, ns := n, solidBase := c.solidBase,
          instanceDict := c.instanceDict, slots := c.slots, immutable := c.immutable,
          gapped := c.gapped, writesGap := c.writesGap, instanceWritesGap := c.instanceWritesGap,
          tpName := c.tpName, hasDel := c.hasDel, asBase := c.asBase, cType := c.cType }
    | _ => none
  | .native f => some <| .native
      { key := f.key, kind := f.kind, captured := f.captured, name := f.name,
        qualname := f.qualname, «module» := f.module, defaults := f.defaults,
        kwdefaults := f.kwdefaults, gapped := f.gapped, owner := f.owner }
  | .module n g w a => some (.module ⟨n, g, w, .made a⟩)
  | .property a b c d => some (.property a b c d)
  | .classmethod f => some (.classmethod f)
  | .staticmethod f => some (.staticmethod f)
  | .super t o => some (.super t o)
  | .opaque t st => some (.opaque t st)
  | .member o n i => some (.member o n i)
  | .mappingProxy d o => some (.mappingProxy d o)
  | .dictProxy d => some (.dictProxy d)
  | .iter it => some (.iter it none)

/-- A new object of the class `cls` with the contents `o`. -/
def allocObj (cls : Value) (o : NewObj Value) : PyM σ .pure true Value :=
  if (newPayload 0 o).isNone then PyM.failure "a new object whose namespace is not a dict"
  else allocWith cls fun id => ⟨cls, none, #[], (newPayload id o).getD .plain⟩

/-- The class `c` of an object, as generic code sees it. -/
def classDataOf (c : ClassObj) : ClassData Value :=
  { name := c.name, qualname := c.qualname, «module» := c.module, bases := c.bases,
    mroTail := c.mro.extract 1 c.mro.size, ns := .obj c.ns, solidBase := c.solidBase,
    instanceDict := c.instanceDict, slots := c.slots, immutable := c.immutable,
    gapped := c.gapped, writesGap := c.writesGap, instanceWritesGap := c.instanceWritesGap,
    tpName := c.tpName, hasDel := c.hasDel, asBase := c.asBase, cType := c.cType }

/-- What the payload `p` is, other than a container. -/
def viewOf : PayloadData → ObjView Value
  | .cls c => .cls (classDataOf c)
  | .native f => .native
      { key := f.key, kind := f.kind, captured := f.captured, name := f.name,
        qualname := f.qualname, «module» := f.module, defaults := f.defaults,
        kwdefaults := f.kwdefaults, gapped := f.gapped, owner := f.owner }
  | .exc e => .exc ⟨e.args, e.context, e.cause, e.suppressContext, e.traceback, e.fields⟩
  | .iter it _ => .iter it
  | .module m => .module m.name m.gapped m.writesGap m.kind
  | .property a b c d => .property a b c d
  | .classmethod f => .classmethod f
  | .staticmethod f => .staticmethod f
  | .super t o => .super t o
  | .opaque t st => .opaque t st
  | .member o n i => .member o n i
  | .mappingProxy d o => .mappingProxy d o
  | .dictProxy d => .dictProxy d
  | _ => .inst

/-- What the store object `o` is, other than a container; a translated function shows its name
and module only, never its closure. -/
def viewOfObj (o : Obj σ) : ObjView Value :=
  match o.payload with
  | .func f => .func f.name f.module f.annotations f.classBody
  | p => (p.data?.map viewOf).getD .inst

/-- What the object `v` is, other than a container. -/
def objView (v : Value) : PyM σ .reads true (Option (ObjView Value)) :=
  match v with
  | .obj id =>
    ⟨fun _ _ _ k _ => do
      let st ← getThe (ObjStore σ)
      k ((st.get? id).map viewOfObj), by
      intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
      exact ContOK.getThe (fun _ => hk _)
        (fun h => absurd h (Level.ne_pure_up he (by decide))),
      by intro _; unfold StartFree; intros; rfl⟩
  | _ => pure none

/-- The payload of a new instance's built-in part. -/
def partPayload : BuiltinPart Value → PayloadData
  | .plain => .plain
  | .list xs => .list xs 0
  | .dict => .dict .empty
  | .set => .set .empty
  | .frozenset => .frozenset .empty false
  | .tuple xs => .tuple xs
  | .str x => .str x
  | .int i => .int i
  | .float b => .float b
  | .bytes b => .bytes b
  | .exc args => .exc { args := .tuple args }

/-- The number of slots of the classes `mro`, which is a class's MRO: its instances' layout. -/
def slotCount : List Value → PyM σ .reads true Nat
  | [] => pure 0
  | .obj id :: rest => do
    let own ← match ← objGet id with
      | some { payload := .cls c, .. } => pure c.slots.size
      | _ => pure 0
    return own + (← slotCount rest)
  | _ :: rest => slotCount rest

/-- Whether the instances of the class `cls` get a `__dict__`, and their number of slots. -/
def layoutOf (cls : Value) : PyM σ .reads true (Bool × Nat) := do
  match cls with
  | .obj id => match ← objGet id with
    | some { payload := .cls c, .. } => return (c.instanceDict, ← slotCount c.mro.toList)
    | _ => PyM.failure s!"object {id} is not a class"
  | _ => pure (false, 0)

/-- A dict table with the entries `kvs`, whose keys are `str`s, in order. -/
def strTable (kvs : Array (String × Value)) : PyM σ .pure true DictTable :=
  kvs.foldlM (init := .empty) fun t (k, v) => do
    let key := Value.ofString k
    let (kc, h) ← probeOf key none
    pure (t.insertNew ⟨h, key, kc⟩ v)

/-- A new instance of the class `cls` with the built-in part `p`, its `__dict__`'s first entries
`dict` and its slot values `slots`. -/
def allocInstance (cls : Value) (p : BuiltinPart Value) (dict : Array (String × Value))
    (slots : Array (Option Value)) : PyM σ .reads true Value := do
  let (hasDict, n) ← layoutOf cls
  if !hasDict && !dict.isEmpty then PyM.failure "dict entries for a class without an instance dict"
  if slots.size != n then PyM.failure "slot values that don't fit the class's layout"
  if (dict.map (·.1)).toList.eraseDups.length != dict.size then
    PyM.failure "an instance dict that repeats a name"
  let d ← if hasDict then
      some <$> ((do allocDictOf { ← strTable dict with inexact := true, split := true }) :
        PyM σ .pure true Value).lift (by decide)
    else pure none
  let dictId := match d with | some (.obj i) => some i | _ => none
  (alloc ⟨cls, dictId, slots.map (·.getD (.undef "")), partPayload p⟩).lift (by decide)

/-- Give the class `id`'s MRO after itself `tail`, as `modify` changes a payload. -/
def withMroTail (id : ObjId) (tail : Array Value) : ObjPayload σ → ObjPayload σ
  | .cls c => .cls { c with mro := #[.obj id] ++ tail }
  | p => p

/-- Give the class `c`, which the operation made, the MRO `tail` after itself. -/
def classSetMroNew (c : Value) (tail : Array Value) : PyM σ .pure false Unit :=
  match c with
  | .obj id => modifyOwnPayload id (withMroTail id tail) (by keeps_closures)
  | _ => PyM.failure "a class that is not an object"

/-- Give any class `c` the MRO `tail` after itself. -/
def classSetMro (c : Value) (tail : Array Value) : PyM σ .writes true Unit :=
  match c with
  | .obj id => modifyPayload id (withMroTail id tail) (by keeps_closures)
  | _ => PyM.failure "a class that is not an object"

/-- Set the `__name__` and `__qualname__` of the class `c`. -/
def classSetName (c : Value) (name qualname : String) : PyM σ .writes true Unit :=
  match c with
  | .obj id => modifyPayload id (fun
    | .cls k => .cls { k with name, qualname }
    | p => p) (by keeps_closures)
  | _ => PyM.failure "a class that is not an object"

/-- Set the `__annotations__` of the function `f`. -/
def funcSetAnnotations (f : Value) (a : Value) : PyM σ .writes true Unit :=
  match f with
  | .obj id => modifyPayload id (fun
    | .func fo => .func { fo with annotations := some a }
    | p => p) (by keeps_closures)
  | _ => PyM.failure "a function that is not an object"

/-- Set the state of the property, `classmethod` or `staticmethod` `v` to `s`, of the same kind;
a model invariant (`PyM.failure`) for any other kind. -/
def stateSet (v : Value) (s : NewObj Value) : PyM σ .writes true Unit := do
  let .obj id := v | PyM.failure "an object's state for a value that is not an object"
  let some o ← (objGet id).lift (by decide) | PyM.failure s!"object {id} does not exist"
  match o.payload, s with
  | .property .., .property a b c d => modifyPayload id (fun _ => .property a b c d) (by keeps_closures)
  | .classmethod _, .classmethod f => modifyPayload id (fun _ => .classmethod f) (by keeps_closures)
  | .staticmethod _, .staticmethod f => modifyPayload id (fun _ => .staticmethod f) (by keeps_closures)
  | _, _ => PyM.failure "an object's state of another kind"

/-- `e`'s exception state with the part `p` written; `__cause__` also sets
`__suppress_context__`, as `PyException_SetCause` does. -/
def _root_.StrataPython.Dyn.Sem.ExcState.write (e : ExcState) : ExcPart Value → ExcState
  | .args v => { e with args := v }
  | .context v => { e with context := v }
  | .cause v => { e with cause := v, suppressContext := true }
  | .suppressContext b => { e with suppressContext := b }
  | .traceback v => { e with traceback := v }
  | .field n v => { e with fields := e.fields.filter (·.1 != n) ++ (v.map (n, ·)).toArray }

/-- Write the part `p` of the state of the exception `e`. -/
def excSet (e : Value) (p : ExcPart Value) : PyM σ .writes true Unit := do
  let .obj id := e | PyM.failure "an exception that is not an object"
  let some o ← (objGet id).lift (by decide) | PyM.failure s!"object {id} does not exist"
  let .exc _ := o.payload | PyM.failure s!"object {id} is not an exception"
  modifyPayload id (fun
    | .exc st => .exc (st.write p)
    | q => q) (by keeps_closures)

/-- Set the state of the iterator `it` to `s`, dropping its byte offset of a `str`. -/
def iterSet (it : Value) (s : IterState) : PyM σ .writes true Unit :=
  match it with
  | .obj id => modifyPayload id (fun
      | .iter _ _ => .iter s none
      | q => q) (by keeps_closures)
  | _ => PyM.failure "an iterator that is not an object"

/-- The byte offset of the character `i` of `s`, found from the start. -/
def strBytePos (s : String) (i : Nat) : String.Pos.Raw :=
  (List.range i).foldl (fun p _ => String.Pos.Raw.next s p) 0

/-- **The next character of the `str` iterator `it`**, or `none` at its end, and the iterator moved
on. A non-ASCII `str` keeps the byte offset of the next character in the iterator's payload, so
that each step takes constant time; an ASCII one is indexed by byte. -/
def strIterNext (it : Value) : PyM σ .writes true (Option Value) := do
  let .obj id := it | PyM.failure "a str iterator that is not an object"
  let some { payload := .iter (.seq kind target i) cached, .. } ← (objGet id).relax.lift (by decide) |
    PyM.failure "a str iterator that is not a sequence iterator"
  let ps ← match target with
    | .str ps => pure ps
    | .obj tid => match ← (objGet tid).relax.lift (by decide) with
      | some { payload := .str ps, .. } => pure ps
      | _ => PyM.failure "a str iterator over a value that is not a str"
    | _ => PyM.failure "a str iterator over a value that is not a str"
  let pos : String.Pos.Raw := if ps.ascii then ⟨i⟩ else match cached with
    | some (j, b) => if j == i then ⟨b⟩ else strBytePos ps.s i
    | none => strBytePos ps.s i
  if String.Pos.Raw.atEnd ps.s pos then
    iterSet it (.done kind)
    return none
  let c := String.Pos.Raw.get ps.s pos
  let next := if ps.ascii then none else some (i + 1, (String.Pos.Raw.next ps.s pos).byteIdx)
  modifyPayload id (fun
    | .iter _ _ => .iter (.seq kind target (i + 1)) next
    | q => q) (by keeps_closures)
  return some (Value.ofString (String.singleton c))

/-- Set the `__name__` of the function `f`. -/
def funcSetName (f : Value) (name : String) : PyM σ .writes true Unit :=
  match f with
  | .obj id => modifyPayload id (fun
    | .func fo => .func { fo with name }
    | p => p) (by keeps_closures)
  | _ => PyM.failure "a function that is not an object"

/-- The `__dict__` of the object `v`, if it has one. -/
def objDict (v : Value) : PyM σ .reads true (Option Value) :=
  match v with
  | .obj id =>
    ⟨fun _ _ _ k _ => do
      let st ← getThe (ObjStore σ)
      k (((st.get? id).bind (·.dict)).map Value.obj), by
      intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
      exact ContOK.getThe (fun _ => hk _)
        (fun h => absurd h (Level.ne_pure_up he (by decide))),
      by intro _; unfold StartFree; intros; rfl⟩
  | _ => pure none

/-- Slot `i` of the object `v`, if it is set. -/
def slotGet (v : Value) (i : Nat) : PyM σ .reads true (Option Value) :=
  match v with
  | .obj id =>
    ⟨fun _ _ _ k _ => do
      let st ← getThe (ObjStore σ)
      k (((st.get? id).bind (·.slots[i]?)).bind fun x =>
        match x with | .undef _ => none | x => some x), by
      intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
      exact ContOK.getThe (fun _ => hk _)
        (fun h => absurd h (Level.ne_pure_up he (by decide))),
      by intro _; unfold StartFree; intros; rfl⟩
  | _ => pure none

/-- Change the object `id` by `f`, in place, at `writes`. -/
def modifyObj (id : ObjId) (f : Obj σ → Obj σ)
    (hf : ∀ o, ∀ l ∈ Refs.refs (σ := σ) (f o), l ∈ Refs.refs (σ := σ) o) :
    PyM σ .writes true Unit :=
  ⟨fun _ _ _ k _ => do
    modifyThe (ObjStore σ) fun st => st.update id f
    k (), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    obtain rfl := Level.writes_up he rfl
    exact ContOK.modifyThe _ hc.store (fun _ _ h => refsOK_update id f hf h)
      (fun h => absurd rfl h) (fun h => nomatch h)
      (hk _),
    by intro _; unfold StartFree; intros; rfl⟩

/-- Set slot `i` of the object `v` to `x`, or unset it when `x` is `undef`. -/
def slotPut (v : Value) (i : Nat) (x : Value) : PyM σ .writes true Unit :=
  match v with
  | .obj id => modifyObj id (fun o => { o with slots := o.slots.setIfInBounds i x }) fun _ _ h => h
  | _ => PyM.failure "a slot of a value that is not an object"

/-- The entry `name` of the `builtins` module's dict, object `0`. -/
def builtinGet (name : String) : PyM σ .reads true (Option Value) :=
  dictFind (.obj 0) (.ofString name) none fun _ =>
    PyM.gap s!"builtins lookup of '{name}': a key with a user __eq__ is not modelled yet"

/-- `v` as a number, if it is a `bool`, an `int` or a `float`. -/
def _root_.StrataPython.Dyn.Sem.Value.toNum? : Value → Option Arith.Num
  | .bool b => some (.bool b)
  | .int i => some (.int i)
  | .float f => some (.float f)
  | _ => none

/-- The number `n` as a value. -/
def _root_.StrataPython.Dyn.Sem.Arith.Num.toValue : Arith.Num → Value
  | .bool b => .bool b
  | .int i => .int i
  | .float f => .float f

/-- What `Arith` says CPython does instead of giving a result: raise a built-in exception with
CPython's message, or a case that is not modelled. -/
def raiseFailure {α : Type} : Format.Failure → PyM σ .reads true α
  | .raise cls msg => match Builtin.ofName? cls with
    | some b => raiseNew (.builtin b) #[.ofString msg] #[]
    | none => PyM.gap s!"raising the exception class {cls}, which is not built in"
  | .notModelled what => PyM.gap s!"not modelled: {what}"

/-- The value of `Arith`'s answer. -/
def ofArith : Option (Except Format.Failure Arith.Num) → PyM σ .reads true (Option Value)
  | none => pure none
  | some (.ok n) => pure (some n.toValue)
  | some (.error f) => raiseFailure f

/-- `a op b` for two numbers. -/
def numBinary (op : Arith.BinOp) (a b : Value) : PyM σ .reads true (Option Value) :=
  match a.toNum?, b.toNum? with
  | some x, some y => ofArith (Arith.binary op x y)
  | _, _ => pure none

/-- `op a` for a number. -/
def numUnary (op : Arith.UnaryOp) (a : Value) : PyM σ .reads true (Option Value) :=
  match a.toNum? with
  | some x => ofArith (Arith.unary op x)
  | none => pure none

/-- The hash of an immediate with no object inside. -/
def immHash (v : Value) : PyM σ .pure true (Option Hash) :=
  if v.deeperThan keyDepth then PyM.gap "a hash of values nested deeper than the model follows" else
  match v with
  | .obj _ | .undef _ => pure none
  | v => match v.immHash with
    | .hash h => pure (some h)
    | .needsStore => pure none
    | .unhashable => PyM.gap "the hash of an unhashable built-in constant is not modelled yet"
    | .unknown => PyM.gap "the hash of this value is not modelled yet"

/-- `hash()`'s result for the hash `h`. -/
def hashValue (h : Hash) : PyM σ .pure true Value :=
  match h with
  | .exact n => pure (.int n)
  | .symbolic src =>
    if src.storeAddrFree then pure (.symHash src) else PyM.gap "hash(x) depends on an address"

/-- Call a function object with an args tuple and a kwargs dict. -/
def callFunc (f args kwargs : Value) : PyM σ .calls true Value := do
  let d ← depthGet.lift (by decide)
  if d.py ≥ pyDepthLimit then PyM.gap s!"Python call depth over {pyDepthLimit}"
  match f with
  | .obj id => callClosure id args kwargs
  | _ => PyM.gap "a call of a value other than a function object is not modelled yet"

/-- The module table. -/
def modulesGet : PyM σ .reads true (Modules σ) :=
  ⟨fun _ _ _ k _ => do k (← getThe (Modules σ)), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    exact ContOK.getThe (fun _ => hk _) (fun h => absurd h (Level.ne_pure_up he (by decide))),
    by intro _; unfold StartFree; intros; rfl⟩

/-- The `__dict__` of the object `v`, made empty first if it has none yet: an object's own dict,
which CPython may keep as a split table (`DictTable.split`). -/
def objEnsureDict (v : Value) : PyM σ .writes true Value := do
  if let some d ← (objDict v).relax.lift (by decide) then return d
  let .obj id := v | PyM.failure "a dict for a value that is not an object"
  let d ← ((allocDictOf { DictTable.empty with inexact := true, split := true }).lift (by decide) :
    PyM σ .writes true Value)
  let .obj did := d | PyM.failure "a new dict that is not an object"
  modifyObj id (fun o => { o with dict := some did }) fun _ _ h => h
  pure d

/-- Add the module `name`, whose object is `v`, to the module table. -/
def moduleAdd (name : String) (v : Value) : PyM σ .reads true Unit := do
  let .obj id := v | PyM.failure "a module that is not an object"
  if (← modulesGet).map[name]?.isSome then PyM.failure s!"module {name} is already in the table"
  ⟨fun _ _ _ k _ => do
    modifyThe (Modules σ) fun m => m.addNew name id
    k (), by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    letI : Refs σ (Modules σ) := modulesRefs tg.value
    refine ContOK.modifyThe _ hc.modules (fun G m h l hl => ?_) (fun _ w => ?_)
      (fun hp => absurd hp (Level.ne_pure_up he (by decide))) (hk _)
    · obtain ⟨k, n, r, hr, rfl⟩ := (mem_modulesRefs tg.value _ l).mp hl
      exact h _ ((mem_modulesRefs tg.value m _).mpr ⟨k, n, r, Modules.cell?_addNew _ _ _ _ _ _ hr, rfl⟩)
    · exact ⟨Nat.le_refl _, fun _ _ _ h => h, Modules.extends_addNew _ _ _, rfl, rfl⟩,
    by intro _; unfold StartFree; intros; rfl⟩

/-- What `f` gives of the payload of the object `v`; `none` for a value that is not an object. -/
def partView {σ : Type} [Store σ] [Decode σ] {e : Level} {fr : Bool} [Level.AtLeast .reads e]
    {α : Type} (v : Value) (f : PayloadG Empty → Option α) : PyM σ e fr (Option α) :=
  match v with
  | .obj id => (fun o => o.bind fun o => f o.payload) <$> (objGet id).relax.lift Level.AtLeast.le
  | _ => pure none

end Prim

/-! ## The record at `PyM` -/

section
variable {σ : Type} [Store σ] [Decode σ]

instance {e : Level} {fr : Bool} : PyPure (PyM σ e fr) Value where
  imm i := i.toValue
  immViewAll v := (Prim.immView v).relax.lift Level.AtLeast.le
  undefName? v := pure (match v with | .undef n => some n | _ => none)
  identical a b := match a, b with
    | .bound _ _ _ .tpNew, _ | _, .bound _ _ _ .tpNew =>
      PyM.gap (modelInvariantPrefix ++ "a type's tp_new outside a class call")
    | _, _ => pure (a.identical b)
  addrHash v := (Prim.addrHash v).relax.lift Level.AtLeast.le
  gap msg := PyM.gap msg
  allocExc c a f x := (Prim.allocExc c a f x).relax.lift Level.AtLeast.le
  allocDict := Prim.allocDict.relax.lift Level.AtLeast.le
  region i args := PyM.region i args
  immHash v := (Prim.immHash v).relax.lift Level.AtLeast.le
  numCompare op a b := pure (match a.toNum?, b.toNum? with
    | some x, some y => some (Arith.compare op x y)
    | _, _ => none)
  hashValue h := (Prim.hashValue h).relax.lift Level.AtLeast.le
  allocList xs := (Prim.allocList xs).relax.lift Level.AtLeast.le
  allocSet frozen inexact := (Prim.allocSet frozen inexact).relax.lift Level.AtLeast.le
  allocObj c o := (Prim.allocObj c o).relax.lift Level.AtLeast.le

instance {e : Level} : PyNew (PyM σ e false) Value where
  dictSetNew := Prim.dictSetNew
  dictDeleteNew := Prim.dictDeleteNew
  dictPopitemNew := Prim.dictPopitemNew
  setAddNew := Prim.setAddNew
  setDiscardNew := Prim.setDiscardNew
  setPopNew := Prim.setPopNew
  setMergeNew := Prim.setMergeNew
  setSubtractNew := Prim.setSubtractNew
  setSymUpdateNew := Prim.setSymUpdateNew
  setReserveNew := Prim.setReserveNew
  setTrimNew := Prim.setTrimNew
  setClearNew := Prim.setClearNew
  setReplaceNew := Prim.setReplaceNew
  setFreezeNew := Prim.setFreezeNew
  listSetNew l i v := (Prim.listChangeNew l (.set i v)).lift Level.AtLeast.le
  listAppendNew l v := (Prim.listChangeNew l (.append v)).lift Level.AtLeast.le
  listSpliceNew l lo hi xs := (Prim.listChangeNew l (.splice lo hi xs)).lift Level.AtLeast.le
  listReserveNew l k := (Prim.listChangeNew l (.reserve k)).lift Level.AtLeast.le
  classSetMroNew c t := (Prim.classSetMroNew c t).lift Level.AtLeast.le

instance : PyNew (PyM σ .writes true) Value where
  dictSetNew := Prim.dictSet
  dictDeleteNew := Prim.dictDelete
  dictPopitemNew := Prim.dictPopitem
  setAddNew := Prim.setAdd true
  setDiscardNew := Prim.setDiscard true
  setPopNew := Prim.setPop true
  setMergeNew := Prim.setMerge true
  setSubtractNew := Prim.setSubtract true
  setSymUpdateNew := Prim.setSymUpdate true
  setReserveNew := Prim.setReserve true
  setTrimNew := Prim.setTrim true
  setClearNew := Prim.setClear true
  setReplaceNew := Prim.setReplace true
  setFreezeNew := Prim.setFreeze
  listSetNew l i v := Prim.listChange l (.set i v)
  listAppendNew l v := Prim.listChange l (.append v)
  listSpliceNew l lo hi xs := Prim.listChange l (.splice lo hi xs)
  listReserveNew l k := Prim.listChange l (.reserve k)
  classSetMroNew := Prim.classSetMro

instance {e : Level} {fr : Bool} [Level.AtLeast .reads e] : PyReads (PyM σ e fr) Value where
  classOf v := (Prim.classOf v).relax.lift Level.AtLeast.le
  handled := Prim.handledGet.relax.lift Level.AtLeast.le
  globalGet m n := (Prim.globalGet m n).relax.lift Level.AtLeast.le
  builtinGet n := (Prim.builtinGet n).relax.lift Level.AtLeast.le
  raiseNew cls args fields := (Prim.raiseNew cls args fields).relax.lift Level.AtLeast.le
  dictFind := Prim.dictFind
  numBinary op a b := (Prim.numBinary op a b).relax.lift Level.AtLeast.le
  numUnary op a := (Prim.numUnary op a).relax.lift Level.AtLeast.le
  listView l := match l with
    | .obj id => (Prim.listOf ·) <$> (Prim.objGet id).relax.lift Level.AtLeast.le
    | _ => pure none
  moduleGet n := (fun (ms : Modules σ) => (ms.map[n]?).map fun e => Value.obj e.obj) <$>
    (Prim.modulesGet.relax.lift Level.AtLeast.le)
  tupleView v := Prim.partView v fun | .tuple xs => some xs | _ => none
  strView v := Prim.partView v fun | .str s => some s | _ => none
  bytesView v := Prim.partView v fun | .bytes b => some b | _ => none
  numView v := Prim.partView v fun
    | .int i => some (.int i)
    | .float f => some (.float f)
    | _ => none
  dictEntries d := (fun t => t.live.map fun (en, v) => (en.key, v, en.hash)) <$>
    (Prim.dictTable d).relax.lift Level.AtLeast.le
  dictEntryAt d i := (Prim.dictEntryAt d i).relax.lift Level.AtLeast.le
  dictEntriesSize d := (·.entries.size) <$> (Prim.dictTable d).relax.lift Level.AtLeast.le
  dictLen d := (·.used) <$> (Prim.dictTable d).relax.lift Level.AtLeast.le
  dictFlags d := (fun t => (t.deleted, t.keysVersion)) <$> (Prim.dictTable d).relax.lift Level.AtLeast.le
  dictLayout d := (fun t => (t.inexact, t.split)) <$> (Prim.dictTable d).relax.lift Level.AtLeast.le
  dictCopy d := (do Prim.allocDictOf (← Prim.dictTable d).compact |>.lift (by decide)).relax.lift
    Level.AtLeast.le
  allocDictFrom d keep := (Prim.allocDictFrom d keep).relax.lift Level.AtLeast.le
  setFind s k h? eq := do
    let id ← Prim.setId s
    let read := (fun r => r.1) <$> (Prim.setRead (.obj id)).relax.lift Level.AtLeast.le
    return (← Prim.setLocate read (some fun n => (Prim.choose n).relax.lift Level.AtLeast.le)
      k h? eq fun x xs => (Prim.structuralKeys x xs).relax.lift Level.AtLeast.le).1.isSome
  setView s := (Prim.setViewOf s).relax.lift Level.AtLeast.le
  setHasUser s := (·.1.hasUser) <$> (Prim.setRead s).relax.lift Level.AtLeast.le
  dictHasUser d := (·.hasUser) <$> (Prim.dictTable d).relax.lift Level.AtLeast.le
  setWalkKinds s := (·.1.walkKinds) <$> (Prim.setRead s).relax.lift Level.AtLeast.le
  setExact s := (Prim.setExactOf s).relax.lift Level.AtLeast.le
  dictWalkKinds d := (·.walkKinds) <$> (Prim.dictTable d).relax.lift Level.AtLeast.le
  setLen s := (·.1.used) <$> (Prim.setRead s).relax.lift Level.AtLeast.le
  setCopy s frozen := (Prim.setCopy s frozen).relax.lift Level.AtLeast.le
  setSlotAt s i := (Prim.setSlotAt s i).relax.lift Level.AtLeast.le
  allocInstance c p d sl := (Prim.allocInstance c p d sl).relax.lift Level.AtLeast.le
  objView v := (Prim.objView v).relax.lift Level.AtLeast.le
  objDict v := (Prim.objDict v).relax.lift Level.AtLeast.le
  slotGet v i := (Prim.slotGet v i).relax.lift Level.AtLeast.le
  moduleAdd n v := (Prim.moduleAdd n v).relax.lift Level.AtLeast.le
  depthC := (·.c) <$> Prim.depthGet.relax.lift Level.AtLeast.le
  withDepth n body := Prim.withDepth (Level.ne_pure_up (e := .reads) Level.AtLeast.le (by decide)) n body
  withPyDepth n body :=
    Prim.withPyDepth (Level.ne_pure_up (e := .reads) Level.AtLeast.le (by decide)) n body
  reprCheck v := (Prim.reprCheck (Prim.reprKeyOf v)).relax.lift Level.AtLeast.le
  withRepr v body := Prim.withRepr (Level.ne_pure_up (e := .reads) Level.AtLeast.le (by decide))
    (Prim.reprKeyOf v) body

/-- Which body a built-in callable runs: a built-in function's, a built-in type's method's, or a
native function's, by its key. -/
inductive ImplKey where
  | function (b : Builtin)
  | method (t : Builtin) (name : String)
  | native (key : String)

/-- The body of `k` in `impls`. -/
def Impls.find (impls : Impls) : ImplKey → Option BuiltinImpl
  | .function b => impls.function b
  | .method t name => impls.method t name
  | .native key => impls.native key

/-- The body that the built-in callable `f` runs on `args`, with its `self`: a built-in
function's own, a bound method's object, an unbound method's first argument, or a native
function.  A type's `tp_new` (`DescrKind.tpNew`) runs the body of `tp_new` (`Impls.withNewCheck`). -/
def resolveBuiltin (f args : Value) : PyM σ .reads true (Option (ImplKey × Value × Value)) := do
  match f with
  | .builtin b => pure (some (.function b, f, args))
  -- A type's `tp_new` as a class call runs it is its `__new__`'s body, under the key `tp_new`.
  | .bound self t name k => pure (some (.method t (if k == .tpNew then "tp_new" else name), self, args))
  -- A static method takes no `self`: it runs on its arguments as they are.
  | .descr t name .staticMethod => pure (some (.method t name, .none, args))
  | .descr t name _ => match args with
    | .tuple xs => match xs[0]? with
      | some self =>
        if (← Prim.classOf self) == .builtin t then
          pure (some (.method t name, self, .tuple (xs.extract 1 xs.size)))
        else PyM.gap s!"a call of the descriptor {t.info.name}.{name} on another type is not modelled yet"
      | none => PyM.gap s!"a call of the descriptor {t.info.name}.{name} without an argument is not modelled yet"
    | _ => PyM.failure "an args value that is not a tuple"
  | .obj _ => match ← Prim.objView f with
    | some (.native nf) => pure (some (.native nf.key, f, args))
    | _ => pure none
  | _ => pure none

/-- The record at `PyM σ .writes fr`, with `cb` as its calls of built-ins. -/
@[reducible] def writesRecord {fr : Bool} (cb : Value → Value → Value → PyM σ .writes true Value) :
    PyWrites (PyM σ .writes fr) Value where
  callFunc f a k := (Prim.callFunc f a k).relax.lift Level.AtLeast.le
  callBuiltin f a k := (cb f a k).relax
  setHandled v := (Prim.setHandled v).relax
  write t := (Prim.writeOut t).relax
  dictSet := Prim.dictSet
  listSet l i v := (Prim.listChange l (.set i v)).relax
  listAppend l v := (Prim.listChange l (.append v)).relax
  listSplice l lo hi xs := (Prim.listChange l (.splice lo hi xs)).relax
  listReserve l k := (Prim.listChange l (.reserve k)).relax
  dictDelete := Prim.dictDelete
  dictPopitem := Prim.dictPopitem
  dictClear d := (Prim.dictClear d).relax
  setAdd := Prim.setAdd false
  setDiscard := Prim.setDiscard false
  setPop := Prim.setPop false
  setMerge := Prim.setMerge false
  setSubtract := Prim.setSubtract false
  setSymUpdate := Prim.setSymUpdate false
  setReserve := Prim.setReserve false
  setTrim := Prim.setTrim false
  setClear := Prim.setClear false
  setReplace := Prim.setReplace false
  slotSet o i v := (Prim.slotPut o i v).relax
  slotDel o i := (Prim.slotPut o i (.undef "")).relax
  classSetName c n q := (Prim.classSetName c n q).relax
  funcSetName f n := (Prim.funcSetName f n).relax
  stateSet v st := (Prim.stateSet v st).relax
  excSet e p := (Prim.excSet e p).relax
  iterSet it st := (Prim.iterSet it st).relax
  strIterNext it := (Prim.strIterNext it).relax
  funcSetAnnotations f a := (Prim.funcSetAnnotations f a).relax
  objEnsureDict v := (Prim.objEnsureDict v).relax

/-- The record at `PyM σ .calls fr`, with `cb` as its calls of built-ins, each in a call
bracket. -/
@[reducible] def callsRecord {fr : Bool} (cb : Value → Value → Value → PyM σ .writes true Value) :
    PyCalls (PyM σ .calls fr) Value where
  callFunc f a k := (Prim.callFunc f a k).relax
  callBuiltin f a k := (Prim.bracketed "a built-in that runs user code changed the world outside its call"
    (cb f a k)).relax

/-- Whether `x` is an exact `TypeError` whose message starts with `pre`: a built-in method's error
about its arguments, which names the method by its type. -/
def isNamedTypeError (x : Value) (pre : String) : PyM σ .reads true Bool := do
  if (← Prim.classOf x) != Value.builtin .TypeError then return false
  match ← Prim.objView x with
  | some (ObjView.exc { args := .tuple #[.str msg], .. }) => pure (msg.s.startsWith pre)
  | _ => pure false

/-- **The calls of built-ins**, with the bodies `impls`: a call at fuel `n + 1` runs its body with a
record whose own calls of built-ins have fuel `n`, so that the bodies, which are generic in the
record, can call built-ins too.  Running out of fuel stops with a gap. -/
def callBuiltinWith (impls : Impls) : Nat → Value → Value → Value → PyM σ .writes true Value
  | 0, _, _, _ => PyM.gap "built-in calls nested deeper than the model follows"
  | n + 1, f, args, kwargs => do
    let some (key, self, args) ← (resolveBuiltin f args).relax.lift (by decide) |
      PyM.gap "a call of this built-in callable is not modelled yet"
    match impls.find key with
    | some impl =>
      let body := @impl (PyM σ .writes true) Value (writesRecord (callBuiltinWith impls n)) _ self
        args kwargs
      -- CPython names a bound built-in method in its argument errors by the method's type when the
      -- call is a method call (`x.m(…)`), and by the type of `self` when the bound method is called
      -- later; the IR doesn't show which, so such an error on an instance of a subtype gaps.
      let run : PyM σ .writes true Value := match f with
        -- A type's `__new__` is a static method, which CPython always names by its type.
        | .bound bself t name .method => do
          if name == "__new__" || (← (Prim.classOf bself).relax.lift (by decide)) == Value.builtin t then
            body else
            tryCatch body fun x => do
              if ← (isNamedTypeError x s!"{t.info.name}.{name}()").relax.lift (by decide) then
                PyM.gap s!"an argument error of the method {t.info.name}.{name} bound to an instance of a subtype is not modelled yet"
              throw x
        | _ => body
      -- A native of kind `function` stands for a Python function: its call is one Python frame,
      -- as a call of a function object is.
      match ← (Prim.objView f).relax.lift (by decide) with
      | some (.native nf) =>
        if nf.kind == .function then Prim.withPyDepth (by decide) 1 run else run
      | _ => run
    | none => PyM.gap (match key with
      | .function b => s!"built-in {b.info.name} is not modelled yet"
      -- A type's `tp_new` (`DescrKind.tpNew`) is its `__new__` to the program.
      -- A hook's name (`importHook`, `typeGetItemHook`, `unionArgsHook`) says what has no body.
      | .method t name =>
        if name.startsWith "<" && name.endsWith ">" then
          s!"{((name.drop 1).dropEnd 1).toString} is not modelled yet"
        else
          s!"built-in method {t.info.name}.{if name == "tp_new" then "__new__" else name} is not modelled yet"
      | .native k => s!"native function {k} has no body")

/-- How deep the calls of built-ins may nest. -/
def builtinFuel : Nat := 10000

end

end

end StrataPython.Dyn.Sem
