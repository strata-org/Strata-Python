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
      fun N => ⟨fun _ w => Same.refl s w, (fun h => absurd h hnp), fun w => ?_⟩⟩
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

/-- Call the function object `id` with `args` and `kwargs`, one Python call deeper, and go on
with `k` of its result or `ke` of its exception: the depth is read before the call and written
back after it, so the call leaves it as it found it. -/
def callClosureT {ε : Eff} {E β : Type} [PyLang σ ε] (id : ObjId) (args kwargs : Value)
    (k : Value → Sem ε E β) (ke : Value → Sem ε E β) : Sem ε E β := do
  let st ← getThe (ObjStore σ)
  match ((st.get? id).map (·.payload) : Option (ObjPayload σ)) with
  | some (PayloadG.func f) =>
    let d ← modifyGetThe Depth fun d => (d, { d with py := d.py + 1 })
    let r ← callFn (s := funcSig (ε := ε)) f.closure (args, kwargs)
    modifyThe Depth fun _ => d
    contOf k ke r
  | _ => semanticGap s!"a call of an object that is not a function object is not modelled yet"

omit [Decode σ] in
/-- A change of the depth changes no protected state. -/
theorem same_depth (s : Start) (d : Depth) (w : World σ) :
    Same s w (HasPart.set w d : World σ) :=
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

/-- The depth of Python calls and CPython's C recursion count. -/
def depthGet : PyM σ .reads true Depth :=
  ⟨fun _ _ _ k _ => do
    let d ← getThe Depth
    k d, by
    intro rs ps S tg V hc s hs hh e' he β Q QW k ke hk hke
    exact ContOK.getThe (fun _ => hk _) (fun h => absurd h (Level.ne_pure_up he (by decide))),
    by intro _; unfold StartFree; intros; rfl⟩

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

/-- The dict table of the object `id`, which the operation made: a model invariant (`PyM.failure`)
for an older object, or one that is not a dict. -/
def ownDict (id : ObjId) : PyM σ .pure false DictTable :=
  ⟨fun _ s _ k _ => if s.storeSize ≤ id then do
      let st ← getThe (ObjStore σ)
      match ((st.get? id).map (·.payload) : Option (ObjPayload σ)) with
      | some (.dict t) => k t
      | _ => modelInvariant s!"object {id} is not a dict"
    else modelInvariant "a write to an object older than the operation", by
    intro rs ps S tg V hc s hs hh e' _ β Q QW k ke hk hke
    show ContOK V s e' Q QW (if s.storeSize ≤ id then _ else _)
    split
    · rename_i hid
      refine ContOK.getThe (fun st => ?_) (fun _ w₁ w₂ h => ?_)
      · split
        · exact hk _
        · exact ContOK.fault _
      · rw [show (HasPart.get w₁ : ObjStore σ).get? id = (HasPart.get w₂ : ObjStore σ).get? id
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
a deeper key stops with a gap, so that the key's own hash and comparison end well before that. -/
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

section
variable {e : Level} {fr : Bool}

/-- The value of the entry `k` of the dict `d`, as `dictLookup` finds it, read after the lookup,
whose comparisons may change it. -/
def dictFind [Level.AtLeast .reads e] (d k : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) : PyM σ e fr (Option Value) := do
  let .obj id := d | PyM.failure "a dict lookup in a value that is not an object"
  let read : PyM σ e fr DictTable := (dictOf id).relax.lift Level.AtLeast.le
  let t ← read
  let (kc, h) ← (probeOf k h?).relax.lift Level.AtLeast.le
  let ops : LookupOps (PyM σ e fr) :=
    ⟨PyM.gap, some (fun n => (choose n).relax.lift Level.AtLeast.le), eq,
      (·.keysVersion) <$> read⟩
  match ← dictLookup ops t k kc h with
  | some i => pure (some ((← read).value i))
  | none => pure none

/-- Set the entry `k` of the dict that `read` gives to `v`, with `modify`: replace the value of the
key that `dictLookup` finds, or add the key.  The change applies to the table as it is after the
lookup, whose comparisons may change the values. -/
def dictSetWith (read : PyM σ e fr DictTable) (modify : (DictTable → DictTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (k v : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) : PyM σ e fr Unit := do
  let (kc, h) ← (probeOf k h?).relax.lift Level.AtLeast.le
  let ops : LookupOps (PyM σ e fr) := ⟨PyM.gap, choose?, eq, (·.keysVersion) <$> read⟩
  match ← dictLookup ops (← read) k kc h with
  | some i => modify (·.setValue i v)
  | none => modify (·.insertNew ⟨h, k, kc⟩ v)

/-- `dictSetWith` on a dict that the operation made; where a choice would be needed at `pure`,
a gap. -/
def dictSetNew (d k v : Value) (h? : Option Hash) (eq : Value → PyM σ e false Bool) :
    PyM σ e false Unit := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  dictSetWith ((ownDict id).lift Level.AtLeast.le) (fun f => (modifyOwnPayload id (PayloadG.modDict f) (keepsClosures_modDict _)).lift Level.AtLeast.le)
    (if h : Level.reads.le e then some fun n => (choose n).relax.lift h else none) k v h? eq

end

/-- `dictSetWith` on any dict. -/
def dictSet {fr : Bool} (d k v : Value) (h? : Option Hash) (eq : Value → PyM σ .writes fr Bool) :
    PyM σ .writes fr Unit := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  dictSetWith ((dictOf id).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modDict f) (keepsClosures_modDict _)).relax)
    (some fun n => (choose n).relax.lift (by decide)) k v h? eq

/-- The entry `name` of the `builtins` module's dict, object `0`. -/
def builtinGet (name : String) : PyM σ .reads true (Option Value) :=
  dictFind (.obj 0) (.ofString name) none fun _ =>
    PyM.gap s!"builtins lookup of '{name}': a key with a user __eq__ is not modelled yet"

/-- The limit of the depth of Python calls, below CPython's 1000. -/
def pyDepthLimit : Nat := 900

/-- Call a function object with an args tuple and a kwargs dict. -/
def callFunc (f args kwargs : Value) : PyM σ .calls true Value := do
  let d ← depthGet.lift (by decide)
  if d.py ≥ pyDepthLimit then PyM.gap s!"Python call depth over {pyDepthLimit}"
  match f with
  | .obj id => callClosure id args kwargs
  | _ => PyM.gap "a call of a value other than a function object is not modelled yet"

end Prim

/-! ## The record at `PyM` -/

section
variable {σ : Type} [Store σ] [Decode σ]

instance {e : Level} {fr : Bool} : PyPure (PyM σ e fr) Value where
  imm i := i.toValue
  immView v := (Prim.immView v).relax.lift Level.AtLeast.le
  isUndef v := pure (match v with | .undef _ => true | _ => false)
  identical a b := pure (a.identical b)
  addrHash v := (Prim.addrHash v).relax.lift Level.AtLeast.le
  gap msg := PyM.gap msg
  allocExc c a f x := (Prim.allocExc c a f x).relax.lift Level.AtLeast.le
  allocDict := Prim.allocDict.relax.lift Level.AtLeast.le
  region i args := PyM.region i args

instance {e : Level} : PyNew (PyM σ e false) Value where
  dictSetNew := Prim.dictSetNew

instance : PyNew (PyM σ .writes true) Value where
  dictSetNew := Prim.dictSet

instance {e : Level} {fr : Bool} [Level.AtLeast .reads e] : PyReads (PyM σ e fr) Value where
  classOf v := (Prim.classOf v).relax.lift Level.AtLeast.le
  handled := Prim.handledGet.relax.lift Level.AtLeast.le
  globalGet m n := (Prim.globalGet m n).relax.lift Level.AtLeast.le
  builtinGet n := (Prim.builtinGet n).relax.lift Level.AtLeast.le
  raiseNew cls args fields := (Prim.raiseNew cls args fields).relax.lift Level.AtLeast.le
  dictFind := Prim.dictFind

instance {e : Level} {fr : Bool} [Level.AtLeast .reads e] [Level.AtLeast .calls e] :
    PyCalls (PyM σ e fr) Value where
  callFunc f a k := (Prim.callFunc f a k).relax.lift Level.AtLeast.le

instance {fr : Bool} : PyWrites (PyM σ .writes fr) Value where
  setHandled v := (Prim.setHandled v).relax
  write t := (Prim.writeOut t).relax
  dictSet := Prim.dictSet

end

end

end StrataPython.Dyn.Sem
