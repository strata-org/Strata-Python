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

/-- The position of the entry `k` in the dict that `read` gives, as `dictLookup` finds it, with
the key's class and hash. -/
def dictLocate (read : PyM σ e fr DictTable) (choose? : Option (Nat → PyM σ e fr Nat))
    (k : Value) (h? : Option Hash) (eq : Value → PyM σ e fr Bool) :
    PyM σ e fr (Option Nat × KeyClass × Hash) := do
  let t ← read
  let (kc, h) ← (probeOf k h?).relax.lift Level.AtLeast.le
  let ops : LookupOps (PyM σ e fr) := ⟨PyM.gap, choose?, eq, (·.keysVersion) <$> read⟩
  pure (← dictLookup ops t k kc h, kc, h)

/-- The value of the entry `k` of the dict `d`, as `dictLookup` finds it, read after the lookup,
whose comparisons may change it. -/
def dictFind [Level.AtLeast .reads e] (d k : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) : PyM σ e fr (Option Value) := do
  let .obj id := d | PyM.failure "a dict lookup in a value that is not an object"
  let read : PyM σ e fr DictTable := (dictOf id).relax.lift Level.AtLeast.le
  match (← dictLocate read (some fun n => (choose n).relax.lift Level.AtLeast.le) k h? eq).1 with
  | some i => pure (some ((← read).value i))
  | none => pure none

/-- Set the entry `k` of the dict that `read` gives to `v`, with `modify`: replace the value of the
key that `dictLookup` finds, or add the key.  The change applies to the table as it is after the
lookup, whose comparisons may change the values. -/
def dictSetWith (read : PyM σ e fr DictTable) (modify : (DictTable → DictTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (k v : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) : PyM σ e fr Unit := do
  match (← dictLocate read choose? k h? eq) with
  | (some i, _, _) => modify (·.setValue i v)
  | (none, kc, h) => modify (·.insertNew ⟨h, k, kc⟩ v)

/-- Delete the entry `k` of the dict that `read` gives, with `modify`, and give its value. -/
def dictDeleteWith (read : PyM σ e fr DictTable) (modify : (DictTable → DictTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (k : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) : PyM σ e fr (Option Value) := do
  match (← dictLocate read choose? k h? eq).1 with
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

end

/-- `dictDeleteWith` on a dict that the operation made. -/
def dictDeleteNew {e : Level} (d k : Value) (h? : Option Hash) (eq : Value → PyM σ e false Bool) :
    PyM σ e false (Option Value) := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  dictDeleteWith ((ownDict id).lift Level.AtLeast.le)
    (fun f => (modifyOwnPayload id (PayloadG.modDict f) (keepsClosures_modDict _)).lift Level.AtLeast.le)
    (if h : Level.reads.le e then some fun n => (choose n).relax.lift h else none) k h? eq

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

/-- `dictDeleteWith` on any dict. -/
def dictDelete {fr : Bool} (d k : Value) (h? : Option Hash) (eq : Value → PyM σ .writes fr Bool) :
    PyM σ .writes fr (Option Value) := do
  let .obj id := d | PyM.failure "a dict write to a value that is not an object"
  dictDeleteWith ((dictOf id).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modDict f) (keepsClosures_modDict _)).relax)
    (some fun n => (choose n).relax.lift (by decide)) k h? eq

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
    (k : Value) (h? : Option Hash) (eq : Value → PyM σ e fr Bool) :
    PyM σ e fr (Option Nat × KeyClass × Hash) := do
  let t ← read
  let (kc, h) ← (probeOf k h?).relax.lift Level.AtLeast.le
  let ops : LookupOps (PyM σ e fr) := ⟨PyM.gap, choose?, eq, pure 0⟩
  let unchanged : PyM σ e fr Bool := (fun t' => t'.version == t.version) <$> read
  pure (← setLookup ops unchanged t k kc h, kc, h)

/-- Add `k` to the set that `read` gives, with `modify`, unless it is there. -/
def setAddWith (read : PyM σ e fr SetTable) (modify : (SetTable → SetTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (k : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) : PyM σ e fr Unit := do
  let (found, kc, h) ← setLocate read choose? k h? eq
  if found.isSome then return
  let some s := (← read).search h | PyM.failure "a set table without an empty slot"
  modify (·.addNew s h k kc)

/-- Remove `k` from the set that `read` gives, with `modify`; whether it was there. -/
def setDiscardWith (read : PyM σ e fr SetTable) (modify : (SetTable → SetTable) → PyM σ e fr Unit)
    (choose? : Option (Nat → PyM σ e fr Nat)) (k : Value) (h? : Option Hash)
    (eq : Value → PyM σ e fr Bool) : PyM σ e fr Bool := do
  match (← setLocate read choose? k h? eq).1 with
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
  if src.hasUser || t.hasUser then
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

/-- `setDiscardWith` on a set that the operation made. -/
def setDiscardNew (s k : Value) (h? : Option Hash) (eq : Value → PyM σ e false Bool) :
    PyM σ e false Bool := do
  let id ← setId s
  let _ ← (ownSet id).lift Level.AtLeast.le
  setDiscardWith (Prod.fst <$> (ownSet id).lift Level.AtLeast.le)
    (fun f => (modifyOwnPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).lift Level.AtLeast.le) (choicesAt e) k h? eq

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

/-- `setDiscardWith` on any set; a frozenset only if `af`. -/
def setDiscard (af : Bool) (s k : Value) (h? : Option Hash) (eq : Value → PyM σ .writes fr Bool) :
    PyM σ .writes fr Bool := do
  let id ← setId s
  let _ ← (mutSet id af).relax.lift (by decide)
  setDiscardWith ((Prod.fst <$> mutSet id af).relax.lift (by decide)) (fun f => (modifyPayload id (PayloadG.modSet f) (keepsClosures_modSet _)).relax)
    (some fun n => (choose n).relax.lift (by decide)) k h? eq

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

/-- The limit of the depth of Python calls, below CPython's 1000. -/
def pyDepthLimit : Nat := 900

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
  immView v := (Prim.immView v).relax.lift Level.AtLeast.le
  isUndef v := pure (match v with | .undef _ => true | _ => false)
  identical a b := pure (a.identical b)
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
  dictCopy d := (do Prim.allocDictOf (← Prim.dictTable d).compact |>.lift (by decide)).relax.lift
    Level.AtLeast.le
  allocDictFrom d keep := (Prim.allocDictFrom d keep).relax.lift Level.AtLeast.le
  setFind s k h? eq := do
    let id ← Prim.setId s
    let read := (fun r => r.1) <$> (Prim.setRead (.obj id)).relax.lift Level.AtLeast.le
    return (← Prim.setLocate read (some fun n => (Prim.choose n).relax.lift Level.AtLeast.le)
      k h? eq).1.isSome
  setView s := (Prim.setViewOf s).relax.lift Level.AtLeast.le
  setHasUser s := (·.1.hasUser) <$> (Prim.setRead s).relax.lift Level.AtLeast.le
  dictHasUser d := (·.hasUser) <$> (Prim.dictTable d).relax.lift Level.AtLeast.le
  setLen s := (·.1.used) <$> (Prim.setRead s).relax.lift Level.AtLeast.le
  setCopy s frozen := (Prim.setCopy s frozen).relax.lift Level.AtLeast.le
  setSlotAt s i := (Prim.setSlotAt s i).relax.lift Level.AtLeast.le

instance {e : Level} {fr : Bool} [Level.AtLeast .reads e] [Level.AtLeast .calls e] :
    PyCalls (PyM σ e fr) Value where
  callFunc f a k := (Prim.callFunc f a k).relax.lift Level.AtLeast.le

instance {fr : Bool} : PyWrites (PyM σ .writes fr) Value where
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

end

end

end StrataPython.Dyn.Sem
