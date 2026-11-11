/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.DictMethods

set_option autoImplicit false

/-!
# The methods of `set` and `frozenset`

Generic over the record, CPython 3.12's set methods (`Objects/setobject.c`). Each method takes
its arguments in order and treats each as `setobject.c` does: a set or frozenset (an instance of
a subclass included) through the set primitives and `Proto`'s set operations, an exact dict by
its keys and stored hashes, and any other iterable by walking its iterator. That walk hashes and
handles each item before it asks for the next one, and stops where CPython stops (`intersection`
once the result is as large as the set, `issuperset` at the first missing item, `isdisjoint` at
the first common one), so a user iterator sees CPython's calls. It is a step machine
(`Machines`). A new set is a plain `set` or `frozenset` (`make_new_set_basetype`). A method
builds it as a `set`, and, for a `frozenset`, moves its table into a new frozenset at the end
(`finishSet`), so the result has the table that CPython builds.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

/-- The method whose walk a `SetWalk` is. -/
inductive SetJob where
  | update
  | union
  | intersection
  | intersectionUpdate
  | difference
  | differenceUpdate
  | symDifference
  | symDifferenceUpdate
  | issubset
  | issuperset
  | isdisjoint
  deriving DecidableEq, Repr, Inhabited

/-- The state of a set method that walks an iterator: `self`; `target`, the set that the walk
writes; `so`, the set whose members the walk looks up; the iterator `it`; the arguments `rest`
after the current one; and `frozen`, whether a result is a frozenset. -/
structure SetWalk (V : Type) where
  job : SetJob
  self : V
  target : V
  so : V
  it : V
  rest : List V
  frozen : Bool

section
variable {m : Type → Type 1} {V : Type}

/-! ## Members and keys -/

/-- Whether the set `s` has the item `k` (`set_contains_key`): `k` hashed. -/
def setHas [PyCalls m V] (s k : V) : m Bool := do
  PyReads.setFind s k (some (← hash k)) (keyEq k)

/-- `set_discard_key(s, k)` with `set_remove`'s and `set_discard`'s retry: a `TypeError` while
`k` is hashed or compared, for a `k` that is a `set`, retries with a frozenset of its members.
Whether a member was removed. -/
def setDiscardRetry [PyWrites m V] (s k : V) : m Bool := do
  let r ← tryCatch (do some <$> PyWrites.setDiscard s k (some (← hash k)) (keyEq k)) fun e => do
    if (← isTypeErrorExc e) && (← anySetLike? k) == some false then pure none else throw e
  match r with
  | some found => return found
  | none =>
    let fz ← PyReads.setCopy k true
    let h := frozensetHash ((← setMembers fz).unordered.toList.map (·.2))
    PyWrites.setDiscard s fz (some h) (keyEq fz)

/-- Whether `v` is a set or frozenset, an instance of a subclass included (`PyAnySet_Check`). -/
def isAnySet [PyReads m V] (v : V) : m Bool := return (← anySetLike? v).isSome

/-- The result type of a method on `self`: a frozenset for a frozenset or an instance of a
subclass of one. -/
def frozenOf [PyReads m V] (self : V) : m Bool := return (← anySetLike? self) == some true

/-! ## The steps without a walk -/

/-- **`s.add(key)`**. -/
def setAddMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .set self Signatures.set_add args kwargs
  setAddItem self (← req "add" ps 0)
  return PyPure.imm (m := m) .none

/-- **`s.remove(key)`** (`raise` for `remove`) and `discard`. -/
def setDiscardMethod [PyWrites m V] (isRemove : Bool) (self args kwargs : V) : m V := do
  let sig := if isRemove then Signatures.set_remove else Signatures.set_discard
  let ps ← bound .set self sig args kwargs
  let k ← req sig.name ps 0
  let found ← setDiscardRetry self k
  if isRemove && !found then raiseKeyError k
  return PyPure.imm (m := m) .none

/-- **`s.pop()`**: the first member from the table's finger. -/
def setPopMethod [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| bound .set self Signatures.set_pop args kwargs
  let some x ← PyWrites.setPop self | raiseBuiltin "KeyError" "pop from an empty set"
  return x

/-- **`s.clear()`**. -/
def setClearMethod [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| bound .set self Signatures.set_clear args kwargs
  PyWrites.setClear self
  return PyPure.imm (m := m) .none

/-- **`s.copy()`**: a plain set or frozenset with the members; an exact frozenset is itself. -/
def setCopyMethod [PyWrites m V] (t : Builtin) (self args kwargs : V) : m V := do
  let sig := if t == .set then Signatures.set_copy else Signatures.frozenset_copy
  discard <| bound t self sig args kwargs
  if t == .frozenset && (← classIs self .frozenset) then return self
  PyReads.setCopy self (← frozenOf self)

/-- A new, empty set that a method builds its result in. -/
def newResult [PyReads m V] : m V := PyPure.allocSet false false

/-- The result `r`, a set that the method built: as it is, or, if `frozen`, a new frozenset with
its table (`setReplaceNew`), closed: the frozenset that CPython builds directly has that table. -/
def finishSet [PyPure m V] [PyNew m V] (frozen : Bool) (r : V) : m V := do
  if !frozen then return r
  let f ← PyPure.allocSet true false
  PyNew.setReplaceNew f r
  PyNew.setFreezeNew f
  return f

/-- The members of the exact dict `d` discarded from or added to the set `s`, by their stored
hashes (`set_symmetric_difference_update` of a dict). -/
def symUpdateDict [PyWrites m V] (w : SetWrites m V) (s d : V) : m Unit := do
  guardDictWalk d s
  for (k, _, h) in ← PyReads.dictEntries d do
    if !(← w.discard s k (some h) (keyEq k)) then w.add s k (some h) (keyEq k)

/-- `set_difference(so, other)` for a set or an exact dict `other`, built as a `set`: the members of
`so` that `other` lacks, or a copy of `so` with `other`'s members discarded when `so` is more
than four times larger. `none` for any other `other`. -/
def differenceKnown [PyWrites m V] [PyNew m V] (so other : V) : m (Option V) := do
  if ← isAnySet other then return some (← setDifference false so other)
  if !(← classIs other .dict) then return none
  let n ← PyReads.dictLen other
  if (← PyReads.setLen so) / 4 > n then
    let c ← openCopy false so
    guardDictWalk other c
    for (k, _, h) in ← PyReads.dictEntries other do
      discard <| PyNew.setDiscardNew c k (some h) (keyEq k)
    PyNew.setTrimNew c
    return some c
  if WalkKinds.mayRunUser [← PyReads.setWalkKinds so, ← PyReads.dictWalkKinds other] then
    PyPure.gap "a set difference with a dict whose comparisons may run user code is not modelled yet"
  -- The members of `so` in its table order, so the result is inexact when `so` is.
  some <$> fillFrom false (← setMembers so) fun k h => do
    return (← PyReads.dictFind other k (some h) (keyEq k)).isNone

/-! ## The walks -/

/-- Whether every member of the set `small` satisfies `p`, in `small`'s table order when `p` may
run user code (the comparisons with the members of `sets`), in any order otherwise, since the
answer doesn't depend on it then. -/
def allMembers [PyCalls m V] (small : V) (sets : List V) (p : V → Hash → m Bool) : m Bool := do
  if ← mayRunUserWalk (small :: sets) then
    return ← setWalkLive small p walkFuel 0
  for (k, h) in (← setMembers small).unordered do
    pauseStep
    if !(← p k h) then return false
  return true

/-- The writes of a walk's target: `self`'s for the in-place methods, a new set's otherwise. -/
def walkWrites [PyWrites m V] [PyNew m V] (j : SetJob) : SetWrites m V :=
  match j with
  | .update | .differenceUpdate => oldSetWrites
  | _ => newSetWrites

/-- One item of a walk: what it does with the item, and whether the walk goes on. -/
def walkItem [PyWrites m V] [PyNew m V] (st : SetWalk V) (k : V) : m (Flow Bool) := do
  match st.job with
  | .update | .union | .symDifference | .symDifferenceUpdate =>
    let w := walkWrites st.job
    w.add st.target k (some (← hash k)) (keyEq k)
    return .next true
  | .intersection | .intersectionUpdate | .issubset =>
    let h ← hash k
    if ← PyReads.setFind st.so k (some h) (keyEq k) then
      PyNew.setAddNew st.target k (some h) (keyEq k)
      if (← PyReads.setLen st.target) ≥ (← PyReads.setLen st.so) then return .stop true
    return .next true
  | .difference | .differenceUpdate =>
    -- `set_discard_key`, without the methods' retry for a `set` item.
    let w := walkWrites st.job
    discard <| w.discard st.target k (some (← hash k)) (keyEq k)
    return .next true
  | .issuperset => if ← setHas st.so k then return .next true else return .stop false
  | .isdisjoint => if ← setHas st.so k then return .stop false else return .next true

/-- What a set method gives once its walks are done. -/
def walkResult [PyWrites m V] [PyNew m V] (st : SetWalk V) : m V := do
  let none' : V := PyPure.imm (m := m) .none
  match st.job with
  | .update | .differenceUpdate => return none'
  | .union | .intersection | .difference => finishSet st.frozen st.target
  | .intersectionUpdate =>
    PyWrites.setReplace st.self st.target
    return none'
  | .symDifference =>
    setSymUpdateWith newSetWrites st.target st.self
    finishSet st.frozen st.target
  | .symDifferenceUpdate =>
    setSymUpdateWith oldSetWrites st.self st.target
    return none'
  | .issubset =>
    return PyPure.imm (m := m) (.bool ((← PyReads.setLen st.target) == (← PyReads.setLen st.self)))
  | .issuperset | .isdisjoint => return PyPure.imm (m := m) (.bool true)

/-- The step of one argument `x` of a multi-argument method, with the walk state `st` (whose
`it` is not used yet): done at once, or a walk of the iterator. -/
def argStep [PyWrites m V] [PyNew m V] (st : SetWalk V) (x : V) : m (Sum (SetWalk V) (SetWalk V)) := do
  match st.job with
  | .update | .union =>
    if st.job == .union && (← PyPure.identical st.self x) == .yes then return .inl st
    match ← setFirst (walkWrites st.job) st.target x with
    | none => return .inl st
    | some it => return .inr { st with it }
  | .intersection | .intersectionUpdate =>
    -- `set_intersection(result, x)`, `result` the set so far.
    let so := st.target
    if (← PyPure.identical so x) == .yes then
      return .inl { st with target := ← PyReads.setCopy so false }
    if ← isAnySet x then return .inl { st with target := ← setIntersection false so x }
    let it ← getIter x
    return .inr { st with so, target := ← newResult, it }
  | .differenceUpdate | .difference =>
    let w := walkWrites st.job
    if (← PyPure.identical st.target x) == .yes then
      if st.job == .differenceUpdate then PyWrites.setClear st.target
      else PyNew.setClearNew st.target
      return .inl st
    if ← isAnySet x then
      setSubtractWith w st.target x
      return .inl st
    return .inr { st with it := ← getIter x }
  | _ => PyPure.modelInvariant "a set method with one argument as a multi-argument one"

/-- One activation of a set method's walk: the walk of `it`, then the arguments `rest`, until a
new walk is needed or the method is done. -/
def setWalkStep [PyWrites m V] [PyNew m V] (st : SetWalk V) : m (LoopStep (SetWalk V) V) := do
  match ← forEachItem iterNext st.it true fun k _ => walkItem st k with
  | .more _ => return .more st
  | .done false => return .done (PyPure.imm (m := m) (.bool false))
  | .done true =>
    -- The walk of this argument is done: `set_difference_update_internal` trims the dummies.
    let mut st := st
    if st.job == .difference || st.job == .differenceUpdate then
      (walkWrites (m := m) st.job).trim st.target
    for _ in [0:st.rest.length] do
      match st.rest with
      | [] => break
      | x :: rest =>
        st := { st with rest }
        match ← argStep st x with
        | .inl st' => st := st'
        | .inr st' => return .more st'
    return .done (← walkResult st)

/-- The first step of a set method `job` on `self` with the arguments `xs`: the result, or the
walk to make. -/
def setJobFirst [PyWrites m V] [PyNew m V] (job : SetJob) (self : V) (xs : Array V) :
    m (Sum V (SetWalk V)) := do
  let frozen ← frozenOf self
  let base : SetWalk V :=
    { job, self, target := self, so := self, it := self, rest := xs.toList.drop 1, frozen }
  let runArgs (st : SetWalk V) (args : List V) : m (Sum V (SetWalk V)) := do
    let mut st := { st with rest := args }
    for _ in [0:args.length + 1] do
      match st.rest with
      | [] => return .inl (← walkResult st)
      | x :: rest =>
        st := { st with rest }
        match ← argStep st x with
        | .inl st' => st := st'
        | .inr st' => return .inr st'
    return .inl (← walkResult st)
  match job with
  | .update => runArgs base xs.toList
  | .union => runArgs { base with target := ← openCopy false self } xs.toList
  | .intersection | .intersectionUpdate =>
    if xs.isEmpty then
      let c ← PyReads.setCopy self frozen
      return .inl (← walkResult { base with target := c })
    runArgs base xs.toList
  | .difference =>
    let some x := xs[0]? | return .inl (← PyReads.setCopy self frozen)
    match ← differenceKnown self x with
    | some r => runArgs { base with target := r } (xs.toList.drop 1)
    | none =>
      -- `set_copy_and_difference`: a copy of `self`, then the walk of `x`.
      runArgs { base with target := ← openCopy false self } xs.toList
  | .differenceUpdate => runArgs base xs.toList
  | .symDifference | .symDifferenceUpdate =>
    let some x := xs[0]? | PyPure.modelInvariant "symmetric_difference without its argument"
    if job == .symDifferenceUpdate then
      if (← PyPure.identical self x) == .yes then
        PyWrites.setClear self
        return .inl (PyPure.imm (m := m) .none)
      if ← classIs x .dict then
        symUpdateDict oldSetWrites self x
        return .inl (PyPure.imm (m := m) .none)
      if ← isAnySet x then
        setSymUpdateWith oldSetWrites self x
        return .inl (PyPure.imm (m := m) .none)
    -- `make_new_set_basetype(type(self), x)`, then the update.
    let r ← newResult
    match ← setFirst newSetWrites r x with
    | none => return .inl (← walkResult { base with target := r })
    | some it => return .inr { base with target := r, it, rest := [] }
  | .issubset =>
    let some x := xs[0]? | PyPure.modelInvariant "issubset without its argument"
    if ← isAnySet x then
      if (← PyReads.setLen self) > (← PyReads.setLen x) then
        return .inl (PyPure.imm (m := m) (.bool false))
      let r ← allMembers self [x] fun k h => PyReads.setFind x k (some h) (keyEq k)
      return .inl (PyPure.imm (m := m) (.bool r))
    -- `set_intersection(self, x)`, then its size.
    if (← PyPure.identical self x) == .yes then return .inl (PyPure.imm (m := m) (.bool true))
    return .inr { base with target := ← newResult, it := ← getIter x, rest := [] }
  | .issuperset =>
    let some x := xs[0]? | PyPure.modelInvariant "issuperset without its argument"
    if ← isAnySet x then
      if (← PyReads.setLen x) > (← PyReads.setLen self) then
        return .inl (PyPure.imm (m := m) (.bool false))
      let r ← allMembers x [self] fun k h => PyReads.setFind self k (some h) (keyEq k)
      return .inl (PyPure.imm (m := m) (.bool r))
    return .inr { base with it := ← getIter x, rest := [] }
  | .isdisjoint =>
    let some x := xs[0]? | PyPure.modelInvariant "isdisjoint without its argument"
    if (← PyPure.identical self x) == .yes then
      return .inl (PyPure.imm (m := m) (.bool ((← PyReads.setLen self) == 0)))
    if (← classIs x .set) || (← classIs x .frozenset) then
      let (big, small) := if (← PyReads.setLen x) > (← PyReads.setLen self) then (x, self) else (self, x)
      let r ← allMembers small [big] fun k h => return !(← PyReads.setFind big k (some h) (keyEq k))
      return .inl (PyPure.imm (m := m) (.bool r))
    return .inr { base with it := ← getIter x, rest := [] }

/-- The job of a method name of `set` or `frozenset`, and its signature. -/
def setJobOf (t : Builtin) : String → Option (SetJob × Sum ParseTupleSig BuiltinSig)
  | "update" => some (.update, .inl Signatures.set_update)
  | "union" => some (.union, .inl (if t == .set then Signatures.set_union else Signatures.frozenset_union))
  | "intersection" =>
    some (.intersection,
      .inl (if t == .set then Signatures.set_intersection else Signatures.frozenset_intersection))
  | "intersection_update" => some (.intersectionUpdate, .inl Signatures.set_intersection_update)
  | "difference" =>
    some (.difference,
      .inl (if t == .set then Signatures.set_difference else Signatures.frozenset_difference))
  | "difference_update" => some (.differenceUpdate, .inl Signatures.set_difference_update)
  | "symmetric_difference" =>
    some (.symDifference, .inr (if t == .set then Signatures.set_symmetric_difference
      else Signatures.frozenset_symmetric_difference))
  | "symmetric_difference_update" =>
    some (.symDifferenceUpdate, .inr Signatures.set_symmetric_difference_update)
  | "issubset" =>
    some (.issubset, .inr (if t == .set then Signatures.set_issubset else Signatures.frozenset_issubset))
  | "issuperset" =>
    some (.issuperset,
      .inr (if t == .set then Signatures.set_issuperset else Signatures.frozenset_issuperset))
  | "isdisjoint" =>
    some (.isdisjoint,
      .inr (if t == .set then Signatures.set_isdisjoint else Signatures.frozenset_isdisjoint))
  | _ => none

/-- The arguments of a set method: `METH_VARARGS` ones as they are, `METH_O` ones bound. -/
def setJobArgs [PyWrites m V] (t : Builtin) (self : V) (sig : Sum ParseTupleSig BuiltinSig)
    (args kwargs : V) : m (Array V) := do
  match sig with
  | .inl s => parseTupleArgs s args kwargs
  | .inr s => return (← bound t self s args kwargs).filterMap id

/-- **A set method that may walk, inside another operation's step**: its walks must end. -/
def setJobBody [PyWrites m V] [PyNew m V] (t : Builtin) (job : SetJob)
    (sig : Sum ParseTupleSig BuiltinSig) (self args kwargs : V) : m V := do
  match ← setJobFirst job self (← setJobArgs t self sig args kwargs) with
  | .inl v => return v
  | .inr st =>
    match ← setWalkStep st with
    | .done v => return v
    | .more _ => midStepGap

/-- This file's bodies of the methods of `set` and `frozenset`. -/
def setMethodsMethod : Builtin → String → Option BuiltinImpl
  | .set, "add" => some fun {_} {_} [_] [_] => setAddMethod
  | .set, "remove" => some fun {_} {_} [_] [_] => setDiscardMethod true
  | .set, "discard" => some fun {_} {_} [_] [_] => setDiscardMethod false
  | .set, "pop" => some fun {_} {_} [_] [_] => setPopMethod
  | .set, "clear" => some fun {_} {_} [_] [_] => setClearMethod
  | .set, "copy" => some fun {_} {_} [_] [_] => setCopyMethod .set
  | .frozenset, "copy" => some fun {_} {_} [_] [_] => setCopyMethod .frozenset
  | t, n =>
    if t != .set && t != .frozenset then none else
    match setJobOf t n with
    | some (job, sig) => some fun {_} {_} [_] [_] => setJobBody t job sig
    | none => none

end

end

end StrataPython.Dyn.Sem.Library
