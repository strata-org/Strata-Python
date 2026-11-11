/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Containers

set_option autoImplicit false

/-!
# Iterators

Generic over the record of primitives, CPython 3.12's iteration:

* `getIter v`, `PyObject_GetIter`: the type's `__iter__`, its result checked; else an iterator
  over an object with `__getitem__` (CPython's `iterator` type);
* `iterStep it`, `tp_iternext`: the next item of `it`, or `none` when a built-in iterator ends;
  a user `__next__` is called, and its `StopIteration` propagates;
* `lengthHint v d`, `PyObject_LengthHint`;
* `forEachItem`, the walk that a looping operation runs in one activation: over a built-in
  iterator of a list, tuple, `str`, `bytes`, range, dict or set, or a reverse iterator, the items
  up to the length when the activation began; over a `zip` or an `enumerate`, the bound of its
  inner iterators (`walkBound`); over any other iterator, one item.

Every built-in iterator but a `zip` and an `enumerate` moves to `done` when it ends and to `failed`
after a size error, so a later step gives the same answer, as in CPython; a `zip` and an
`enumerate` call their inner iterators again at every step.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- A new built-in iterator of the type `kind` with the state `s`. -/
def newIter [PyPure m V] (kind : Builtin) (s : IterStateG V) : m V :=
  PyPure.allocObj (PyPure.imm (m := m) (.builtin kind)) (.iter s)

/-- C's `LONG_MAX` and `LONG_MIN` on a 64-bit Linux. -/
def longMax : Int := 2 ^ 63 - 1
def longMin : Int := -(2 ^ 63)

/-- `range_iter`'s choice: a `range_iterator` when the start, the stop, the step, the length and
the last value fit in a C `long`, else a `longrange_iterator`. -/
def rangeIterKind (a b c : Int) : Builtin :=
  let fits (x : Int) := longMin ≤ x ∧ x ≤ longMax
  let n := rangeLen a b c
  if !(fits a ∧ fits b ∧ fits c) || (n : Int) > longMax then .longrange_iterator
  else if n == 0 then .range_iterator
  else if c > 0 then (if b > longMax - (c - 1) then .longrange_iterator else .range_iterator)
  else if b < longMin + (-1 - c) then .longrange_iterator else .range_iterator

/-- `iter(v)` for a built-in sequence, dict or set, or an instance of a subclass of one, as the
type's own `__iter__` makes it; `none` for any other value. -/
def builtinIter? [PyCalls m V] (v : V) : m (Option V) := do
  if let some (.range a b c) ← PyPure.immView v then
    let k := rangeIterKind a b c
    return some (← newIter k (.range k a c (rangeLen a b c)))
  match ← seqOf v with
  | some (.list _ _) => return some (← newIter .list_iterator (.seq .list_iterator v 0))
  | some (.tuple _) => return some (← newIter .tuple_iterator (.seq .tuple_iterator v 0))
  | some (.str t) =>
    -- An ASCII `str` gets `str_ascii_iterator`; an instance of a subclass, `str_iterator`.
    let exact := (← PyPure.immView v).isSome
    let k := if t.ascii && exact then Builtin.str_ascii_iterator else .str_iterator
    return some (← newIter k (.seq k v 0))
  | some (.bytes _) => return some (← newIter .bytes_iterator (.seq .bytes_iterator v 0))
  | some (.range ..) => return none
  | none =>
    if ← isDictLike v then
      let (_, ver) ← PyReads.dictFlags v
      return some (← newIter .dict_keyiterator (.dict .dict_keyiterator v 0 (← PyReads.dictLen v) ver))
    if (← anySetLike? v).isSome then
      return some (← newIter .set_iterator (.set v 0 (← PyReads.setLen v) 0))
    return none

/-- Whether `x` is a `StopIteration`, or an instance of a subclass of it. -/
def isStopIterationExc [PyReads m V] (x : V) : m Bool := do
  let some mro ← mroOf (← PyReads.classOf x) | return false
  inMro (PyPure.imm (m := m) (.builtin .StopIteration)) mro

/-- Whether `x` is an `IndexError`, or an instance of a subclass of it. -/
def isIndexErrorExc [PyReads m V] (x : V) : m Bool := do
  let some mro ← mroOf (← PyReads.classOf x) | return false
  inMro (PyPure.imm (m := m) (.builtin .IndexError)) mro

/-- Raise a new `StopIteration` with no arguments, as `py.next` and a built-in `__next__` raise it
when a built-in iterator ends. -/
def raiseStop [PyReads m V] {α : Type} : m α :=
  PyReads.raiseNew (PyPure.imm (m := m) (.builtin .StopIteration)) #[] #[]

/-- **`PyObject_GetIter(v)`**: the type's `__iter__`, called, and its result checked; `__iter__ =
None` raises `TypeError`; with no `__iter__`, an object with `__getitem__` (other than a dict)
gives an `iterator` over it. -/
def getIter [PyCalls m V] (v : V) : m V := do
  let t ← PyReads.classOf v
  let notIterable : m V := do raiseBuiltin "TypeError" s!"'{← typeName v}' object is not iterable"
  match ← lookupType t "__iter__" with
  | some f =>
    if (← PyPure.immView f) matches some .none then return ← notIterable
    -- A built-in container's own `__iter__` gives its iterator without a dispatch.
    if let some (.descr b "__iter__" _) ← PyPure.immView f then
      -- Only `v`'s own type's `__iter__`: one bound from another type is `callFound`'s check.
      if !b.info.name.endsWith "iterator" && (← builtinBase? v) == some b then
        if let some it ← builtinIter? v then return it
    let r ← callFound "__iter__" f v t #[] (← PyPure.allocDict)
    if (← lookupType (← PyReads.classOf r) "__next__").isNone then
      raiseBuiltin "TypeError" s!"iter() returned non-iterator of type '{← typeName r}'"
    pure r
  | none =>
    if (← lookupType t "__getitem__").isSome && !(← isDictLike v) then
      newIter .iterator (.getItem v 0)
    else notIterable

/-- The first entry of the dict `d` at or after position `i`, with its position; `none` past the
last. -/
def dictEntryFrom [PyReads m V] (d : V) (i : Nat) : m (Option (Nat × V × V)) := do
  let n ← PyReads.dictEntriesSize d
  for j in [i:n] do
    match ← PyReads.dictEntryAt d j with
    | .entry k v _ => return some (j, k, v)
    | .hole => pure ()
    | .past => return none
  return none

/-- The first member of the set `s` at or after slot `i`, with its slot; `none` past the last
slot. -/
def setSlotFrom [PyReads m V] (s : V) : Nat → Nat → m (Option (Nat × V))
  | 0, _ => PyPure.gap "a set table larger than the model walks"
  | fuel + 1, i => do
    match ← PyReads.setSlotAt s i with
    | .entry k _ => return some (i, k)
    | .hole => setSlotFrom s fuel (i + 1)
    | .past => return none

/-- The next item of `it` by a call of the `__next__` that its class finds.  The iterator had one
when the loop got it, so a class without one lost it in use, where CPython's error depends on the
operation: a gap. -/
def classNext [PyWrites m V] (it : V) : m V := do
  let t ← PyReads.classOf it
  match ← lookupType t "__next__" with
  | some f => callFound "__next__" f it t #[] (← PyPure.allocDict)
  | none => PyPure.gap "an iterator whose class lost __next__ while it is in use is not modelled yet"

/-- **`tp_iternext` of the iterator `it`**: the next item, or `none` when a built-in iterator
ends; a user `__next__` is called, and the exception it raises, `StopIteration` included,
propagates. -/
def iterStep [PyWrites m V] (it : V) : m (Option V) := do
  match ← PyReads.objView it with
  | some (.iter st) => match st with
    | .seq kind target i =>
      let some s ← seqOf target | PyPure.modelInvariant "an iterator over a value that is no longer a sequence"
      -- A `str` steps in constant time through its own primitive.
      if s matches .str _ then return ← PyWrites.strIterNext it
      if i < s.length then
        PyWrites.iterSet it (.seq kind target (i + 1))
        return some (s.at (m := m) i)
      PyWrites.iterSet it (.done kind)
      return none
    | .range kind next step left =>
      if left == 0 then return none
      PyWrites.iterSet it (.range kind (next + step) step (left - 1))
      return some (PyPure.imm (m := m) (.int next))
    | .dict kind target i size ver =>
      if (← PyReads.dictLen target) != size then
        let msg := "dictionary changed size during iteration"
        PyWrites.iterSet it (.failed kind msg)
        raiseBuiltin "RuntimeError" msg
      if (← PyReads.dictFlags target).2 != ver then
        PyPure.gap "a dict whose keys changed at the same size during its iteration is not modelled yet"
      match ← dictEntryFrom target i with
      | some (j, k, v) =>
        PyWrites.iterSet it (.dict kind target (j + 1) size ver)
        return some (match kind with
          | .dict_valueiterator => v
          | .dict_itemiterator => PyPure.imm (m := m) (.tuple #[k, v])
          | _ => k)
      | none =>
        PyWrites.iterSet it (.done kind)
        return none
    | .set target i size seen =>
      if (← PyReads.setLen target) != size then
        let msg := "Set changed size during iteration"
        PyWrites.iterSet it (.failed .set_iterator msg)
        raiseBuiltin "RuntimeError" msg
      match ← setSlotFrom target walkFuel i with
      | some (j, k) =>
        PyWrites.iterSet it (.set target (j + 1) size (seen + 1))
        return some k
      | none =>
        PyWrites.iterSet it (.done .set_iterator)
        return none
    | .getItem target i =>
      if ← isUserObject target then
        if (← lookupType (← PyReads.classOf target) "__getitem__").isNone then
          PyPure.gap "an iteration whose object's class lost __getitem__ is not modelled yet"
      let r ← tryCatch (some <$> getItem target (PyPure.imm (m := m) (.int i))) fun x => do
        if (← isIndexErrorExc x) || (← isStopIterationExc x) then pure none else throw x
      match r with
      | some v =>
        -- `__getitem__` may have stepped or ended this iterator: `iter_iternext` increments the
        -- index it holds now, and an ended iterator stays ended.
        if let some (.iter (.getItem t j)) ← PyReads.objView it then
          PyWrites.iterSet it (.getItem t (j + 1))
        return some v
      | none =>
        PyWrites.iterSet it (.done .iterator)
        return none
    | .callable f sentinel =>
      let r ← tryCatch (some <$> callN dispatchDepth f (PyPure.imm (m := m) (.tuple #[]))
          (← PyPure.allocDict)) fun x => do
        if ← isStopIterationExc x then pure none else throw x
      match r with
      | some v =>
        -- A call that exhausted the iterator itself, re-entrantly, ends it: `calliter_iternext`
        -- drops the result without comparing it with the sentinel, so no user `__eq__` runs.
        if (← PyReads.objView it) matches some (.iter (.done _)) then return none
        if ← sameOrEq (richCompare .eq) sentinel v then
          PyWrites.iterSet it (.done .callable_iterator)
          return none
        return some v
      | none =>
        PyWrites.iterSet it (.done .callable_iterator)
        return none
    | .done _ => return none
    | .failed _ msg => raiseBuiltin "RuntimeError" msg
    -- No rule makes these states yet, and no table holds their `__next__`, so a step on one
    -- stops with a gap there.
    | .zip .. | .enumerate .. | .reversed .. | .dictReversed .. => some <$> classNext it
    | _ => PyPure.gap "the next item of this iterator is not modelled yet"
  | _ => some <$> classNext it

/-- The next item of `it` by a call of its type's `__next__`, as a rule below `writes` steps an
iterator: `none` on a `StopIteration`. -/
def nextCall [PyCalls m V] (it : V) : m (Option V) := do
  let t ← PyReads.classOf it
  let some f ← lookupType t "__next__" |
    PyPure.gap "an iterator whose class lost __next__ while it is in use is not modelled yet"
  tryCatch (some <$> callFound "__next__" f it t #[] (← PyPure.allocDict)) fun x => do
    if ← isStopIterationExc x then pure none else throw x

/-- What a walk's body does after an item: go on, or stop the walk. -/
inductive Flow (S : Type) where
  | next (s : S)
  | stop (s : S)

/-- How many iterators the bound of a walk visits, at most, in a nest of `zip`s and `enumerate`s. -/
def walkBudget : Nat := 64

/-- How many items a walk takes from the iterator `it` in one activation, and the visits left of
the budget `b`, within the depth `d`: up to the length that it has left when the activation
begins, and one more, for a built-in iterator of a sequence, a range, a dict or a set, and a
reverse iterator; an `enumerate`'s inner bound, and the least of a `zip`'s inner bounds (1 for an
empty one); one item for any other iterator, and when the depth or the budget runs out.  Every
bound is at least 1. -/
def walkBoundIn [PyCalls m V] : Nat → Nat → V → m (Nat × Nat)
  | 0, b, _ => return (1, b)
  | _, 0, _ => return (1, 0)
  | d + 1, b + 1, it => do
    match ← PyReads.objView it with
    | some (.iter (.seq _ target i)) =>
      match ← seqOf target with
      | some s => return (s.length - i + 1, b)
      | none => return (1, b)
    | some (.iter (.range _ _ _ left)) => return (left + 1, b)
    | some (.iter (.dict _ target _ _ _)) => return ((← PyReads.dictLen target) + 1, b)
    | some (.iter (.set target _ _ _)) => return ((← PyReads.setLen target) + 1, b)
    | some (.iter (.reversed _ _ i)) => return (max 1 (i + 2).toNat, b)
    | some (.iter (.dictReversed _ target _ _ _ _)) => return ((← PyReads.dictLen target) + 1, b)
    | some (.iter (.enumerate inner _)) => walkBoundIn d b inner
    | some (.iter (.zip iters _)) => do
      let mut least : Option Nat := none
      let mut b := b
      for x in iters do
        let (n, b') ← walkBoundIn d b x
        b := b'
        least := some (match least with | some l => min l n | none => n)
      return (least.getD 1, b)
    | _ => return (1, b)

/-- How many items a walk takes from the iterator `it` in one activation (`walkBoundIn`, within
the budget `walkBudget`). -/
def walkBound [PyCalls m V] (it : V) : m Nat :=
  Prod.fst <$> walkBoundIn walkBudget walkBudget it

/-- **One activation's walk of the iterator `it`**, from the state `s`: `step` gives each item
(`none` at the end), and `each` runs on it. It gives `.done` when the iterator ends or `each`
stops, and `.more` with the state to go on from otherwise. -/
def forEachItem [PyCalls m V] {S : Type} (step : V → m (Option V)) (it : V) (s : S)
    (each : V → S → m (Flow S)) : m (LoopStep S S) := do
  let n ← walkBound it
  let mut s := s
  for _ in [0:n] do
    match ← step it with
    | none => return .done s
    | some x => match ← each x s with
      | .stop s' => return .done s'
      | .next s' => s := s'
  return .more s

/-- Whether `x` is a `TypeError`, or an instance of a subclass of it. -/
def isTypeErrorExc [PyReads m V] (x : V) : m Bool := do
  let some mro ← mroOf (← PyReads.classOf x) | return false
  inMro (PyPure.imm (m := m) (.builtin .TypeError)) mro

/-- The `int` that `v` is, for `PyLong_Check`: an `int`, a `bool`, or an instance of a subclass of
`int`. -/
def intPart? [PyReads m V] (v : V) : m (Option Int) := do
  match ← PyPure.immView v with
  | some (.int i) => return some i
  | some (.bool b) => return some (if b then 1 else 0)
  | some _ => return none
  | none =>
    if ← PyPure.isUndef v then return none
    match ← PyReads.numView v with
    | some (.int i) => return some i
    | some (.bool b) => return some (if b then 1 else 0)
    | _ => return none

/-- `slot_sq_length`'s check of the result `r` of a user `__len__`: converted as
`PyNumber_Index` does, then a non-negative `Py_ssize_t`. -/
def lenResult [PyCalls m V] (r : V) : m Nat := do
  let some n ← indexValue? r |
    raiseBuiltin "TypeError" s!"'{← typeName r}' object cannot be interpreted as an integer"
  if n < 0 then raiseBuiltin "ValueError" "__len__() should return >= 0"
  if n > (Format.ssizeMax : Int) then
    raiseBuiltin "OverflowError" "cannot fit 'int' into an index-sized integer"
  return n.toNat

/-- The length of a built-in sequence, range, dict or set, or of the built-in part of an instance
of a subclass of one, as its type's `__len__` gives it; `none` for any other value. A range longer
than a `Py_ssize_t` raises CPython's `OverflowError`. -/
def builtinLen? [PyCalls m V] (v : V) : m (Option Nat) := do
  if let some (.range a b c) ← PyPure.immView v then
    let n := rangeLen a b c
    if (n : Int) > (Format.ssizeMax : Int) then
      raiseBuiltin "OverflowError" "Python int too large to convert to C ssize_t"
    return some n
  if let some s ← seqOf v then return some s.length
  if ← isDictLike v then return some (← PyReads.dictLen v)
  if (← anySetLike? v).isSome then return some (← PyReads.setLen v)
  return none

/-- **`len(v)`, CPython's `PyObject_Size`**: a user `__len__`, checked by `lenResult`; the length of
a built-in sequence, range, dict or set, or of the built-in part of an instance of a subclass of
one; else `TypeError`. -/
def pyLen [PyCalls m V] (v : V) : m Nat := do
  let t ← PyReads.classOf v
  let f? ← lookupType t "__len__"
  match f? with
  | none => raiseBuiltin "TypeError" s!"object of type '{← typeName v}' has no len()"
  | some f =>
    if let some (.descr b "__len__" _) ← PyPure.immView f then
      if (← builtinBase? v) != some b then
        return ← lenResult (← callFound "__len__" f v t #[] (← PyPure.allocDict))
      match ← builtinLen? v with
      | some n => return n
      | none => PyPure.gap s!"len() of a {← typeName v} is not modelled yet"
    if (← PyPure.immView f) matches some .none then
      raiseBuiltin "TypeError" s!"'NoneType' object is not callable"
    lenResult (← callFound "__len__" f v t #[] (← PyPure.allocDict))

/-- **`PyObject_LengthHint(v, d)`**: `len(v)` when the type has `__len__`, a `TypeError` falling
through; else the type's `__length_hint__`, where none, a `TypeError` or `NotImplemented` gives
`d`; a result that is not an `int` or that is negative raises CPython's error. -/
def lengthHint [PyCalls m V] (v : V) (d : Nat) : m Nat := do
  let t ← PyReads.classOf v
  if (← lookupType t "__len__").isSome then
    let r ← tryCatch (some <$> pyLen v) fun x => do
      if ← isTypeErrorExc x then pure none else throw x
    if let some n := r then return n
  let some hint ← lookupType t "__length_hint__" | return d
  -- `PyObject_LengthHint` binds the method first (`_PyObject_LookupSpecial`), so a `TypeError` of a
  -- descriptor's `__get__` propagates; only the call's `TypeError` means "no hint".
  let g ← descrGetN dispatchDepth hint (some v) t
  let r ← tryCatch (some <$> callN dispatchDepth g (PyPure.imm (m := m) (.tuple #[]))
      (← PyPure.allocDict)) fun x => do
    if ← isTypeErrorExc x then pure none else throw x
  let some r := r | return d
  if (← PyPure.immView r) matches some .notImplemented then return d
  let some n ← intPart? r |
    raiseBuiltin "TypeError" s!"__length_hint__ must be an integer, not {← typeName r}"
  -- `PyLong_AsSsize_t` first, then the sign.
  if n < Arith.ssizeMin ∨ n > (Format.ssizeMax : Int) then
    raiseBuiltin "OverflowError" "Python int too large to convert to C ssize_t"
  if n < 0 then raiseBuiltin "ValueError" "__length_hint__() should return >= 0"
  return n.toNat

/-- A gap for a length hint beyond `maxRepeat`: CPython reserves room for the hint before it
iterates, and may then raise `MemoryError`, which depends on the machine. -/
def hintCheck [PyPure m V] (n : Nat) : m Unit := do
  if n > maxRepeat then PyPure.gap "a length hint too large to model, where CPython may raise MemoryError"

/-- `PyObject_GetIter(v)` with the `TypeError` of a value that has neither `__iter__` nor
`__getitem__` replaced by `msg t`, as `LIST_EXTEND`, `UNPACK_EX` and `CALL_FUNCTION_EX` replace
it. -/
def getIterAs [PyCalls m V] (v : V) (msg : String → String) : m V := do
  let t ← PyReads.classOf v
  if (← lookupType t "__iter__").isNone && (← lookupType t "__getitem__").isNone then
    raiseBuiltin "TypeError" (msg (← typeName v))
  getIter v

/-- The step of a walk at `writes`: `iterStep`, with a `StopIteration` from a user `__next__` as
the end, as `PyIter_Next` takes it. -/
def iterNext [PyWrites m V] (it : V) : m (Option V) :=
  tryCatch (iterStep it) fun x => do
    if ← isStopIterationExc x then pure none else throw x

/-- Whether `v` is a built-in container of an exact built-in type, whose iteration runs no user
code: a `tuple`, `str`, `bytes` or `range`, or a list, dict, set or frozenset that is not an
instance of a subclass. -/
def exactBuiltinIterable [PyReads m V] (v : V) : m Bool := do
  match ← PyPure.immView v with
  | some (.tuple _) | some (.str _) | some (.bytes _) | some (.range ..) => return true
  | some _ => return false
  | none => return (← classIs v .list) || (← isDict v) || (← anySet? v).isSome

/-- **`l.extend(it)` for a list `l`, as CPython's `LIST_EXTEND`**, one activation of it: an exact
built-in container, whose walk runs no user code, is appended at once; any other iterable is
iterated, after its length hint, its iterator the state. -/
def listExtendStep [PyWrites m V] [PyNew m V] (l it : V) (st : Option V) :
    m (LoopStep V Unit) := do
  let iter ← match st with
    | some i => pure i
    | none =>
      let some xs ← listOf? l | PyPure.modelInvariant "listExtend: operand assumption failed"
      if ← exactBuiltinIterable it then
        listExtendWith l xs it fun _ => ""
        return .done ()
      let i ← getIterAs it fun t => s!"Value after * must be an iterable, not {t}"
      let n ← lengthHint it 8
      -- `list_extend` reserves the list's size plus the hint.
      hintCheck (xs.size + n)
      if n > 0 then PyWrites.listReserve l (xs.size + n)
      pure i
  match ← forEachItem iterNext iter iter fun x s => do
      PyWrites.listAppend l x
      pure (.next s) with
  | .done _ => return .done ()
  | .more i => return .more i

/-- **`s.update(it)` for a set `s`, as CPython's `SET_UPDATE`**, one activation of it: a set or a
frozenset, or an instance of a subclass of one, merged in without its `__iter__`; an exact dict's
keys or an exact built-in sequence added at once; any other iterable iterated, its iterator the
state. -/
def setUpdateStep [PyWrites m V] (s it : V) (st : Option V) : m (LoopStep V Unit) := do
  let iter ← match st with
    | some i => pure i
    | none =>
      if (← anySetLike? it).isSome || (← exactBuiltinIterable it) then
        setUpdate s it
        return .done ()
      getIter it
  match ← forEachItem iterNext iter iter fun x st => do
      setAddItem s x
      pure (.next st) with
  | .done _ => return .done ()
  | .more i => return .more i

/-- **`a, b, … = v` with `n` targets, as CPython's `UNPACK_SEQUENCE`**: an exact built-in
container at once; otherwise `iter(v)`, `n` items, and one more to check that the iterator has
ended, all in one activation. -/
def unpackSeqAll [PyWrites m V] (v : V) (n : Nat) : m V := do
  if ← exactBuiltinIterable v then return ← unpackSeq v n
  let it ← getIterAs v unpackMsg
  let mut xs : Array V := #[]
  for i in [0:n] do
    match ← iterNext it with
    | some x => xs := xs.push x
    | none => raiseBuiltin "ValueError" s!"not enough values to unpack (expected {n}, got {i})"
  if (← iterNext it).isSome then raiseBuiltin "ValueError" s!"too many values to unpack (expected {n})"
  pure (PyPure.imm (m := m) (.tuple xs))

/-- The state of `unpackEx` across its activations: the items before the star, the list of the
rest, and its iterator. -/
abbrev UnpackState (V : Type) := Array V × V × V

/-- **`a, *b, c = v` as CPython's `UNPACK_EX`**, one activation of it: an exact built-in
container at once; otherwise `iter(v)`, the `before` items, then the rest as `PySequence_List`
makes it (a second `iter` of the iterator, its length hint, and the items), and the `after` items
popped off the end. -/
def unpackExStep [PyWrites m V] [PyNew m V] (v : V) (before after : Nat)
    (st : Option (UnpackState V)) : m (LoopStep (UnpackState V) V) := do
  let atLeast (got : Nat) : String :=
    s!"not enough values to unpack (expected at least {before + after}, got {got})"
  let (pre, lst, it2) ← match st with
    | some x => pure x
    | none =>
      if ← exactBuiltinIterable v then return .done (← unpackEx v before after)
      let it ← getIterAs v unpackMsg
      let mut pre : Array V := #[]
      for i in [0:before] do
        match ← iterNext it with
        | some x => pre := pre.push x
        | none => raiseBuiltin "ValueError" (atLeast i)
      let it2 ← getIter it
      let n ← lengthHint it 8
      hintCheck n
      let lst ← PyPure.allocList #[]
      if n > 0 then PyNew.listReserveNew lst n
      pure (pre, lst, it2)
  match ← forEachItem iterNext it2 () fun x _ => do
      PyWrites.listAppend lst x
      pure (.next ()) with
  | .more _ => return .more (pre, lst, it2)
  | .done _ =>
    let some xs ← listOf? lst | PyPure.gap "unpackEx: the list of the rest is not a list"
    if xs.size < after then raiseBuiltin "ValueError" (atLeast (before + xs.size))
    PyWrites.listSplice lst (xs.size - after) xs.size #[]
    return .done (PyPure.imm (m := m) (.tuple (pre ++ #[lst] ++ xs.extract (xs.size - after) xs.size)))

/-- **`x in s`**, one activation of it: a built-in container, or a user `__contains__`, at once;
otherwise CPython's `_PySequence_IterSearch` over `iter(s)`, a `TypeError` from which becomes
"argument of type 'S' is not iterable", each item compared as `item == x`, after the identity
shortcut. Its state is the iterator, stepped by a call of its `__next__`. -/
def containsStep [PyCalls m V] (x s : V) (st : Option V) : m (LoopStep V Bool) := do
  let it ← match st with
    | some i => pure i
    | none =>
      -- A built-in iterator has no `__contains__`, so it is iterated as a user iterable is. An
      -- iterator is what `PyIter_Check` says, an object whose class has `__next__`: a dict view
      -- is not one.
      let isIter := (← PyReads.objView s) matches some (.iter _) &&
        (← lookupType (← PyReads.classOf s) "__next__").isSome
      if !(← isUserObject s) && !isIter then return .done (← containsCore x s)
      let t ← PyReads.classOf s
      if let some f ← lookupType t "__contains__" then
        -- `slot_sq_contains` binds first: a `None` that the binding gives makes it no container.
        let g ← descrGetN dispatchDepth f (some s) t
        if (← PyPure.immView g) matches some .none then
          raiseBuiltin "TypeError" s!"'{← typeName s}' object is not a container"
        let r ← callN dispatchDepth g (PyPure.imm (m := m) (.tuple #[x])) (← PyPure.allocDict)
        return .done (← truthy r)
      tryCatch (getIter s) fun e => do
        if ← isTypeErrorExc e then
          raiseBuiltin "TypeError" s!"argument of type '{← typeName s}' is not iterable"
        throw e
  match ← forEachItem nextCall it false fun item _ => do
      if ← sameOrEq (richCompare .eq) item x then pure (.stop true) else pure (.next false) with
  | .done found => return .done found
  | .more _ => return .more it

/-- **`x in s` inside another operation's step**, which can't suspend: `containsStep` from the
start; a walk that would need another activation stops with a gap. -/
def contains [PyCalls m V] (x s : V) : m Bool := do
  match ← containsStep x s none with
  | .done b => pure b
  | .more _ => PyPure.gap "a looping built-in was reached inside an operation"

/-- One activation of `x in s` (`x not in s` when `neg`), with its result as a `bool`. -/
def inStep [PyCalls m V] (neg : Bool) (x s : V) (st : Option V) : m (LoopStep V V) := do
  match ← containsStep x s st with
  | .done b => return .done (PyPure.imm (m := m) (.bool (b != neg)))
  | .more i => return .more i


/-- `next(iter)`, or a raised `StopIteration` when it ends. -/
def nextOrStop [PyWrites m V] (iter : V) : m V := do
  match ← iterStep iter with
  | some v => pure v
  | none => raiseStop

/-- Whether the exception `exc` is a `StopIteration`, by its class. -/
def isStopIteration [PyReads m V] (exc : V) : m Bool := do
  isSubclass (← PyReads.classOf exc) (PyPure.imm (m := m) (.builtin .StopIteration))

end

end

end StrataPython.Dyn.Sem.Proto
