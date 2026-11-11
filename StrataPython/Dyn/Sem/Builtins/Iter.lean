/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Dunders

set_option autoImplicit false

/-!
# The entries of the built-in iterators

Generic over the record, the `__iter__` of the built-in containers, which makes their iterators
(`builtinIter?`), and the `__iter__` (the iterator itself), `__next__` (`iterStep`, with a new
`StopIteration` at the end) and `__length_hint__` of the iterator types of `iterTypes`; the
built-ins `len`, `iter` and `next`, and `range`'s constructor. The dict iterators'
`__length_hint__` is not filled here.
-/

namespace StrataPython.Dyn.Sem.Builtins

open Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The iterator types whose entries this file fills. -/
def iterTypes : List Builtin :=
  [.list_iterator, .tuple_iterator, .str_ascii_iterator, .str_iterator, .bytes_iterator,
    .range_iterator, .longrange_iterator, .dict_keyiterator, .dict_valueiterator,
    .dict_itemiterator, .set_iterator, .callable_iterator, .iterator]

/-- `t.__iter__(self)` of a built-in container: its iterator. -/
def containerIterBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__iter__" args kwargs
  let some it ← builtinIter? self | PyPure.gap "__iter__ of this value is not modelled yet"
  pure it

/-- An iterator's `__iter__(self)`: the iterator itself. -/
def iterSelfBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__iter__" args kwargs
  pure self

/-- An iterator's `__next__(self)`: its next item, or a new `StopIteration` at the end. -/
def iterNextBody [PyWrites m V] (self args kwargs : V) : m V := do
  noArg "__next__" args kwargs
  match ← iterStep self with
  | some v => pure v
  | none => raiseStop

/-- An iterator's `__length_hint__(self)`, as each of CPython's iterator types counts it: the
items left, or `0` once it has ended or failed; for an `iterator` over an object with
`__getitem__`, its `len()` less the index, or `NotImplemented` without `__len__`. -/
def iterLengthHintBody [PyWrites m V] (qualname : String) (self args kwargs : V) : m V := do
  let sig : BuiltinSig := { name := "__length_hint__", qualname, style := .noArgs }
  discard <| bindBuiltinArgs sig args kwargs
  let n : Int ← match ← PyReads.objView self with
    | some (.iter (.seq _ target i)) =>
      match ← seqOf target with
      | some s => pure (max 0 ((s.length : Int) - i))
      | none => pure 0
    | some (.iter (.range _ _ _ left)) => pure left
    | some (.iter (.set target _ size seen)) =>
      pure (if (← PyReads.setLen target) == size then (size : Int) - seen else 0)
    | some (.iter (.getItem target _)) =>
      if (← lookupType (← PyReads.classOf target) "__len__").isNone then
        return PyPure.imm (m := m) .notImplemented
      let n ← pyLen target
      -- `iter_len` reads the index after `__len__`, which may have stepped or ended the iterator.
      match ← PyReads.objView self with
      | some (.iter (.getItem _ j)) => pure (max 0 ((n : Int) - j))
      | _ => PyPure.gap "a __len__ that ended the iterator it measures is not modelled yet"
    | some (.iter (.done _)) | some (.iter (.failed ..)) => pure 0
    | _ => PyPure.gap s!"{qualname} of this iterator is not modelled yet"
  pure (PyPure.imm (m := m) (.int n))

/-- **`len(x)`**, `PyObject_Size`. -/
def lenFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig : BuiltinSig := { name := "len", qualname := "len", style := .methO }
  let b ← bindBuiltinArgs sig args kwargs
  let #[some x] := b.params | PyPure.modelInvariant "len: the binder's assumption failed"
  pure (PyPure.imm (m := m) (.int (← pyLen x)))

/-- **`iter(x)`** and **`iter(f, sentinel)`**: `PyObject_GetIter`, or a `callable_iterator`. -/
def iterFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig : BuiltinSig :=
    { name := "iter", qualname := "iter", style := .posOnly, posonly := 2, minpos := 1, maxpos := 2 }
  let b ← bindBuiltinArgs sig args kwargs
  match b.params with
  | #[some x, none] => getIter x
  | #[some f, some sentinel] =>
    if (← lookupType (← PyReads.classOf f) "__call__").isNone then
      raiseBuiltin "TypeError" "iter(v, w): v must be callable"
    newIter .callable_iterator (.callable f sentinel)
  | _ => PyPure.modelInvariant "iter: the binder's assumption failed"

/-- **`next(it)`** and **`next(it, default)`**: the next item; at the end, a new `StopIteration`,
or `default`, which a `StopIteration` from a user `__next__` gives too. -/
def nextFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig : BuiltinSig :=
    { name := "next", qualname := "next", style := .posOnly, posonly := 2, minpos := 1, maxpos := 2 }
  let b ← bindBuiltinArgs sig args kwargs
  let (it, dflt) ← match b.params with
    | #[some it, d] => pure (it, d)
    | _ => PyPure.modelInvariant "next: the binder's assumption failed"
  -- `PyIter_Check`: an iterator's class has `__next__`; a dict view, though an `.iter` object, is not
  -- one.
  if (← lookupType (← PyReads.classOf it) "__next__").isNone then
    raiseBuiltin "TypeError" s!"'{← typeName it}' object is not an iterator"
  match dflt with
  | none =>
    match ← iterStep it with
    | some v => pure v
    | none => raiseStop
  | some d =>
    match ← iterNext it with
    | some v => pure v
    | none => pure d

/-- An argument of `range`, as `PyNumber_Index` converts it. -/
def rangeArg [PyCalls m V] (v : V) : m Int := do
  let some i ← indexValue? v |
    raiseBuiltin "TypeError" s!"'{← typeName v}' object cannot be interpreted as an integer"
  pure i

/-- **`range.__new__(cls, ...)`**, CPython's `range_new`: `range(stop)`, `range(start, stop)` or
`range(start, stop, step)`, each argument through `PyNumber_Index`; a zero step raises
`ValueError`. -/
def rangeNew [PyWrites m V] (_self args kwargs : V) : m V := do
  if (← PyReads.dictLen kwargs) > 0 then raiseBuiltin "TypeError" "range() takes no keyword arguments"
  let xs := (← tupleItems args).extract 1 (← tupleItems args).size
  let sig : BuiltinSig :=
    { name := "range", qualname := "range", style := .posOnly, posonly := 3, minpos := 1, maxpos := 3 }
  let b ← bindBuiltinArgs sig (PyPure.imm (m := m) (.tuple xs)) kwargs
  let (a, z, c) ← match b.params with
    | #[some stop, none, none] => pure (0, ← rangeArg stop, 1)
    | #[some start, some stop, none] => pure (← rangeArg start, ← rangeArg stop, 1)
    | #[some start, some stop, some step] =>
      let a ← rangeArg start
      let z ← rangeArg stop
      let c ← rangeArg step
      if c == 0 then raiseBuiltin "ValueError" "range() arg 3 must not be zero"
      pure (a, z, c)
    | _ => PyPure.modelInvariant "range: the binder's assumption failed"
  pure (PyPure.imm (m := m) (.range a z c))

/-- **`range.__reversed__(self)`, CPython's `range_reverse`**: an iterator from the last item down;
a `range_iterator` when the start, the stop, the step, its negation, `start - step` and the length
fit in a C `long`, else a `longrange_iterator`. -/
def rangeReversedBody [PyWrites m V] (self args kwargs : V) : m V := do
  let sig : BuiltinSig := { name := "__reversed__", qualname := "range.__reversed__", style := .noArgs }
  discard <| bindBuiltinArgs sig args kwargs
  let some (.range a z c) ← PyPure.immView self | PyPure.gap "range.__reversed__ of a value that is not a range"
  let n := rangeLen a z c
  let fits (x : Int) := longMin ≤ x ∧ x ≤ longMax
  let k := if fits a ∧ fits z ∧ fits c ∧ c != longMin ∧ fits (a - c) ∧ (n : Int) ≤ longMax
    then Builtin.range_iterator else .longrange_iterator
  newIter k (.range k (a + ((n : Int) - 1) * c) (-c) n)

/-- **The body of the entry `t.name`** of a built-in iterator type or of a container's
`__iter__`, if this file fills it. -/
def iterImpl (t : Builtin) (name : String) : Option BuiltinImpl :=
  if iterTypes.contains t then
    match name with
    | "__iter__" => some fun {_} {_} [_] [_] => iterSelfBody
    | "__next__" => some fun {_} {_} [_] [_] => iterNextBody
    | "__length_hint__" =>
      if [Builtin.dict_keyiterator, .dict_valueiterator, .dict_itemiterator].contains t then none
      else some fun {_} {_} [_] [_] => iterLengthHintBody s!"{t.info.name}.__length_hint__"
    | _ => none
  else if t == .range && name == "__new__" then some fun {_} {_} [_] [_] => rangeNew
  else if t == .range && name == "__reversed__" then some fun {_} {_} [_] [_] => rangeReversedBody
  else if name == "__iter__" &&
      [Builtin.list, .tuple, .str, .bytes, .range, .dict, .«set», .«frozenset»].contains t then
    some fun {_} {_} [_] [_] => containerIterBody
  else none

end

end

end StrataPython.Dyn.Sem.Builtins
