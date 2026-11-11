/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.StrMethods

set_option autoImplicit false

/-!
# The methods of `list`, `tuple` and `range`, but `list.sort`

Generic over the record, CPython 3.12's `list` methods (`Objects/listobject.c`), and `count` and
`index` of `tuple` (`Objects/tupleobject.c`) and `range` (`Objects/rangeobject.c`). A list changes
in place through the list primitives.

`list.index`, `list.count` and `list.remove` compare the items with `==` from an index while it is
below the list's current length, as CPython's loop `i < Py_SIZE(self)` does, and a user `__eq__`
may grow the list. So they are step machines (`Machines`): one activation compares at most as
many items as the list had when it began, and one more, then suspends with the index.
`list.extend` walks an iterator as `list.__init__` does (`Collections`). A tuple can't change,
and a range compares with `==` only for a value that is not an exact `int` or a `bool`, so their
searches are loops over the items.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The items of `self`, which the descriptor check has made a list. -/
def selfItems [PyReads m V] (self : V) : m (Array V) := do
  let some xs ← listOf? self | PyPure.modelInvariant "a method of list on a value that is not a list"
  return xs

/-- A bound of `index` (`_PyEval_SliceIndexNotNone`): an index, `None` refused. -/
def indexBound [PyCalls m V] (v : V) : m Int := do
  let some i ← indexValue? v |
    raiseBuiltin "TypeError" "slice indices must be integers or have an __index__ method"
  return i

/-- CPython's adjustment of a bound of `index` to a sequence of length `n`: a negative one counts
from the end, and stops at zero. -/
def adjustBound (i : Int) (n : Nat) : Int := if i < 0 then max (i + n) 0 else i

/-- The bounds of `index(value, start=0, stop=sys.maxsize)`, converted in order. -/
def indexBounds [PyCalls m V] (ps : Array (Option V)) : m (Int × Int) := do
  let start ← match arg (m := m) ps 1 with | some v => indexBound v | none => pure 0
  let stop ← match arg (m := m) ps 2 with
    | some v => indexBound v
    | none => pure (Format.ssizeMax : Int)
  return (start, stop)

/-- `x == value` as CPython's searches compare (`PyObject_RichCompareBool`): `is` first. -/
def searchEq [PyCalls m V] (x value : V) : m Bool := sameOrEq (richCompare .eq) x value

/-! ## `list` -/

/-- **`list.append(object)`**. -/
def listAppendMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .list self Signatures.list_append args kwargs
  PyWrites.listAppend self (← req "append" ps 0)
  return PyPure.imm (m := m) .none

/-- **`list.clear()`**. -/
def listClearMethod [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| bound .list self Signatures.list_clear args kwargs
  PyWrites.listSplice self 0 (← selfItems self).size #[]
  return PyPure.imm (m := m) .none

/-- **`list.copy()`**: a new exact list of the items. -/
def listCopyMethod [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| bound .list self Signatures.list_copy args kwargs
  PyPure.allocList (← selfItems self)

/-- **`list.reverse()`**. -/
def listReverseMethod [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| bound .list self Signatures.list_reverse args kwargs
  let xs ← selfItems self
  PyWrites.listSplice self 0 xs.size xs.reverse
  return PyPure.imm (m := m) .none

/-- **`list.pop(index=-1)`**. -/
def listPopMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .list self Signatures.list_pop args kwargs
  let i ← match arg (m := m) ps 0 with | some v => ssizeArg v | none => pure (-1)
  let xs ← selfItems self
  if xs.isEmpty then raiseBuiltin "IndexError" "pop from empty list"
  let some j := position i xs.size | raiseBuiltin "IndexError" "pop index out of range"
  let some x := xs[j]? | PyPure.modelInvariant "list.pop: an item"
  PyWrites.listSplice self j (j + 1) #[]
  return x

/-- **`list.insert(index, object)`**: the index clamped to the list. -/
def listInsertMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .list self Signatures.list_insert args kwargs
  let i ← ssizeArg (← req "insert" ps 0)
  let x ← req "insert" ps 1
  let n := (← selfItems self).size
  let j : Nat := (if i < 0 then max (i + n) 0 else min i n).toNat
  PyWrites.listSplice self j j #[x]
  return PyPure.imm (m := m) .none

/-- What a list search does with a match. -/
inductive ListSearch where
  | index
  | count
  | remove
  deriving DecidableEq, Repr, Inhabited

/-- The method name of a list search. -/
def ListSearch.name : ListSearch → String
  | .index => "index"
  | .count => "count"
  | .remove => "remove"

/-- The state of a list search: the next index `i`, the bound `stop`, and the matches so far. -/
structure ListScan (V : Type) where
  kind : ListSearch
  self : V
  value : V
  i : Nat
  stop : Int
  found : Nat

/-- The result of a search that reached the end without a decisive match. -/
def scanEnd [PyWrites m V] (s : ListScan V) : m V := do
  match s.kind with
  | .count => return intValue (m := m) s.found
  | .index => raiseBuiltin "ValueError" s!"{← reprTextOf s.value} is not in list"
  | .remove => raiseBuiltin "ValueError" "list.remove(x): x not in list"

/-- One activation of a list search: at most the list's length at its start, and one more,
comparisons, each while the index is below the list's current length and `stop`. -/
def scanStep [PyWrites m V] (s : ListScan V) : m (LoopStep (ListScan V) V) := do
  let n0 := (← selfItems s.self).size
  let mut s := s
  for _ in [0:n0 + 1] do
    let xs ← selfItems s.self
    if (s.i : Int) ≥ s.stop || s.i ≥ xs.size then return .done (← scanEnd s)
    let some x := xs[s.i]? | PyPure.modelInvariant "a list search: an item"
    if ← searchEq x s.value then
      match s.kind with
      | .index => return .done (intValue (m := m) s.i)
      | .remove =>
        -- CPython removes the item at the index, even if `__eq__` moved the items, and nothing
        -- if `__eq__` shrank the list below it (`list_ass_slice` clamps the slice).
        if s.i < (← selfItems s.self).size then PyWrites.listSplice s.self s.i (s.i + 1) #[]
        return .done (PyPure.imm (m := m) .none)
      | .count => s := { s with found := s.found + 1 }
    s := { s with i := s.i + 1 }
  return .more s

/-- The first state of `list.index`, `list.count` or `list.remove` from its arguments. -/
def scanFirst [PyWrites m V] (kind : ListSearch) (self args kwargs : V) : m (ListScan V) := do
  match kind with
  | .index =>
    let ps ← bound .list self Signatures.list_index args kwargs
    let value ← req "index" ps 0
    let (start, stop) ← indexBounds ps
    let n := (← selfItems self).size
    return { kind, self, value, i := (adjustBound start n).toNat, stop := adjustBound stop n,
             found := 0 }
  | .count | .remove =>
    let sig := if kind == .count then Signatures.list_count else Signatures.list_remove
    let ps ← bound .list self sig args kwargs
    return { kind, self, value := ← req kind.name ps 0, i := 0, stop := Format.ssizeMax,
             found := 0 }

/-- **A list search inside another operation's step**: one activation, which must end. -/
def scanBody [PyWrites m V] (kind : ListSearch) (self args kwargs : V) : m V := do
  match ← scanStep (← scanFirst kind self args kwargs) with
  | .done v => return v
  | .more _ => midStepGap

/-- The first step of `self.extend(iterable)`: the iterator left to walk, if any. -/
def listExtendStart [PyWrites m V] (self args kwargs : V) : m (Option V) := do
  let ps ← bound .list self Signatures.list_extend args kwargs
  listExtendFirst self (← req "extend" ps 0)

/-- **`list.extend(iterable)` inside another operation's step**: one walk, which must end. -/
def listExtendBody [PyWrites m V] (self args kwargs : V) : m V := do
  match ← listExtendStart self args kwargs with
  | none => return PyPure.imm (m := m) .none
  | some it =>
    match ← listStep self it with
    | .done _ => return PyPure.imm (m := m) .none
    | .more _ => midStepGap

/-! ## `tuple` and `range` -/

/-- The items of `self`, which the descriptor check has made a tuple. -/
def selfTuple [PyReads m V] (self : V) : m (Array V) := do
  match ← PyPure.immView self with
  | some (.tuple xs) => return xs
  | _ =>
    let some xs ← PyReads.tupleView self |
      PyPure.modelInvariant "a method of tuple on a value that is not a tuple"
    return xs

/-- **`tuple.count(value)`**. -/
def tupleCountMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .tuple self Signatures.tuple_count args kwargs
  let value ← req "count" ps 0
  let mut n := 0
  for x in ← selfTuple self do
    pauseStep
    if ← searchEq x value then n := n + 1
  return intValue (m := m) n

/-- **`tuple.index(value, start=0, stop=sys.maxsize)`**. -/
def tupleIndexMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .tuple self Signatures.tuple_index args kwargs
  let value ← req "index" ps 0
  let (start, stop) ← indexBounds ps
  let xs ← selfTuple self
  let lo := (adjustBound start xs.size).toNat
  let hi := (min (adjustBound stop xs.size) xs.size).toNat
  for i in [lo:hi] do
    pauseStep
    if let some x := xs[i]? then
      if ← searchEq x value then return intValue (m := m) i
  raiseBuiltin "ValueError" "tuple.index(x): x not in tuple"

/-- The start, stop and step of `self`, a range. -/
def selfRange [PyReads m V] (self : V) : m (Int × Int × Int) := do
  let some (.range a b c) ← PyPure.immView self |
    PyPure.modelInvariant "a method of range on a value that is not a range"
  return (a, b, c)

/-- The position of the integer `x` in the range `a, b, c`, if it is one of its items. -/
def rangePos (a b c x : Int) : Option Nat :=
  let n := rangeLen a b c
  if c == 0 then none
  else if (x - a) % c != 0 then none
  else
    let k := (x - a) / c
    if 0 ≤ k ∧ k < n then some k.toNat else none

/-- An exact `int`, or a `bool` as an integer: the values that a range compares by arithmetic. -/
def rangeInt? [PyReads m V] (v : V) : m (Option Int) := do
  match ← PyPure.immView v with
  | some (.int i) => return some i
  | some (.bool b) => return some (if b then 1 else 0)
  | _ => return none

/-- **`range.count(value)`** and **`range.index(value)`**: arithmetic for an exact `int` or a
`bool`; otherwise a search with `==` over the items. -/
def rangeSearchMethod [PyWrites m V] (isIndex : Bool) (self args kwargs : V) : m V := do
  let sig := if isIndex then Signatures.range_index else Signatures.range_count
  let ps ← bound .range self sig args kwargs
  let value ← req sig.name ps 0
  let (a, b, c) ← selfRange self
  if let some x ← rangeInt? value then
    match rangePos a b c x, isIndex with
    | some k, true => return intValue (m := m) k
    | none, true => raiseBuiltin "ValueError" s!"{← reprTextOf value} is not in range"
    | some _, false => return intValue (m := m) 1
    | none, false => return intValue (m := m) 0
  let mut n := 0
  for k in [0:rangeLen a b c] do
    pauseStep
    if ← searchEq (intValue (m := m) (a + c * k)) value then
      if isIndex then return intValue (m := m) k
      n := n + 1
  if isIndex then raiseBuiltin "ValueError" "sequence.index(x): x not in sequence"
  return intValue (m := m) n

/-- This file's bodies of the methods of `list`, `tuple` and `range`. -/
def sequencesMethod : Builtin → String → Option BuiltinImpl
  | .list, "append" => some fun {_} {_} [_] [_] => listAppendMethod
  | .list, "clear" => some fun {_} {_} [_] [_] => listClearMethod
  | .list, "copy" => some fun {_} {_} [_] [_] => listCopyMethod
  | .list, "reverse" => some fun {_} {_} [_] [_] => listReverseMethod
  | .list, "pop" => some fun {_} {_} [_] [_] => listPopMethod
  | .list, "insert" => some fun {_} {_} [_] [_] => listInsertMethod
  | .list, "extend" => some fun {_} {_} [_] [_] => listExtendBody
  | .list, "index" => some fun {_} {_} [_] [_] => scanBody .index
  | .list, "count" => some fun {_} {_} [_] [_] => scanBody .count
  | .list, "remove" => some fun {_} {_} [_] [_] => scanBody .remove
  | .tuple, "count" => some fun {_} {_} [_] [_] => tupleCountMethod
  | .tuple, "index" => some fun {_} {_} [_] [_] => tupleIndexMethod
  | .range, "count" => some fun {_} {_} [_] [_] => rangeSearchMethod false
  | .range, "index" => some fun {_} {_} [_] [_] => rangeSearchMethod true
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
