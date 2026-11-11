/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Sequences
public import StrataDyn.Util.Sort

set_option autoImplicit false

/-!
# `list.sort` and `sorted`

Generic over the record, CPython 3.12's `list_sort_impl` (`Objects/listobject.c`) and
`builtin_sorted` (`Python/bltinmodule.c`):
1. The list is emptied, and its resize counter read; the list looks empty while the keys are
   computed and the items sorted.
2. The keys are computed in order, one call of `key` per item; a call may suspend, so this phase
   is a step machine (`Machines`). If a call raises, the list gets its items back unsorted.
3. With `reverse`, the items are reversed before the sort and after it.
4. The key scan picks CPython's comparison: `safe_object_compare` (`a < b`), or, when every key
   has one type, `unsafe_object_compare` (that type's own `__lt__` first), and, for non-empty
   exact tuples, `unsafe_tuple_compare`, which compares the first members not equal. When every
   key is an exact `int`, `bool` or non-NaN `float`, or every key is an exact `str`, no comparison
   can raise or run user code and `<` is a strict weak order, so every stable sort gives CPython's
   result: `List.mergeSort` sorts them (`fastSort`; its proofs are in `SortProps`).
5. Otherwise `Strata.Dyn.Util.Sort` sorts them with CPython's comparisons in CPython's order.
6. The list gets the sorted items back, and what user code put into it is dropped. If its resize
   counter moved, the sort raises `ValueError: list modified during sort`, unless a comparison
   raised first.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The comparison of the keys that CPython's key scan picks. -/
inductive SortCompare where
  /-- `PyObject_RichCompareBool(a, b, Py_LT)`. -/
  | safe
  /-- The keys' type's own `__lt__` first, then `a < b` if it gives `NotImplemented`. -/
  | object
  deriving DecidableEq, Repr, Inhabited

/-- What the key scan found: the comparison of the keys, or of their first members when the
keys are non-empty exact tuples (`inTuples`). -/
structure SortPlan where
  compare : SortCompare
  inTuples : Bool
  deriving Repr, Inhabited

/-- The non-empty members of `v`, if it is an exact tuple with at least one. -/
def nonEmptyTuple? [PyPure m V] (v : V) : m (Option (Array V)) := do
  match ← PyPure.immView v with
  | some (.tuple xs) => return if xs.isEmpty then none else some xs
  | _ => return none

/-- A key that the fast path can sort: the exact value of a number that is not NaN (an
infinity, or `m * 2 ^ e`), or a `str`. Numbers come before `str`s, so that the order is total;
the fast path never sorts a number with a `str`. -/
inductive FastKey where
  | inf (neg : Bool)
  | fin (m e : Int)
  | str (s : String)

/-- The exact value of a numeric key. -/
def FastKey.exact : FastKey → Arith.Exact
  | .inf neg => .inf neg
  | .fin m e => .finite m e
  | .str _ => .nan

/-- `v` as a key of the fast path: an exact `int`, `bool` or non-NaN `float`, or an exact `str`. -/
def fastKey? [PyPure m V] (v : V) : m (Option FastKey) := do
  let ofExact : Arith.Exact → Option FastKey
    | .nan => none
    | .inf neg => some (.inf neg)
    | .finite m e => some (.fin m e)
  match ← PyPure.immView v with
  | some (.int i) => return ofExact (Arith.Num.int i).exact
  | some (.bool b) => return ofExact (Arith.Num.bool b).exact
  | some (.float f) => return ofExact (Arith.Num.float f).exact
  | some (.str s) => return some (.str s.s)
  | _ => return none

/-- `a < b` for two keys of the fast path: CPython's `<` for two numbers (`Arith.compare`) and
for two `str`s; a number is below every `str`. -/
def FastKey.lt : FastKey → FastKey → Bool
  | .str a, .str b => decide (a < b)
  | .str _, _ => false
  | _, .str _ => true
  | a, b => a.exact.compare b.exact == some .lt

/-- `a ≤ b` for two keys of the fast path, as a stable sort needs it: `b` is not below `a`. -/
def FastKey.le (a b : FastKey) : Bool := !(FastKey.lt b a)

/-- **The fast path**: the positions sorted by their keys, stably. -/
def fastSort (xs : List (Nat × FastKey)) : List (Nat × FastKey) :=
  xs.mergeSort fun a b => FastKey.le a.2 b.2

/-- The keys as keys of the fast path, if they all are, all numbers or all `str`s. -/
def fastKeys? [PyReads m V] (keys : Array V) : m (Option (Array FastKey)) := do
  let mut out := #[]
  for k in keys do
    pauseStep
    let some f ← fastKey? k | return none
    out := out.push f
  let allNum := out.all fun | .str _ => false | _ => true
  let allStr := out.all fun | .str _ => true | _ => false
  return if allNum || allStr then some out else none

/-- **CPython's key scan** over at least two keys: whether every key is a non-empty exact tuple,
and whether every key (or every first member) has the first one's type. -/
def keyScan [PyReads m V] (keys : Array V) : m SortPlan := do
  let some k0 := keys[0]? | return { compare := .safe, inTuples := false }
  let mut inTuples := (← nonEmptyTuple? k0).isSome
  let first (k : V) : m V := do
    if inTuples then
      if let some xs ← nonEmptyTuple? k then if let some x := xs[0]? then return x
    return k
  let keyType ← PyReads.classOf (← first k0)
  let mut sameType := true
  for k in keys do
    pauseStep
    if inTuples && (← nonEmptyTuple? k).isNone then
      inTuples := false
      sameType := false
      break
    let t ← PyReads.classOf (← first k)
    if (← PyPure.identical t keyType) != .yes then
      sameType := false
      if !inTuples then break
  let compare := if sameType then SortCompare.object else .safe
  -- For tuples of tuples, the first members compare as `safe_object_compare` does.
  let compare := if inTuples && (← PyPure.immView keyType) matches some (.builtin .tuple) then
      SortCompare.safe else compare
  return { compare, inTuples }

/-- `a < b` by the comparison `c`. -/
def compareLt [PyCalls m V] (c : SortCompare) (a b : V) : m Bool := do
  match c with
  | .safe => richCompare .lt a b
  | .object =>
    match ← trySlot a b "__lt__" (swallow := true) with
    | some r => if let some (.bool x) ← PyPure.immView r then pure x else truthy r
    | none => richCompare .lt a b

/-- `a < b` for two keys by the plan: for tuples, CPython's `unsafe_tuple_compare`. -/
def planLt [PyCalls m V] (p : SortPlan) (a b : V) : m Bool := do
  if !p.inTuples then return ← compareLt p.compare a b
  let some xs ← nonEmptyTuple? a | PyPure.modelInvariant "a sort key that is not a tuple"
  let some ys ← nonEmptyTuple? b | PyPure.modelInvariant "a sort key that is not a tuple"
  let n := min xs.size ys.size
  let mut i := 0
  for j in [0:n] do
    i := j
    let some x := xs[j]? | PyPure.modelInvariant "a tuple member"
    let some y := ys[j]? | PyPure.modelInvariant "a tuple member"
    if !(← searchEq x y) then break
    i := j + 1
  if i ≥ n then return decide (xs.size < ys.size)
  let some x := xs[i]? | PyPure.modelInvariant "a tuple member"
  let some y := ys[i]? | PyPure.modelInvariant "a tuple member"
  if i == 0 then compareLt p.compare x y else richCompare .lt x y

/-- The port's run with the comparisons `results`, in order, and a failure at the next one: the
array as CPython's sort leaves it when that comparison raises. The port is deterministic, so it
makes the same comparisons as the run that gave `results`. -/
def replaySort (idx : Array Nat) (results : Array Bool) : Array Nat :=
  let lt (_ _ : Nat) : StateM Nat (Except Unit Bool) := do
    let k ← get
    set (k + 1)
    match results[k]? with
    | some b => pure (.ok b)
    | none => pure (.error ())
  ((Strata.Dyn.Util.Sort.sort lt idx).run' 0).1

/-- The positions of the items, sorted by their keys as CPython sorts them, with the error of
the comparison that stopped the sort, if one did. The port runs with comparisons that may raise;
each result goes into the store list `log`, so that, if one raises, `replaySort` gives the array
as CPython leaves it. (Catching each comparison's exception instead would keep a second reference
to the port's array, which every write would then copy.) -/
def sortPositions [PyWrites m V] (keys : Array V) (idx : Array Nat) :
    m (Array Nat × Option V) := do
  let none' : V := PyPure.imm (m := m) .none
  if idx.size < 2 then return (idx, none)
  let ks := idx.map fun i => keys.getD i none'
  if let some fs ← fastKeys? ks then
    return ((fastSort (idx.zip fs).toList).toArray.map (·.1), none)
  let plan ← keyScan ks
  let log ← PyPure.allocList #[]
  let lt (i j : Nat) : m (Except Unit Bool) := do
    pauseStep
    let r ← planLt plan (keys.getD i none') (keys.getD j none')
    PyWrites.listAppend log (PyPure.imm (m := m) (.bool r))
    pure (.ok r)
  tryCatch (do
      let (out, _) ← Strata.Dyn.Util.Sort.sort lt idx
      pure (out, none))
    fun e => do
      let some xs ← listOf? log | PyPure.modelInvariant "the sort's log stopped being a list"
      let results ← xs.mapM fun x => do
        let some (.bool b) ← PyPure.immView x |
          PyPure.modelInvariant "the sort's log holds a value that is not a bool"
        pure b
      pure (replaySort idx results, some e)

/-- The state of a sort while its keys are computed: the list `self` (empty during the sort),
its items `items` and the keys so far `keys` (two store lists), the key function, `reverse`, the
list's resize counter after it was emptied, and the sort's result: `None` for `list.sort`, the
list for `sorted`. -/
structure SortState (V : Type) where
  self : V
  items : V
  keys : V
  key : Option V
  reverse : Bool
  resizes : Nat
  result : V

/-- The arguments of `list.sort(*, key=None, reverse=False)`: the key function, `None` for none,
and the truth of `reverse`. -/
def sortArgs [PyCalls m V] (self args kwargs : V) : m (Option V × Bool) := do
  let ps ← bound .list self Signatures.list_sort args kwargs
  let key ← match arg (m := m) ps 0 with
    | some k => if (← PyPure.immView k) matches some .none then pure none else pure (some k)
    | none => pure none
  let reverse ← match arg (m := m) ps 1 with | some r => truthy r | none => pure false
  return (key, reverse)

/-- The first state of `self.sort(…)`: the list emptied, its items saved. -/
def sortFirst [PyWrites m V] (self args kwargs : V) (result : Option V := none) :
    m (SortState V) := do
  let (key, reverse) ← sortArgs self args kwargs
  let xs ← selfItems self
  PyWrites.listSplice self 0 xs.size #[]
  let some (_, resizes) ← PyReads.listView self | PyPure.modelInvariant "list.sort of a non-list"
  return { self, items := ← PyPure.allocList xs, keys := ← PyPure.allocList #[], key, reverse,
           resizes, result := result.getD (PyPure.imm (m := m) .none) }

/-- The list `self` gets the items `out` back, and what user code put into it is dropped. -/
def sortRestore [PyWrites m V] (self : V) (out : Array V) : m Unit := do
  PyWrites.listSplice self 0 (← selfItems self).size out

/-- **The sort, once the keys are known**: the items sorted, put back into the list, and the
error of a comparison or of a change of the list. -/
def sortFinish [PyWrites m V] (s : SortState V) : m V := do
  let items ← (·.getD #[]) <$> listOf? s.items
  let keys ← if s.key.isSome then (·.getD #[]) <$> listOf? s.keys else pure items
  let idx := (Array.range items.size)
  let idx := if s.reverse then idx.reverse else idx
  let (sorted, err) ← sortPositions keys idx
  let sorted := if s.reverse then sorted.reverse else sorted
  let some (_, rz) ← PyReads.listView s.self | PyPure.modelInvariant "list.sort of a non-list"
  sortRestore s.self (sorted.map fun i => items.getD i (PyPure.imm (m := m) .none))
  if let some e := err then throw e
  if rz != s.resizes then raiseBuiltin "ValueError" "list modified during sort"
  return s.result

/-- The list `self` gets its items back unsorted after a key call raised `e`, which is raised
again. -/
def sortKeyFailed [PyWrites m V] {α : Type} (s : SortState V) (e : V) : m α := do
  sortRestore s.self (← (·.getD #[]) <$> listOf? s.items)
  throw e

/-- The key calls of the sort `s`, made directly, and the sort. -/
def sortAll [PyWrites m V] (s : SortState V) : m V := do
  if let some k := s.key then
    for x in ← (·.getD #[]) <$> listOf? s.items do
      let kv ← tryCatch (callN dispatchDepth k (PyPure.imm (m := m) (.tuple #[x]))
        (← PyPure.allocDict)) (sortKeyFailed s)
      PyWrites.listAppend s.keys kv
  sortFinish s

/-- **`self.sort(…)` inside another operation's step**. -/
def sortBody [PyWrites m V] (self args kwargs : V) : m V := do
  sortAll (← sortFirst self args kwargs)

/-- **`sorted(iterable, /, **kwargs)`**: the items in a new list, then its `sort(**kwargs)`;
CPython checks only the positional count first. Without a key, the sort of an inexact set of
`int`s or `str`s doesn't depend on the set's order (`orderFree`). -/
def sortedFirst [PyWrites m V] (args kwargs : V) : m (V × Option V) := do
  -- A keyword that is not a `str` fails at the call, before the items are read.
  discard <| kwPairs kwargs
  let xs ← tupleItems args
  let #[x] := xs |
    raiseBuiltin "TypeError" s!"sorted expected 1 argument, got {xs.size}"
  let noKey ← (← PyReads.dictEntries kwargs).allM fun (k, _, _) => do
    return (← str? k) == some "reverse"
  let x ← if noKey then orderFree x else pure x
  let acc ← PyPure.allocList #[]
  return (acc, ← listExtendFirst acc x)

/-- **`sorted(…)` inside another operation's step**: one walk, which must end, and the sort. -/
def sortedBody [PyWrites m V] (_self args kwargs : V) : m V := do
  let (acc, it?) ← sortedFirst args kwargs
  if let some it := it? then
    if let .more _ ← listStep acc it then return ← midStepGap
  sortAll (← sortFirst acc (PyPure.imm (m := m) (.tuple #[])) kwargs (some acc))

/-- This file's body of `list.sort`. -/
def sortingMethod : Builtin → String → Option BuiltinImpl
  | .list, "sort" => some fun {_} {_} [_] [_] => sortBody
  | _, _ => none

/-- This file's body of `sorted`. -/
def sortingFunction : Builtin → Option BuiltinImpl
  | .sorted => some fun {_} {_} [_] [_] => sortedBody
  | _ => none

end

end

end StrataPython.Dyn.Sem.Library
