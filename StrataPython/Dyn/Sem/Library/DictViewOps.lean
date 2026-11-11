/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.SetMethods
public import StrataPython.Dyn.Sem.Library.Iterators

set_option autoImplicit false

/-!
# The dunders of the dict views

Generic over the record, CPython 3.12's `dict_keys` and `dict_items` as sets
(`Objects/dictobject.c`): `__contains__`, `__reversed__`, `__repr__`, the rich comparisons
(`dictview_richcompare`, by sizes and `all_contained_in`), the set operations `&`, `|`, `-` and
`^` in both orders (`_PyDictView_Intersect`, `dictviews_or`, `dictviews_sub`, `dictviews_xor`,
`dictitems_xor`), which give a `set`, and `isdisjoint`; `dict_values` has `__reversed__` and
`__repr__` only; and all three have `mapping`, a read-only proxy of their dict. The operations
call these dunders as the C slots of the views' classes. They are reached inside another
operation's step, so a walk over a user iterator that doesn't end there stops with the gap of the
residual case.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The kind and the dict of `v` if it is a `dict_keys` or `dict_items` view
(`PyDictViewSet_Check`). -/
def setView? [PyReads m V] (v : V) : m (Option (Builtin × V)) := do
  if (← PyPure.immView v).isSome || (← PyPure.isUndef v) then return none
  match ← PyReads.objView v with
  | some (.iter (.view k d)) => return if k == .dict_values then none else some (k, d)
  | _ => return none

/-- `x in view` for a keys or items view of the dict `d` (`dictkeys_contains`,
`dictitems_contains`): a key looked up; for items, a pair whose key is found and whose value is
equal to the found one, `found == value`. -/
def viewHas [PyCalls m V] (k : Builtin) (d x : V) : m Bool := do
  if k == .dict_keys then return (← dictFindKey d x).isSome
  let xs? ← match ← PyPure.immView x with
    | some (.tuple xs) => pure (some xs)
    | some _ => pure none
    | none => PyReads.tupleView x
  let some #[key, value] := xs? | return false
  let some found ← dictFindKey d key | return false
  sameOrEq (richCompare .eq) found value

/-- `x in c`, a view's own test for a keys or items view, `in` otherwise. -/
def memberOfAny [PyWrites m V] (c x : V) : m Bool := do
  match ← setView? c with
  | some (k, d) => viewHas k d x
  | none => contains x c

/-- The items of a walk of `v` that must end inside the step; each one through `f`, which may
stop the walk. -/
def walkAll [PyWrites m V] (v : V) (f : V → m Bool) : m Bool := do
  let it ← getIter v
  match ← forEachItem iterNext it true fun x _ => do
      if ← f x then pure (.next true) else pure (.stop false) with
  | .done b => return b
  | .more _ => midStepGap

/-- The size of `v` as `PyObject_Size` gives it: a view's dict's; a set subclass's own `__len__`. -/
def sizeOf [PyWrites m V] (v : V) : m Nat := do
  match ← setView? v with
  | some (_, d) => PyReads.dictLen d
  | none => pyLen v

/-- **`__contains__`** of a keys or items view. -/
def viewContains [PyWrites m V] (self args kwargs : V) : m V := do
  let #[x] ← wrapperArgs "__contains__" 1 args kwargs |
    PyPure.modelInvariant "__contains__ without its operand"
  let (k, d) ← viewOf self
  return PyPure.imm (m := m) (.bool (← viewHas k d x))

/-- **`__reversed__`** of a view: a reverse iterator of its kind. -/
def viewReversed [PyWrites m V] (self args kwargs : V) : m V := do
  let (k, d) ← viewOf self
  noArgsMethod k "__reversed__" self args kwargs
  let rk := match k with
    | .dict_values => Builtin.dict_reversevalueiterator
    | .dict_items => .dict_reverseitemiterator
    | _ => .dict_reversekeyiterator
  dictRevIter rk d

/-- The items of the view of the kind `k` over `d`, as its iterator gives them. -/
def viewItems [PyReads m V] (k : Builtin) (d : V) : m (Array V) := do
  return (← PyReads.dictEntries d).map fun (key, v, _) => match k with
    | .dict_values => v
    | .dict_items => PyPure.imm (m := m) (.tuple #[key, v])
    | _ => key

/-- **`__repr__`** of a view: `dict_keys([…])`, its type name and the `repr` of the list of its
items; `...` for a view met again inside its own `repr`. -/
def viewRepr [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| wrapperArgs "__repr__" 0 args kwargs
  let (k, d) ← viewOf self
  match ← PyReads.reprCheck self with
  | .hit => return strValue (m := m) "..."
  | .unknown => PyPure.modelInvariant "the repr guard is unsure of an object"
  | .fresh => PyReads.withRepr self do
    let l ← PyPure.allocList (← viewItems k d)
    return strValue (m := m) s!"{k.info.name}({← reprTextOf l})"

/-- `all_contained_in(a, b)`: every item of `a` is in `b`. -/
def allContainedIn [PyWrites m V] (a b : V) : m Bool := walkAll a (memberOfAny b)

/-- **The rich comparison `op`** of a keys or items view with another such view or a set:
`NotImplemented` for any other operand. -/
def viewCompare [PyWrites m V] (op : Arith.CmpOp) (name : String) (self args kwargs : V) : m V := do
  let #[other] ← wrapperArgs name 1 args kwargs |
    PyPure.modelInvariant "a comparison without its operand"
  if !(← isAnySet other) && (← setView? other).isNone then
    return PyPure.imm (m := m) .notImplemented
  let a ← sizeOf self
  let b ← sizeOf other
  let r ← match op with
    | .eq => if a == b then allContainedIn self other else pure false
    | .ne => if a == b then (! ·) <$> allContainedIn self other else pure true
    | .lt => if a < b then allContainedIn self other else pure false
    | .le => if a ≤ b then allContainedIn self other else pure false
    | .gt => if a > b then allContainedIn other self else pure false
    | .ge => if a ≥ b then allContainedIn other self else pure false
  return PyPure.imm (m := m) (.bool r)

/-- A new set of the items of `v` (`dictviews_to_set`): a keys view of an exact dict through the
dict, any other value through its iterator. -/
def viewToSet [PyWrites m V] [PyNew m V] (v : V) : m V := do
  let src ← match ← setView? v with
    | some (.dict_keys, d) => if ← classIs d .dict then pure d else pure v
    | _ => pure v
  let r ← newResult
  match ← setFirst newSetWrites r src with
  | none => return r
  | some it =>
    match ← setStep newSetWrites r it with
    | .done _ => return r
    | .more _ => midStepGap

/-- A set method's job on `s` with the argument `x`, run to its end inside the step. -/
def runJob [PyWrites m V] [PyNew m V] (job : SetJob) (s x : V) : m V := do
  match ← setJobFirst job s #[x] with
  | .inl v => return v
  | .inr st =>
    match ← setWalkStep st with
    | .done v => return v
    | .more _ => midStepGap

/-- `_PyDictView_Intersect(a, b)`: a view and any iterable, in either order. -/
def viewIntersect [PyWrites m V] [PyNew m V] (a b : V) : m V := do
  let (self, other) ← if (← setView? a).isNone then pure (b, a) else pure (a, b)
  let lenSelf ← sizeOf self
  if ← classIs other .set then
    if lenSelf ≤ (← PyReads.setLen other) then return ← runJob .intersection other self
  let (self, other) ← match ← setView? other with
    | some _ => if (← sizeOf other) > lenSelf then pure (other, self) else pure (self, other)
    | none => pure (self, other)
  let some (k, d) ← setView? self | PyPure.modelInvariant "an intersection without a view"
  let r ← newResult
  discard <| walkAll other fun x => do
    if ← viewHas k d x then setAddItem r x
    pure true
  return r

/-- `dictitems_xor(a, b)` for two items views: the pairs of `b`'s dict whose key is missing from,
or has another value in, a copy of `a`'s dict, which loses the equal ones; then the pairs left in
that copy. `b`'s dict is walked live, by position. CPython's resize compacts the dict's holes, so
a change of its keys while it has a deleted entry moves the entries under the walk: a gap. -/
def itemsXor [PyWrites m V] [PyNew m V] (d1 d2 : V) : m V := do
  let tmp ← dictCopyOf d1
  let r ← newResult
  let (_, ver0) ← PyReads.dictFlags d2
  let mut i := 0
  let mut ended := false
  for _ in [0:walkFuel] do
    let (deleted, ver) ← PyReads.dictFlags d2
    if ver != ver0 && deleted then
      PyPure.gap "a dict whose keys change while it has deleted entries, during a walk, is not modelled yet"
    match ← PyReads.dictEntryAt d2 i with
    | .past =>
      ended := true
      break
    | .hole => i := i + 1
    | .entry key v2 h =>
      i := i + 1
      pauseStep
      let toDelete ← match ← PyReads.dictFind tmp key (some h) (keyEq key) with
        | none => pure false
        | some v1 => sameOrEq (richCompare .eq) v1 v2
      if toDelete then discard <| PyWrites.dictDelete tmp key (some h) (keyEq key)
      else setAddItem r (PyPure.imm (m := m) (.tuple #[key, v2]))
  unless ended do PyPure.gap "a walk of a dict that doesn't end"
  for (key, v, _) in ← PyReads.dictEntries tmp do
    setAddItem r (PyPure.imm (m := m) (.tuple #[key, v]))
  return r

/-- **A set operation of a view**, `op` with its operands `a` and `b` in the order of the C slot
(`__rand__` and friends swap them). -/
def viewSetOp [PyWrites m V] [PyNew m V] (op : Arith.BinOp) (a b : V) : m V := do
  match op with
  | .and => viewIntersect a b
  | .or =>
    let r ← viewToSet a
    discard <| runJob .update r b
    return r
  | .sub =>
    let r ← viewToSet a
    discard <| runJob .differenceUpdate r b
    return r
  | _ =>
    match ← setView? a, ← setView? b with
    | some (.dict_items, d1), some (.dict_items, d2) => itemsXor d1 d2
    | _, _ =>
      let r ← viewToSet a
      discard <| runJob .symDifferenceUpdate r b
      return r

/-- The slot wrapper of a view's set operation `op`: `rev` for the reflected one. -/
def viewSetOpBody [PyWrites m V] [PyNew m V] (op : Arith.BinOp) (rev : Bool) (name : String)
    (self args kwargs : V) : m V := do
  let #[other] ← wrapperArgs name 1 args kwargs |
    PyPure.modelInvariant "a set operation without its operand"
  if rev then viewSetOp op other self else viewSetOp op self other

/-- **`view.isdisjoint(other)`** (`dictviews_isdisjoint`): the shorter of two sized operands
walked. -/
def viewIsdisjoint [PyWrites m V] (self args kwargs : V) : m V := do
  let (k, _) ← viewOf self
  let ps ← bindBuiltinArgs
    { name := "isdisjoint", qualname := s!"{k.info.name}.isdisjoint", style := .methO } args kwargs
  let some (some other) := ps.params[0]? | PyPure.modelInvariant "isdisjoint without its operand"
  if (← PyPure.identical self other) == .yes then
    return PyPure.imm (m := m) (.bool ((← sizeOf self) == 0))
  let (a, b) ← if (← isAnySet other) || (← setView? other).isSome then
      if (← sizeOf other) > (← sizeOf self) then pure (other, self) else pure (self, other)
    else pure (self, other)
  let r ← walkAll b fun x => return !(← memberOfAny a x)
  return PyPure.imm (m := m) (.bool r)

/-- The comparison operator of a rich-comparison dunder name. -/
def cmpOfName : String → Option Arith.CmpOp
  | "__eq__" => some .eq | "__ne__" => some .ne | "__lt__" => some .lt
  | "__le__" => some .le | "__gt__" => some .gt | "__ge__" => some .ge
  | _ => none

/-- The operator of a set-operation dunder name, and whether it is the reflected one. -/
def setOpOfName : String → Option (Arith.BinOp × Bool)
  | "__and__" => some (.and, false) | "__rand__" => some (.and, true)
  | "__or__" => some (.or, false) | "__ror__" => some (.or, true)
  | "__sub__" => some (.sub, false) | "__rsub__" => some (.sub, true)
  | "__xor__" => some (.xor, false) | "__rxor__" => some (.xor, true)
  | _ => none

/-- **`view.mapping`** (`dictview_mapping`): a read-only proxy of the view's dict. -/
def viewMapping [PyWrites m V] (self _args _kwargs : V) : m V := do
  let (_, d) ← viewOf self
  Proto.allocMappingProxy d

/-- This file's bodies. -/
def dictViewOpsMethod : Builtin → String → Option BuiltinImpl
  | .dict_values, "__reversed__" => some fun {_} {_} [_] [_] => viewReversed
  | .dict_values, "__repr__" => some fun {_} {_} [_] [_] => viewRepr
  | t, n =>
    if (t == .dict_keys || t == .dict_values || t == .dict_items) && n == getsetHook "mapping" then
      some fun {_} {_} [_] [_] => viewMapping
    else if t != .dict_keys && t != .dict_items then none
    else match n with
      | "__contains__" => some fun {_} {_} [_] [_] => viewContains
      | "__reversed__" => some fun {_} {_} [_] [_] => viewReversed
      | "__repr__" => some fun {_} {_} [_] [_] => viewRepr
      | "isdisjoint" => some fun {_} {_} [_] [_] => viewIsdisjoint
      | _ =>
        match cmpOfName n, setOpOfName n with
        | some op, _ => some fun {_} {_} [_] [_] => viewCompare op n
        | none, some (op, rev) => some fun {_} {_} [_] [_] => viewSetOpBody op rev n
        | none, none => none

end

end

end StrataPython.Dyn.Sem.Library
