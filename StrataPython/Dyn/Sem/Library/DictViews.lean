/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Sequences

set_option autoImplicit false

/-!
# The dict views

Generic over the record, CPython 3.12's `dict_keys`, `dict_values` and `dict_items`
(`Objects/dictobject.c`): `dict.keys()`, `values()` and `items()` give a live view of the dict, an
object whose state is `.view kind d`.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The kind and the dict of the view `v`. -/
def viewOf [PyReads m V] (v : V) : m (Builtin × V) := do
  let some (.iter (.view k d)) ← PyReads.objView v |
    PyPure.modelInvariant "a method of a dict view on a value that is not one"
  return (k, d)

/-- The iterator kind of a view kind. -/
def viewIterKind : Builtin → Builtin
  | .dict_values => .dict_valueiterator
  | .dict_items => .dict_itemiterator
  | _ => .dict_keyiterator

/-- **`dict.keys()`**, `values()` and `items()`: a new view of the kind `k`. -/
def dictViewMethod [PyWrites m V] (k : Builtin) (sig : BuiltinSig) (self args kwargs : V) : m V := do
  discard <| bound .dict self sig args kwargs
  newIter k (.view k self)

/-- **`view.__len__()`**. -/
def viewLen [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| wrapperArgs "__len__" 0 args kwargs
  let (_, d) ← viewOf self
  return intValue (m := m) (← PyReads.dictLen d)

/-- **`view.__iter__()`**: a new iterator of the view's kind over the dict. -/
def viewIter [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| wrapperArgs "__iter__" 0 args kwargs
  let (k, d) ← viewOf self
  let ik := viewIterKind k
  let (_, ver) ← PyReads.dictFlags d
  newIter ik (.dict ik d 0 (← PyReads.dictLen d) ver)

/-- This file's bodies. -/
def dictViewsMethod : Builtin → String → Option BuiltinImpl
  | .dict, "keys" => some fun {_} {_} [_] [_] => dictViewMethod .dict_keys Signatures.dict_keys
  | .dict, "values" =>
    some fun {_} {_} [_] [_] => dictViewMethod .dict_values Signatures.dict_values
  | .dict, "items" => some fun {_} {_} [_] [_] => dictViewMethod .dict_items Signatures.dict_items
  | .dict_keys, "__len__" | .dict_values, "__len__" | .dict_items, "__len__" =>
    some fun {_} {_} [_] [_] => viewLen
  | .dict_keys, "__iter__" | .dict_values, "__iter__" | .dict_items, "__iter__" =>
    some fun {_} {_} [_] [_] => viewIter
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
