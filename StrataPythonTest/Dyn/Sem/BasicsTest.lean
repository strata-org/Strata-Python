/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.Basics
meta import StrataPython.Dyn.Sem.Basics

set_option autoImplicit false

/-!
# `is` and `type()` of values that are not objects

`is` on each pair of kinds, and `type()` of the immediates and constants, with CPython 3.12's
answers: `type(NotImplemented)`, `type(...)`, `type(int.__add__)` and `type((1).__add__)` are
CPython 3.12.15's.
-/

namespace StrataPython.Dyn.Sem.BasicsTest

open StrataPython.Dyn.Sem

/-- The name of `type(v)`. -/
def typeName (v : Value) : Option String :=
  match v.classOfImm with
  | some (.builtin b) => some b.info.name
  | _ => none

-- Objects compare by id.
#guard Value.identical (.obj 1) (.obj 1) == .yes
#guard Value.identical (.obj 1) (.obj 2) == .no
-- Singletons and built-in constants compare by value.
#guard Value.identical .none .none == .yes
#guard Value.identical .notImplemented .ellipsis == .no
#guard Value.identical (.bool true) (.bool true) == .yes
#guard Value.identical (.bool true) (.bool false) == .no
#guard Value.identical (.builtin .len) (.builtin .len) == .yes
#guard Value.identical (.builtin .len) (.builtin .print) == .no
#guard Value.identical (.descr .str "upper" .method) (.descr .str "upper" .method) == .yes
-- Two equal immediates of one type depend on CPython's caching.
#guard Value.identical (.int 1) (.int 1) == .unknown
#guard Value.identical (.ofString "a") (.ofString "a") == .unknown
#guard Value.identical (.ofFloat 1.5) (.ofFloat 1.5) == .unknown
#guard Value.identical (.tuple #[]) (.tuple #[]) == .unknown
#guard Value.identical (.bound (.int 1) .int "__add__" .slotWrapper)
  (.bound (.int 1) .int "__add__" .slotWrapper) == .unknown
-- A symbolic hash may equal an int in some run.
#guard Value.identical (.symHash (HashSrc.buffer [97].toByteArray)) (.int 5) == .unknown
#guard Value.identical (.symHash (HashSrc.buffer [97].toByteArray)) (.symHash (HashSrc.buffer [98].toByteArray)) == .unknown
-- Unequal immediates, values of two types, and an object against an immediate are never one.
#guard Value.identical (.int 1) (.int 2) == .no
#guard Value.identical (.int 1) (.bool true) == .no
#guard Value.identical (.int 1) (.ofFloat 1.0) == .no
#guard Value.identical (.obj 0) (.int 0) == .no
#guard Value.identical .none (.int 0) == .no

#guard typeName .notImplemented == some "NotImplementedType"
#guard typeName .ellipsis == some "ellipsis"
#guard typeName (.descr .int "__add__" .slotWrapper) == some "wrapper_descriptor"
#guard typeName (.bound (.int 1) .int "__add__" .slotWrapper) == some "method-wrapper"
#guard typeName (.descr .str "upper" .method) == some "method_descriptor"
#guard typeName (.builtin .len) == some "builtin_function_or_method"
#guard typeName (.builtin .int) == some "type"
#guard typeName (.builtin .exit) == some "Quitter"
#guard typeName (.symHash (HashSrc.buffer [97].toByteArray)) == some "int"
#guard typeName (.obj 3) == none

-- No object has a class whose values are always immediates.
#guard (Value.builtin .int).isImmClass
#guard !(Value.builtin .list).isImmClass

-- A static method of a built-in type is one value per type and name, so `is` compares it by
-- value; a method bound to a value is not.
#guard (Value.bound .none .str "maketrans" .staticMethod).isConstant
#guard !(Value.bound .none .list "append" .method).isConstant

end StrataPython.Dyn.Sem.BasicsTest
