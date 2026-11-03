/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Dom

set_option autoImplicit false

/-!
# Classes and identity of values that are not objects

`Value.classOfImm` is `type(v)` for a value that is not an object of the store, and
`Value.identical` is `is` (CPython 3.12): on objects it compares ids, on singletons and built-in
constants it compares the values, and on two equal immediates of the same type it is unknown,
since CPython's answer depends on its caches; so is a symbolic hash against an `int`, which may
be equal in some run.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- The type of a descriptor of the kind `k`, unbound. -/
def DescrKind.descrType : DescrKind → Builtin
  | .method => .method_descriptor
  | .slotWrapper => .wrapper_descriptor
  | .classMethod => .classmethod_descriptor
  | .staticMethod => .staticmethod
  | .getset => .getset_descriptor
  | .member => .member_descriptor
  | .tpNew => .builtin_function_or_method

/-- The type of a descriptor of the kind `k`, bound to an object. -/
def DescrKind.boundType : DescrKind → Builtin
  | .slotWrapper => .«method-wrapper»
  | _ => .builtin_function_or_method

/-- `type(v)` when `v` is not an object of the store. -/
def Value.classOfImm : Value → Option Value
  | .undef _ => Option.none
  | .none => some (.builtin .NoneType)
  | .notImplemented => some (.builtin .NotImplementedType)
  | .ellipsis => some (.builtin .ellipsis)
  | .bool _ => some (.builtin .bool)
  | .int _ | .symHash _ => some (.builtin .int)
  | .float _ => some (.builtin .float)
  | .str _ => some (.builtin .str)
  | .bytes _ => some (.builtin .bytes)
  | .tuple _ => some (.builtin .tuple)
  | .range .. => some (.builtin .range)
  | .slice .. => some (.builtin .slice)
  | .builtin b => some (.builtin b.typeOf)
  | .descr _ _ k => some (.builtin k.descrType)
  | .bound _ _ _ k => some (.builtin k.boundType)
  | .method .. => some (.builtin .method)
  | .traceback => some (.builtin .traceback)
  | .obj _ => Option.none

/-- Which kind of immediate a value is, for `is` on two equal values: two values of one kind
are of one type. -/
def Value.immKind : Value → Option Nat
  | .int _ => some 0
  | .float _ => some 1
  | .str _ => some 2
  | .bytes _ => some 3
  | .tuple _ => some 4
  | .range .. => some 5
  | .slice .. => some 6
  | .bound .. => some 7
  | .method .. => some 8
  | .traceback => some 9
  | .symHash _ => some 10
  | _ => Option.none

/-- Whether a value is a singleton or a built-in constant, which `is` compares by value. -/
def Value.isConstant : Value → Bool
  | .none | .notImplemented | .ellipsis | .bool _ | .builtin _ | .descr .. => true
  | _ => false

/-- Whether `c` is a class whose values are always immediates: `NoneType`, `bool`, `int`,
`float`, `str`, `bytes`, `tuple`, `range` or `slice`.  `alloc` refuses an object of
one (`StoreOK`). -/
def Value.isImmClass : Value → Bool
  | .builtin b => [Builtin.NoneType, .bool, .int, .float, .str, .bytes, .tuple, .range,
      .slice].contains b
  | _ => false

/-- `a is b`. -/
def Value.identical : Value → Value → IdResult
  | .obj a, .obj b => if a = b then .yes else .no
  | .symHash _, .symHash _ | .symHash _, .int _ | .int _, .symHash _ => .unknown
  | a, b =>
    if a.isConstant && b.isConstant then (if a == b then .yes else .no)
    else match a.immKind, b.immKind with
      | some i, some j => if i = j && a == b then .unknown else .no
      | _, _ => .no

end

end StrataPython.Dyn.Sem
