/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Containers

set_option autoImplicit false

/-!
# Operators

The binary and in-place operators, the unary operators, `not`, the truth test and the
comparisons, on built-in values and through user dunders (`Proto/Ops.lean`).  The in-place operators give the same results
as the binary ones, except where they change a list, a dict or a set (`Proto/Containers.lean`).
The binary operators that make a new set or dict from two objects read the operation's start,
so that they can fill it below `writes`; the others, and the in-place operators, which run at
`writes`, don't need it.
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.add] def add (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.binaryOp (m := PyM σ .calls true) .add lhs rhs)

@[dyn_sem Py.sub] def sub (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleIf (lhs matches .obj _ && rhs matches .obj _) err #[]
    (Proto.setOp (m := PyM σ .calls false) .sub lhs rhs)
    (Proto.binaryOp (m := PyM σ .calls true) .sub lhs rhs)

@[dyn_sem Py.mult] def mult (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.binaryOp (m := PyM σ .calls true) .mul lhs rhs)

@[dyn_sem Py.div] def div (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.binaryOp (m := PyM σ .calls true) .trueDiv lhs rhs)

@[dyn_sem Py.floorDiv] def floorDiv (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.binaryOp (m := PyM σ .calls true) .floorDiv lhs rhs)

@[dyn_sem Py.mod] def mod (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.binaryOp (m := PyM σ .calls true) .mod lhs rhs)

@[dyn_sem Py.pow] def pow (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.binaryOp (m := PyM σ .calls true) .pow lhs rhs)

@[dyn_sem Py.lShift] def lShift (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.binaryOp (m := PyM σ .calls true) .lshift lhs rhs)

@[dyn_sem Py.rShift] def rShift (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.binaryOp (m := PyM σ .calls true) .rshift lhs rhs)

@[dyn_sem Py.bitAnd] def bitAnd (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleIf (lhs matches .obj _ && rhs matches .obj _) err #[]
    (Proto.setOp (m := PyM σ .calls false) .and lhs rhs)
    (Proto.binaryOp (m := PyM σ .calls true) .and lhs rhs)

@[dyn_sem Py.bitOr] def bitOr (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleIf (lhs matches .obj _ && rhs matches .obj _) err #[]
    (Proto.setOp (m := PyM σ .calls false) .or lhs rhs)
    (Proto.binaryOp (m := PyM σ .calls true) .or lhs rhs)

@[dyn_sem Py.bitXor] def bitXor (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleIf (lhs matches .obj _ && rhs matches .obj _) err #[]
    (Proto.setOp (m := PyM σ .calls false) .xor lhs rhs)
    (Proto.binaryOp (m := PyM σ .calls true) .xor lhs rhs)

@[dyn_sem Py.iAdd] def iAdd (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .add lhs rhs)

@[dyn_sem Py.iSub] def iSub (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .sub lhs rhs)

@[dyn_sem Py.iMult] def iMult (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .mul lhs rhs)

@[dyn_sem Py.iDiv] def iDiv (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .trueDiv lhs rhs)

@[dyn_sem Py.iFloorDiv] def iFloorDiv (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .floorDiv lhs rhs)

@[dyn_sem Py.iMod] def iMod (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .mod lhs rhs)

@[dyn_sem Py.iPow] def iPow (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .pow lhs rhs)

@[dyn_sem Py.iLShift] def iLShift (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .lshift lhs rhs)

@[dyn_sem Py.iRShift] def iRShift (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .rshift lhs rhs)

@[dyn_sem Py.iBitAnd] def iBitAnd (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .and lhs rhs)

@[dyn_sem Py.iBitOr] def iBitOr (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .or lhs rhs)

@[dyn_sem Py.iBitXor] def iBitXor (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceOp (m := PyM σ .writes true) .xor lhs rhs)

@[dyn_sem Py.matMult] def matMult (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.matMultOp (m := PyM σ .calls true) lhs rhs)

@[dyn_sem Py.iMatMult] def iMatMult (lhs rhs : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.inplaceMatMult (m := PyM σ .calls true) lhs rhs)

@[dyn_sem Py.uSub] def uSub (operand : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.unaryOp (m := PyM σ .calls true) .neg operand)

@[dyn_sem Py.uAdd] def uAdd (operand : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.unaryOp (m := PyM σ .calls true) .pos operand)

@[dyn_sem Py.invert] def invert (operand : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.unaryOp (m := PyM σ .calls true) .invert operand)

@[dyn_sem Py.not_] def not_ (operand : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.notValue (m := PyM σ .calls true) operand)

@[dyn_sem Py.truthy] def truthy (val : Value) (err : Target E [Value]) : Sem ε E Bool :=
  runRuleFree err #[] (Proto.truthy (m := PyM σ .calls true) val)

@[dyn_sem Py.eq] def eq (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.richCompareV (m := PyM σ .calls true) .eq lhs rhs)

@[dyn_sem Py.notEq] def notEq (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.richCompareV (m := PyM σ .calls true) .ne lhs rhs)

@[dyn_sem Py.lt] def lt (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.richCompareV (m := PyM σ .calls true) .lt lhs rhs)

@[dyn_sem Py.ltE] def ltE (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.richCompareV (m := PyM σ .calls true) .le lhs rhs)

@[dyn_sem Py.gt] def gt (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.richCompareV (m := PyM σ .calls true) .gt lhs rhs)

@[dyn_sem Py.gtE] def gtE (lhs rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.richCompareV (m := PyM σ .calls true) .ge lhs rhs)

end

end StrataPython.Dyn.Sem.Rules
