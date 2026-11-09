/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Repr

set_option autoImplicit false

/-!
# The rules of `repr`, `str`, `ascii` and f-strings

`py.repr`, `py.str` and `py.ascii` are an f-string's `!r`, `!s` and `!a`, `py.fmtValue` its
`FORMAT_VALUE` after the conversion, and `py.strConcat` its `BUILD_STRING` (`Proto/Repr.lean`).
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.repr] def repr (val : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.reprOf (m := PyM σ .calls true) val)

@[dyn_sem Py.toStr] def toStr (val : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.strOf (m := PyM σ .calls true) val)

@[dyn_sem Py.ascii] def ascii (val : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.asciiOf (m := PyM σ .calls true) val)

/-- `FORMAT_VALUE`: an exact `str` with no spec as it is, else `format(val, spec)`. -/
@[dyn_sem Py.fmtValue] def fmtValue (val spec : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.formatOf (m := PyM σ .calls true) val spec)

@[dyn_sem Py.strConcat] def strConcat (parts : Array Value) : Sem ε E Value :=
  runTotalFree "py.strConcat" #[] (Proto.concatStrs (m := PyM σ .pure true) parts)

end

end StrataPython.Dyn.Sem.Rules
