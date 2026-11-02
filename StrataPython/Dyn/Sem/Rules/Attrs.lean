/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Attrs

set_option autoImplicit false

/-!
# Attributes

`obj.name`, its write and its deletion, through the attribute protocol (`Proto/Attrs.lean`).
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.attr] def attr (obj : Value) (name : String) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.getAttr (m := PyM σ .calls true) obj name)

@[dyn_sem Py.setAttr] def setAttr (obj : Value) (name : String) (val : Value)
    (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (Proto.setAttr (m := PyM σ .writes true) obj name (some val))

@[dyn_sem Py.delAttr] def delAttr (obj : Value) (name : String) (err : Target E [Value]) :
    Sem ε E Unit :=
  runRuleFree err #[] (Proto.setAttr (m := PyM σ .writes true) obj name none)

end

end StrataPython.Dyn.Sem.Rules
