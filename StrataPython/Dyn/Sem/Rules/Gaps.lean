/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes

set_option autoImplicit false

/-!
# The operations that are not modelled yet

Each rule here stops with the gap "not modelled yet: <op>", at its operation's declared effect.  A
commit that models an operation moves its rule out of this file.  The contract operations have
no rule.
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.listComp] def listComp (_iterable : Value)
    (_each : Region ε [ListAcc, Value] (Except Value Unit)) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (PyPure.gap (m := PyM σ .writes true) "not modelled yet: py.listComp")

@[dyn_sem Py.setComp] def setComp (_iterable : Value)
    (_each : Region ε [SetAcc, Value] (Except Value Unit)) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (PyPure.gap (m := PyM σ .writes true) "not modelled yet: py.setComp")

@[dyn_sem Py.dictComp] def dictComp (_iterable : Value)
    (_each : Region ε [DictAcc, Value] (Except Value Unit)) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (PyPure.gap (m := PyM σ .writes true) "not modelled yet: py.dictComp")

@[dyn_sem Py.compFor] def compFor (_iterable : Value)
    (_each : Region ε [Value] (Except Value Unit)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyPure.gap (m := PyM σ .writes true) "not modelled yet: py.compFor")

@[dyn_sem Py.compIf] def compIf (_cond : Region ε [] (Except Value Bool))
    (_then : Region ε [] (Except Value Unit)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyPure.gap (m := PyM σ .writes true) "not modelled yet: py.compIf")

@[dyn_sem Py.compAppend] def compAppend (_out : ListAcc)
    (_elt : Region ε [] (Except Value Value)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyPure.gap (m := PyM σ .writes true) "not modelled yet: py.compAppend")

@[dyn_sem Py.compAdd] def compAdd (_out : SetAcc)
    (_elt : Region ε [] (Except Value Value)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyPure.gap (m := PyM σ .writes true) "not modelled yet: py.compAdd")

@[dyn_sem Py.compStore] def compStore (_out : DictAcc)
    (_key : Region ε [] (Except Value Value)) (_value : Region ε [] (Except Value Value))
    (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyPure.gap (m := PyM σ .writes true) "not modelled yet: py.compStore")

end

end StrataPython.Dyn.Sem.Rules
