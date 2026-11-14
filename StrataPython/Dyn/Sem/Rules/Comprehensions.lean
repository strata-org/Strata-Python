/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Iter

set_option autoImplicit false

/-!
# Comprehensions

A list, set or dict comprehension runs its first `for` clause by `listComp`, `setComp` or
`dictComp`, which loop by `again` (`Proto.compStep`); a later `for` clause is `compFor`, its `if`s
`compIf`, and its element is added by `compAppend`, `compAdd` or `compStore`.  Each rule runs its
regions through `regionHandle`; their parameters, an accumulator and an item, hold no ref.
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.listComp] def listComp (iterable : Value)
    (each : Region ε [ListAcc, Value] (Except Value Unit)) (err : Target E [Value])
    (st : Option (Value × Value)) (again : Again E (Value × Value)) : Sem ε E Value :=
  runLoopFree err again st
    #[regionHandle each (fun a => (twoValues a).map fun (acc, x) => (ListAcc.mk acc, x))
      fun _ => .none]
    (Proto.listCompStep (m := PyM σ .writes true) iterable)

@[dyn_sem Py.setComp] def setComp (iterable : Value)
    (each : Region ε [SetAcc, Value] (Except Value Unit)) (err : Target E [Value])
    (st : Option (Value × Value)) (again : Again E (Value × Value)) : Sem ε E Value :=
  runLoopFree err again st
    #[regionHandle each (fun a => (twoValues a).map fun (acc, x) => (SetAcc.mk acc, x))
      fun _ => .none]
    (Proto.setCompStep (m := PyM σ .writes true) iterable)

@[dyn_sem Py.dictComp] def dictComp (iterable : Value)
    (each : Region ε [DictAcc, Value] (Except Value Unit)) (err : Target E [Value])
    (st : Option (Value × Value)) (again : Again E (Value × Value)) : Sem ε E Value :=
  runLoopFree err again st
    #[regionHandle each (fun a => (twoValues a).map fun (acc, x) => (DictAcc.mk acc, x))
      fun _ => .none]
    (Proto.dictCompStep (m := PyM σ .writes true) iterable)

@[dyn_sem Py.compFor] def compFor (iterable : Value)
    (each : Region ε [Value] (Except Value Unit)) (err : Target E [Value]) (st : Option Value)
    (again : Again E Value) : Sem ε E Unit :=
  runLoopFree err again st #[regionHandle each oneValue fun _ => .none]
    (Proto.compForStep (m := PyM σ .writes true) iterable)

@[dyn_sem Py.compIf] def compIf (cond : Region ε [] (Except Value Bool))
    («then» : Region ε [] (Except Value Unit)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err
    #[regionHandle cond noValues .bool, regionHandle «then» noValues fun _ => .none]
    (Proto.compIfRun (m := PyM σ .calls true))

@[dyn_sem Py.compAppend] def compAppend (out : ListAcc)
    (elt : Region ε [] (Except Value Value)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[regionHandle elt noValues id]
    (Proto.compAppendRun (m := PyM σ .writes true) out.obj)

@[dyn_sem Py.compAdd] def compAdd (out : SetAcc)
    (elt : Region ε [] (Except Value Value)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[regionHandle elt noValues id]
    (Proto.compAddRun (m := PyM σ .writes true) out.obj)

@[dyn_sem Py.compStore] def compStore (out : DictAcc)
    (key : Region ε [] (Except Value Value)) (value : Region ε [] (Except Value Value))
    (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[regionHandle key noValues id, regionHandle value noValues id]
    (Proto.compStoreRun (m := PyM σ .writes true) out.obj)

end

end StrataPython.Dyn.Sem.Rules
