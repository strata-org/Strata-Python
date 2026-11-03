/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Exceptions

set_option autoImplicit false

/-!
# Exceptions and `with`

Raising, chaining and matching exceptions, the exception being handled, and the lookups and the
exceptional call of `with`, through `Proto/Exceptions.lean`.
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.toException] def toException (val : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.toException (m := PyM σ .writes true) val)

@[dyn_sem Py.setCause] def setCause (exc cause : Value) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (Proto.setCauseOf (m := PyM σ .writes true) exc cause)

@[dyn_sem Py.pushExcInfo] def pushExcInfo (exc : Value) : Sem ε E Value :=
  runTotalFree "py.pushExcInfo" #[] (do
    let prev ← PyReads.handled
    PyWrites.setHandled exc
    pure prev : PyM σ .writes true Value)

@[dyn_sem Py.pushPending] def pushPending (pending : Py.Completion.Val) : Sem ε E Value :=
  runTotalFree "py.pushPending" #[] (do
    let prev ← PyReads.handled
    if let .completionRaise exc := pending then PyWrites.setHandled exc
    pure prev : PyM σ .writes true Value)

@[dyn_sem Py.popExcept] def popExcept (prev : Value) : Sem ε E Unit :=
  runTotalFree "py.popExcept" #[] (PyWrites.setHandled prev : PyM σ .writes true Unit)

@[dyn_sem Py.handledExc] def handledExc (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let h ← PyReads.handled
    if h matches .none then Proto.raiseBuiltin "RuntimeError" "No active exception to reraise"
    pure h : PyM σ .reads true Value)

@[dyn_sem Py.excMatch] def excMatch (exc type : Value) (err : Target E [Value]) : Sem ε E Bool :=
  runRuleFree err #[] (Proto.excMatches (m := PyM σ .reads true) exc type)

@[dyn_sem Py.isStopIteration] def isStopIteration (exc : Value) : Sem ε E Bool :=
  runTotalFree "py.isStopIteration" #[]
    (do Proto.isSubclass (← PyReads.classOf exc) (.builtin .StopIteration) : PyM σ .reads true Bool)

@[dyn_sem Py.enterMethod] def enterMethod (mgr : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.enterOf (m := PyM σ .calls true) mgr)

@[dyn_sem Py.exitMethod] def exitMethod (mgr : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.exitOf (m := PyM σ .calls true) mgr)

@[dyn_sem Py.exitWithExc] def exitWithExc (exit exc : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (Proto.exitWithExc (m := PyM σ .writes true) exit exc)

end

end StrataPython.Dyn.Sem.Rules
