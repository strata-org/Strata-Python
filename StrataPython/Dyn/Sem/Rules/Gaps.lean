/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Concrete
public import StrataPython.Dyn.Sem.PyTypes

set_option autoImplicit false

/-!
# The operations that are not modelled yet

Each rule here stops with the gap "not modelled yet: <op>", at its operation's declared effect.  A
commit that models an operation moves its rule out of this file.  `py.mkClosure` and the
contract operations have no rule.
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

@[dyn_sem Py.bindArgs] def bindArgs (_args _kwargs _defaults : Value) (_nPosOnly _nPos : Int)
    (_varPos _varKw : Bool) (_names : Array String) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.bindArgs")

@[dyn_sem Py.call] def call (_func : Value) (_args : Value) (_kwargs : Value)
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.call")

@[dyn_sem Py.qualifiedRef] def qualifiedRef (_moduleName : String) (_name : String)
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.qualifiedRef")

@[dyn_sem Py.attr] def attr (_obj : Value) (_name : String) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.attr")

@[dyn_sem Py.setAttr] def setAttr (_obj : Value) (_name : String) (_val : Value)
    (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.setAttr")

@[dyn_sem Py.delAttr] def delAttr (_obj : Value) (_name : String) (err : Target E [Value])
    : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.delAttr")

@[dyn_sem Py.importModule] def importModule (_module : String) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.importModule")

@[dyn_sem Py.importFrom] def importFrom (_module : String) (_name : String)
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.importFrom")

@[dyn_sem Py.mkKwargs] def mkKwargs (_kvs : (Array Value)) : Sem ε E Value :=
  runTotalFree "py.mkKwargs" #[] (PyM.gap (σ := σ) (fr := true) (e := .pure) "not modelled yet: py.mkKwargs")

@[dyn_sem Py.argsTuple] def argsTuple (_callee : Value) (_iterable : Value)
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.argsTuple")

@[dyn_sem Py.dictMerge] def dictMerge (_callee : Value) (_dict : Value) (_other : Value)
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.dictMerge")

@[dyn_sem Py.dictUpdate] def dictUpdate (_dict : Value) (_other : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.dictUpdate")


@[dyn_sem Py.getIter] def getIter (_obj : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.getIter")

@[dyn_sem Py.next] def next (_iter : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.next")

@[dyn_sem Py.isStopIteration] def isStopIteration (_exc : Value) : Sem ε E Bool :=
  runTotalFree "py.isStopIteration" #[]
    (PyM.gap (σ := σ) (fr := true) (e := .reads) "not modelled yet: py.isStopIteration")

@[dyn_sem Py.toException] def toException (_val : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.toException")

@[dyn_sem Py.setCause] def setCause (_exc : Value) (_cause : Value) (err : Target E [Value])
    : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.setCause")

@[dyn_sem Py.pushExcInfo] def pushExcInfo (_exc : Value) : Sem ε E Value :=
  runTotalFree "py.pushExcInfo" #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.pushExcInfo")

@[dyn_sem Py.pushPending] def pushPending (_pending : Py.Completion.Val) : Sem ε E Value :=
  runTotalFree "py.pushPending" #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.pushPending")

@[dyn_sem Py.popExcept] def popExcept (_prev : Value) : Sem ε E Unit :=
  runTotalFree "py.popExcept" #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.popExcept")

@[dyn_sem Py.handledExc] def handledExc  (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .reads) "not modelled yet: py.handledExc")

@[dyn_sem Py.excMatch] def excMatch (_exc : Value) (_type : Value) (err : Target E [Value])
    : Sem ε E Bool :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.excMatch")

@[dyn_sem Py.enterMethod] def enterMethod (_mgr : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.enterMethod")

@[dyn_sem Py.exitMethod] def exitMethod (_mgr : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.exitMethod")

@[dyn_sem Py.exitWithExc] def exitWithExc (_exit : Value) (_exc : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.exitWithExc")

@[dyn_sem Py.repr] def repr (_val : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.repr")

@[dyn_sem Py.toStr] def toStr (_val : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.str")

@[dyn_sem Py.ascii] def ascii (_val : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.ascii")

@[dyn_sem Py.fmtValue] def fmtValue (_val : Value) (_spec : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.fmtValue")

@[dyn_sem Py.strConcat] def strConcat (_parts : (Array Value)) : Sem ε E Value :=
  runTotalFree "py.strConcat" #[] (PyM.gap (σ := σ) (fr := true) (e := .pure) "not modelled yet: py.strConcat")

@[dyn_sem Py.listComp] def listComp (_iterable : Value)
    (_each : Region ε [ListAcc, Value] (Except Value Unit)) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.listComp")

@[dyn_sem Py.setComp] def setComp (_iterable : Value)
    (_each : Region ε [SetAcc, Value] (Except Value Unit)) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.setComp")

@[dyn_sem Py.dictComp] def dictComp (_iterable : Value)
    (_each : Region ε [DictAcc, Value] (Except Value Unit)) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.dictComp")

@[dyn_sem Py.compFor] def compFor (_iterable : Value)
    (_each : Region ε [Value] (Except Value Unit)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.compFor")

@[dyn_sem Py.compIf] def compIf (_cond : Region ε [] (Except Value Bool))
    (_then : Region ε [] (Except Value Unit)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.compIf")

@[dyn_sem Py.compAppend] def compAppend (_out : ListAcc)
    (_elt : Region ε [] (Except Value Value)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.compAppend")

@[dyn_sem Py.compAdd] def compAdd (_out : SetAcc)
    (_elt : Region ε [] (Except Value Value)) (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.compAdd")

@[dyn_sem Py.compStore] def compStore (_out : DictAcc)
    (_key : Region ε [] (Except Value Value)) (_value : Region ε [] (Except Value Value))
    (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.compStore")

end

end StrataPython.Dyn.Sem.Rules
