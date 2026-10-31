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

@[dyn_sem Py.truthy] def truthy (_val : Value) (err : Target E [Value]) : Sem ε E Bool :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.truthy")

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

@[dyn_sem Py.add] def add (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.add")

@[dyn_sem Py.sub] def sub (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.sub")

@[dyn_sem Py.mult] def mult (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.mult")

@[dyn_sem Py.div] def div (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.div")

@[dyn_sem Py.floorDiv] def floorDiv (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.floorDiv")

@[dyn_sem Py.mod] def mod (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.mod")

@[dyn_sem Py.pow] def pow (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.pow")

@[dyn_sem Py.matMult] def matMult (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.matMult")

@[dyn_sem Py.lShift] def lShift (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.lShift")

@[dyn_sem Py.rShift] def rShift (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.rShift")

@[dyn_sem Py.bitAnd] def bitAnd (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.bitAnd")

@[dyn_sem Py.bitOr] def bitOr (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.bitOr")

@[dyn_sem Py.bitXor] def bitXor (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.bitXor")

@[dyn_sem Py.iAdd] def iAdd (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iAdd")

@[dyn_sem Py.iSub] def iSub (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iSub")

@[dyn_sem Py.iMult] def iMult (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iMult")

@[dyn_sem Py.iMatMult] def iMatMult (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iMatMult")

@[dyn_sem Py.iDiv] def iDiv (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iDiv")

@[dyn_sem Py.iFloorDiv] def iFloorDiv (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iFloorDiv")

@[dyn_sem Py.iMod] def iMod (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iMod")

@[dyn_sem Py.iPow] def iPow (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iPow")

@[dyn_sem Py.iLShift] def iLShift (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iLShift")

@[dyn_sem Py.iRShift] def iRShift (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iRShift")

@[dyn_sem Py.iBitAnd] def iBitAnd (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iBitAnd")

@[dyn_sem Py.iBitOr] def iBitOr (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iBitOr")

@[dyn_sem Py.iBitXor] def iBitXor (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.iBitXor")

@[dyn_sem Py.not_] def not_ (_operand : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.not")

@[dyn_sem Py.uSub] def uSub (_operand : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.uSub")

@[dyn_sem Py.uAdd] def uAdd (_operand : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.uAdd")

@[dyn_sem Py.invert] def invert (_operand : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.invert")

@[dyn_sem Py.eq] def eq (_lhs : Value) (_rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.eq")

@[dyn_sem Py.notEq] def notEq (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.notEq")

@[dyn_sem Py.lt] def lt (_lhs : Value) (_rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.lt")

@[dyn_sem Py.ltE] def ltE (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.ltE")

@[dyn_sem Py.gt] def gt (_lhs : Value) (_rhs : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.gt")

@[dyn_sem Py.gtE] def gtE (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.gtE")

@[dyn_sem Py.in_] def in_ (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.in")

@[dyn_sem Py.notIn] def notIn (_lhs : Value) (_rhs : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.notIn")

@[dyn_sem Py.mkKwargs] def mkKwargs (_kvs : (Array Value)) : Sem ε E Value :=
  runTotalFree "py.mkKwargs" #[] (PyM.gap (σ := σ) (fr := true) (e := .pure) "not modelled yet: py.mkKwargs")

@[dyn_sem Py.mkList] def mkList (_elems : (Array Value)) : Sem ε E Value :=
  runTotalFree "py.mkList" #[] (PyM.gap (σ := σ) (fr := true) (e := .pure) "not modelled yet: py.mkList")

@[dyn_sem Py.mkSet] def mkSet (_elems : (Array Value)) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.mkSet")

@[dyn_sem Py.mkTuple] def mkTuple (_elems : (Array Value)) : Sem ε E Value :=
  runTotalFree "py.mkTuple" #[] (PyM.gap (σ := σ) (fr := true) (e := .pure) "not modelled yet: py.mkTuple")

@[dyn_sem Py.getItem] def getItem (_obj : Value) (_key : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.getItem")

@[dyn_sem Py.getOptionalItem] def getOptionalItem (_obj : Value) (_key : Value)
    (_fallback : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.getOptionalItem")

@[dyn_sem Py.setItem] def setItem (_obj : Value) (_key : Value) (_val : Value)
    (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.setItem")

@[dyn_sem Py.delItem] def delItem (_obj : Value) (_key : Value) (err : Target E [Value])
    : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.delItem")

@[dyn_sem Py.mkSlice] def mkSlice (_lo : Value) (_hi : Value) (_step : Value) : Sem ε E Value :=
  runTotalFree "py.mkSlice" #[] (PyM.gap (σ := σ) (fr := true) (e := .pure) "not modelled yet: py.mkSlice")

@[dyn_sem Py.getSlice] def getSlice (_obj : Value) (_lo : Value) (_hi : Value) (_step : Value)
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.getSlice")

@[dyn_sem Py.unpackSeq] def unpackSeq (_val : Value) (_n : Int) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.unpackSeq")

@[dyn_sem Py.unpackEx] def unpackEx (_val : Value) (_before : Int) (_after : Int)
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.unpackEx")

@[dyn_sem Py.listToTuple] def listToTuple (_list : Value) : Sem ε E Value :=
  runTotalFree "py.listToTuple" #[] (PyM.gap (σ := σ) (fr := true) (e := .reads) "not modelled yet: py.listToTuple")

@[dyn_sem Py.argsTuple] def argsTuple (_callee : Value) (_iterable : Value)
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.argsTuple")

@[dyn_sem Py.tupleGet] def tupleGet (_tup : Value) (_i : Int) : Sem ε E Value :=
  runTotalFree "py.tupleGet" #[] (PyM.gap (σ := σ) (fr := true) (e := .pure) "not modelled yet: py.tupleGet")

@[dyn_sem Py.dictMerge] def dictMerge (_callee : Value) (_dict : Value) (_other : Value)
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.dictMerge")

@[dyn_sem Py.dictUpdate] def dictUpdate (_dict : Value) (_other : Value) (err : Target E [Value])
    : Sem ε E Value :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .calls) "not modelled yet: py.dictUpdate")

@[dyn_sem Py.listAppend] def listAppend (_list : Value) (_value : Value) : Sem ε E Unit :=
  runTotalFree "py.listAppend" #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.listAppend")

@[dyn_sem Py.listExtend] def listExtend (_list : Value) (_iterable : Value)
    (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.listExtend")

@[dyn_sem Py.setAdd] def setAdd (_set : Value) (_value : Value) (err : Target E [Value])
    : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.setAdd")

@[dyn_sem Py.setUpdate] def setUpdate (_set : Value) (_iterable : Value) (err : Target E [Value])
    : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.setUpdate")

@[dyn_sem Py.dictSet] def dictSet (_dict : Value) (_key : Value) (_value : Value)
    (err : Target E [Value]) : Sem ε E Unit :=
  runRuleFree err #[] (PyM.gap (σ := σ) (fr := true) (e := .writes) "not modelled yet: py.dictSet")

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
