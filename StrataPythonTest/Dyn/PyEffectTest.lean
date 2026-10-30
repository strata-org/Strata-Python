/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Env
public import StrataDyn.DDM
import StrataDyn.Env.WF
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Env
meta import StrataDyn.DDM
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The effects of Python's operations

Every operation of `Py.env` whose effect is not `writes`, with that effect.  An operation that
changes effect must be updated here, and a new operation that is not `writes` must be added.

No `pure` operation that falls through declares a successor: an operation that raises reads the
exception being handled, which becomes the new exception's `__context__`.

The operations that declare no successor, which never raise, are listed too, since
`docs/PythonToDyn.md` (§2) names them.
-/

namespace StrataPython.Dyn.PyEffectTest

open Strata.Dyn

/-- Each instruction of `Py.env` (the base's excluded) that is not `writes`, as its name's text
and its effect, sorted by name. -/
private def notWrites : List (String × Effect) :=
  let all := Py.names.filterMap fun n =>
    match Py.env.get? n with
    | some (.insn (isig := σ) _) =>
      let t := ToDDM.nameText n
      if σ.effect != .writes && t.startsWith "py." then some (t, σ.effect) else none
    | _ => none
  all.mergeSort (fun a b => decide (a.1 ≤ b.1))

#guard notWrites == [
  ("py.Completion.case", .pure), ("py.add", .calls), ("py.allIn", .reads), ("py.allItems", .reads),
  ("py.anyIn", .reads), ("py.anyItems", .reads), ("py.argOf", .reads), ("py.ascii", .calls),
  ("py.assertionError", .pure), ("py.attr", .calls), ("py.attrLoc", .reads),
  ("py.bindArgs", .calls), ("py.bindsTo", .reads), ("py.bitAnd", .calls), ("py.bitOr", .calls),
  ("py.bitXor", .calls), ("py.boolLit", .pure), ("py.bytesLit", .pure),
  ("py.completionBreak", .pure), ("py.completionContinue", .pure), ("py.completionNormal", .pure),
  ("py.completionRaise", .pure), ("py.completionReturn", .pure), ("py.dictKeysWithin", .reads),
  ("py.dictMerge", .calls), ("py.dictUpdate", .calls), ("py.div", .calls),
  ("py.ellipsisLit", .pure), ("py.enterMethod", .calls), ("py.eq", .calls), ("py.excMatch", .calls),
  ("py.exitMethod", .calls), ("py.extraKwargs", .reads), ("py.floatLit", .pure),
  ("py.floorDiv", .calls), ("py.fmtValue", .calls), ("py.getItem", .calls),
  ("py.getOptionalItem", .calls), ("py.getSlice", .calls), ("py.globalCell", .pure),
  ("py.gt", .calls), ("py.gtE", .calls), ("py.handledExc", .reads), ("py.in", .calls),
  ("py.instanceState", .reads), ("py.intIsOneOf", .pure), ("py.intLit", .pure),
  ("py.invert", .calls), ("py.is", .pure), ("py.isDefined", .pure), ("py.isImmutableScalar", .pure),
  ("py.isInstance", .calls), ("py.isNot", .pure), ("py.isStopIteration", .reads),
  ("py.itemLoc", .pure), ("py.lShift", .calls), ("py.len", .calls), ("py.listToTuple", .reads),
  ("py.loadGlobal", .calls), ("py.lt", .calls), ("py.ltE", .calls), ("py.matMult", .calls),
  ("py.mkClosure", .reads), ("py.mkDict", .calls), ("py.mkKwargs", .pure), ("py.mkList", .pure),
  ("py.mkSet", .calls), ("py.mkSlice", .pure), ("py.mkTuple", .pure), ("py.mod", .calls),
  ("py.mult", .calls), ("py.noneLit", .pure), ("py.not", .calls), ("py.notEq", .calls),
  ("py.notIn", .calls), ("py.objLoc", .reads), ("py.pow", .calls), ("py.rShift", .calls),
  ("py.reSearch", .reads), ("py.reachLoc", .reads), ("py.repr", .calls),
  ("py.requireDefined", .reads), ("py.stdClass", .pure), ("py.str", .calls),
  ("py.strConcat", .pure), ("py.strIsOneOf", .pure), ("py.strLit", .pure), ("py.sub", .calls),
  ("py.truthy", .calls), ("py.tupleGet", .pure), ("py.typeIsSubclass", .reads), ("py.uAdd", .calls),
  ("py.uSub", .calls), ("py.undef", .pure)]

/-- The operations of `Py.env` that are `pure`, have a result, and declare a successor, by name. -/
private def pureWithFailure : List String :=
  Py.names.filterMap fun n =>
    match Py.env.get? n with
    | some (.insn (isig := σ) _) =>
      if σ.effect == .pure && σ.returnType.isSome && !σ.succs.isEmpty then
        some (ToDDM.nameText n) else none
    | _ => none

#guard pureWithFailure == []

/-- Each instruction of `Py.env` (the base's excluded) that declares no successor, as its name's
text, sorted. -/
private def total : List String :=
  let all := Py.names.filterMap fun n =>
    match Py.env.get? n with
    | some (.insn (isig := σ) _) =>
      let t := ToDDM.nameText n
      if σ.succs.isEmpty && t.startsWith "py." then some t else none
    | _ => none
  all.mergeSort (fun a b => decide (a ≤ b))

#guard total == [
  "py.argOf", "py.assertionError", "py.attrLoc", "py.bindsTo", "py.boolLit", "py.bytesLit",
  "py.completionBreak", "py.completionContinue", "py.completionNormal", "py.completionRaise",
  "py.completionReturn", "py.dictKeysWithin", "py.ellipsisLit", "py.extraKwargs", "py.floatLit",
  "py.globalCell", "py.instanceState", "py.intIsOneOf", "py.intLit", "py.is", "py.isDefined",
  "py.isImmutableScalar", "py.isNot", "py.isStopIteration", "py.itemLoc", "py.listAppend",
  "py.listToTuple", "py.mkClosure", "py.mkKwargs", "py.mkList", "py.mkSlice", "py.mkTuple",
  "py.noneLit", "py.objLoc", "py.popExcept", "py.pushExcInfo", "py.pushPending", "py.reachLoc",
  "py.stdClass", "py.strConcat", "py.strIsOneOf", "py.strLit", "py.tupleGet", "py.undef",
  "py.unsupported"]

end StrataPython.Dyn.PyEffectTest
