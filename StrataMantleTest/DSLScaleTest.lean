/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env
import StrataMantle.Env.WF
import StrataMantle.DSL
public import StrataMantle.Base
-- The `#guard`s below run the signatures as compiled code.
meta import StrataMantle.WF
meta import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# A large `environment` block

`Scale` declares 240 instructions in one batch: Python's 61 operations, then most of them
again three times with a suffix, nearly four times Python's 64.  Each generated proof that
reduced a long literal in the elaborator, rather than the kernel, failed with "maximum
recursion depth" under the default `maxRecDepth`, at its own size: a reference's bound
`j < ops.size` at 123 instructions, the names as one list at 131, the stage's names at 165,
`mem_env` at 217.  This block is past all four.  A batch is still limited, at about 500
instructions, by the reference to instruction `j`, whose type reduces `ops[j]`.

The block takes about 25 s.  Most of it is the stage's freshness, which the kernel checks
by comparing every pair of names: quadratic in the batch.
-/

namespace Strata.Mantle.DSLScaleTest

/-- A Python-shaped environment of 240 instructions. -/
public environment Scale extends Base where
  namespace scale
  open base
  /-- Every value. -/
  type Value
  /-- How a protected block finished. -/
  data Completion where
    | completionNormal
    | completionReturn (value : Value)
    | completionRaise (exc : Value)
    | completionBreak
    | completionContinue
  insn undef (name : String) : Value
  insn isDefined (val : Value) : Bool
  insn truthy (val : Value) (^err (exc : Value)) : Bool
  insn requireDefined (val : Value) (excType msg : String) (^err (exc : Value)) : Value
  insn requireUndefined (val : Value) (excType msg : String) (^err (exc : Value)) : Unit
  insn requireAtMost (val : Value) (limit : Int) (excType msg : String) (^err (exc : Value)) : Unit
  insn intLit (val : Int) : Value
  insn floatLit (val : Float64) : Value
  insn strLit (val : String) : Value
  insn boolLit (val : Bool) : Value
  insn bytesLit (val : String) : Value
  insn noneLit  : Value
  insn call (func args kwargs : Value) (^err (exc : Value)) : Value
  insn qualifiedRef (moduleName name : String) (^err (exc : Value)) : Value
  insn mkClosure (code : Code) (*cells : (Ref Value)) : Value
  insn attr (obj : Value) (name : String) (^err (exc : Value)) : Value
  insn setAttr (obj : Value) (name : String) (val : Value) (^err (exc : Value)) : Unit
  insn add (lhs rhs : Value) (^err (exc : Value)) : Value
  insn sub (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mult (lhs rhs : Value) (^err (exc : Value)) : Value
  insn div (lhs rhs : Value) (^err (exc : Value)) : Value
  insn floorDiv (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mod (lhs rhs : Value) (^err (exc : Value)) : Value
  insn pow (lhs rhs : Value) (^err (exc : Value)) : Value
  insn not_ as "not" (operand : Value) (^err (exc : Value)) : Value
  insn uSub (operand : Value) (^err (exc : Value)) : Value
  insn eq (lhs rhs : Value) (^err (exc : Value)) : Value
  insn notEq (lhs rhs : Value) (^err (exc : Value)) : Value
  insn lt (lhs rhs : Value) (^err (exc : Value)) : Value
  insn ltE (lhs rhs : Value) (^err (exc : Value)) : Value
  insn gt (lhs rhs : Value) (^err (exc : Value)) : Value
  insn gtE (lhs rhs : Value) (^err (exc : Value)) : Value
  insn is_ as "is" (lhs rhs : Value) : Value
  insn isNot (lhs rhs : Value) : Value
  insn in_ as "in" (lhs rhs : Value) (^err (exc : Value)) : Value
  insn notIn (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mkDict (*elems : Value) : Value
  insn mkList (*elems : Value) : Value
  insn mkSet (*elems : Value) : Value
  insn mkTuple (*elems : Value) : Value
  insn getItem (obj key : Value) (^err (exc : Value)) : Value
  insn setItem (obj key val : Value) (^err (exc : Value)) : Unit
  insn getSlice (obj lo hi step : Value) (^err (exc : Value)) : Value
  insn tupleExtend (tup iterable : Value) (^err (exc : Value)) : Value
  insn tupleLen (tup : Value) : Value
  insn dictMerge (callee dict other : Value) (^err (exc : Value)) : Value
  insn dictUpdate (dict other : Value) (^err (exc : Value)) : Value
  insn dictLen (dict : Value) : Value
  insn dictGet (dict key fallback : Value) : Value
  insn dictFirstKey (dict fallback : Value) : Value
  insn dictDiscard (dict key : Value) : Unit
  insn listAppend (list value : Value) : Unit
  insn setAdd (set value : Value) : Unit
  insn dictSet (dict key value : Value) : Unit
  insn getIter (obj : Value) (^err (exc : Value)) : Value
  insn next_ as "next" (iter : Value) (^err (exc : Value)) : Value
  insn isStopIteration (exc : Value) : Bool
  insn fmtValue (val : Value) (^err (exc : Value)) : Value
  insn strConcat (*parts : Value) (^err (exc : Value)) : Value
  insn assert_ as "assert" (cond msg : Value) (^err (exc : Value)) : Unit
  insn unsupported (name : Value) : Value
  insn undef2 (name : String) : Value
  insn isDefined2 (val : Value) : Bool
  insn truthy2 (val : Value) (^err (exc : Value)) : Bool
  insn requireDefined2 (val : Value) (excType msg : String) (^err (exc : Value)) : Value
  insn requireUndefined2 (val : Value) (excType msg : String) (^err (exc : Value)) : Unit
  insn requireAtMost2 (val : Value) (limit : Int) (excType msg : String) (^err (exc : Value)) : Unit
  insn intLit2 (val : Int) : Value
  insn floatLit2 (val : Float64) : Value
  insn strLit2 (val : String) : Value
  insn boolLit2 (val : Bool) : Value
  insn bytesLit2 (val : String) : Value
  insn noneLit2  : Value
  insn call2 (func args kwargs : Value) (^err (exc : Value)) : Value
  insn qualifiedRef2 (moduleName name : String) (^err (exc : Value)) : Value
  insn mkClosure2 (code : Code) (*cells : (Ref Value)) : Value
  insn attr2 (obj : Value) (name : String) (^err (exc : Value)) : Value
  insn setAttr2 (obj : Value) (name : String) (val : Value) (^err (exc : Value)) : Unit
  insn add2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn sub2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mult2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn div2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn floorDiv2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mod2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn pow2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn not_2 as "not2" (operand : Value) (^err (exc : Value)) : Value
  insn uSub2 (operand : Value) (^err (exc : Value)) : Value
  insn eq2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn notEq2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn lt2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn ltE2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn gt2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn gtE2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn is_2 as "is2" (lhs rhs : Value) : Value
  insn isNot2 (lhs rhs : Value) : Value
  insn in_2 as "in2" (lhs rhs : Value) (^err (exc : Value)) : Value
  insn notIn2 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mkDict2 (*elems : Value) : Value
  insn mkList2 (*elems : Value) : Value
  insn mkSet2 (*elems : Value) : Value
  insn mkTuple2 (*elems : Value) : Value
  insn getItem2 (obj key : Value) (^err (exc : Value)) : Value
  insn setItem2 (obj key val : Value) (^err (exc : Value)) : Unit
  insn getSlice2 (obj lo hi step : Value) (^err (exc : Value)) : Value
  insn tupleExtend2 (tup iterable : Value) (^err (exc : Value)) : Value
  insn tupleLen2 (tup : Value) : Value
  insn dictMerge2 (callee dict other : Value) (^err (exc : Value)) : Value
  insn dictUpdate2 (dict other : Value) (^err (exc : Value)) : Value
  insn dictLen2 (dict : Value) : Value
  insn dictGet2 (dict key fallback : Value) : Value
  insn dictFirstKey2 (dict fallback : Value) : Value
  insn dictDiscard2 (dict key : Value) : Unit
  insn listAppend2 (list value : Value) : Unit
  insn setAdd2 (set value : Value) : Unit
  insn dictSet2 (dict key value : Value) : Unit
  insn getIter2 (obj : Value) (^err (exc : Value)) : Value
  insn next_2 as "next2" (iter : Value) (^err (exc : Value)) : Value
  insn isStopIteration2 (exc : Value) : Bool
  insn fmtValue2 (val : Value) (^err (exc : Value)) : Value
  insn strConcat2 (*parts : Value) (^err (exc : Value)) : Value
  insn undef3 (name : String) : Value
  insn isDefined3 (val : Value) : Bool
  insn truthy3 (val : Value) (^err (exc : Value)) : Bool
  insn requireDefined3 (val : Value) (excType msg : String) (^err (exc : Value)) : Value
  insn requireUndefined3 (val : Value) (excType msg : String) (^err (exc : Value)) : Unit
  insn requireAtMost3 (val : Value) (limit : Int) (excType msg : String) (^err (exc : Value)) : Unit
  insn intLit3 (val : Int) : Value
  insn floatLit3 (val : Float64) : Value
  insn strLit3 (val : String) : Value
  insn boolLit3 (val : Bool) : Value
  insn bytesLit3 (val : String) : Value
  insn noneLit3  : Value
  insn call3 (func args kwargs : Value) (^err (exc : Value)) : Value
  insn qualifiedRef3 (moduleName name : String) (^err (exc : Value)) : Value
  insn mkClosure3 (code : Code) (*cells : (Ref Value)) : Value
  insn attr3 (obj : Value) (name : String) (^err (exc : Value)) : Value
  insn setAttr3 (obj : Value) (name : String) (val : Value) (^err (exc : Value)) : Unit
  insn add3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn sub3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mult3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn div3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn floorDiv3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mod3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn pow3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn not_3 as "not3" (operand : Value) (^err (exc : Value)) : Value
  insn uSub3 (operand : Value) (^err (exc : Value)) : Value
  insn eq3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn notEq3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn lt3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn ltE3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn gt3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn gtE3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn is_3 as "is3" (lhs rhs : Value) : Value
  insn isNot3 (lhs rhs : Value) : Value
  insn in_3 as "in3" (lhs rhs : Value) (^err (exc : Value)) : Value
  insn notIn3 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mkDict3 (*elems : Value) : Value
  insn mkList3 (*elems : Value) : Value
  insn mkSet3 (*elems : Value) : Value
  insn mkTuple3 (*elems : Value) : Value
  insn getItem3 (obj key : Value) (^err (exc : Value)) : Value
  insn setItem3 (obj key val : Value) (^err (exc : Value)) : Unit
  insn getSlice3 (obj lo hi step : Value) (^err (exc : Value)) : Value
  insn tupleExtend3 (tup iterable : Value) (^err (exc : Value)) : Value
  insn tupleLen3 (tup : Value) : Value
  insn dictMerge3 (callee dict other : Value) (^err (exc : Value)) : Value
  insn dictUpdate3 (dict other : Value) (^err (exc : Value)) : Value
  insn dictLen3 (dict : Value) : Value
  insn dictGet3 (dict key fallback : Value) : Value
  insn dictFirstKey3 (dict fallback : Value) : Value
  insn dictDiscard3 (dict key : Value) : Unit
  insn listAppend3 (list value : Value) : Unit
  insn setAdd3 (set value : Value) : Unit
  insn dictSet3 (dict key value : Value) : Unit
  insn getIter3 (obj : Value) (^err (exc : Value)) : Value
  insn next_3 as "next3" (iter : Value) (^err (exc : Value)) : Value
  insn isStopIteration3 (exc : Value) : Bool
  insn fmtValue3 (val : Value) (^err (exc : Value)) : Value
  insn strConcat3 (*parts : Value) (^err (exc : Value)) : Value
  insn assert_3 as "assert3" (cond msg : Value) (^err (exc : Value)) : Unit
  insn unsupported3 (name : Value) : Value
  insn undef4 (name : String) : Value
  insn isDefined4 (val : Value) : Bool
  insn truthy4 (val : Value) (^err (exc : Value)) : Bool
  insn requireDefined4 (val : Value) (excType msg : String) (^err (exc : Value)) : Value
  insn requireUndefined4 (val : Value) (excType msg : String) (^err (exc : Value)) : Unit
  insn requireAtMost4 (val : Value) (limit : Int) (excType msg : String) (^err (exc : Value)) : Unit
  insn intLit4 (val : Int) : Value
  insn floatLit4 (val : Float64) : Value
  insn strLit4 (val : String) : Value
  insn boolLit4 (val : Bool) : Value
  insn bytesLit4 (val : String) : Value
  insn noneLit4  : Value
  insn call4 (func args kwargs : Value) (^err (exc : Value)) : Value
  insn qualifiedRef4 (moduleName name : String) (^err (exc : Value)) : Value
  insn mkClosure4 (code : Code) (*cells : (Ref Value)) : Value
  insn attr4 (obj : Value) (name : String) (^err (exc : Value)) : Value
  insn setAttr4 (obj : Value) (name : String) (val : Value) (^err (exc : Value)) : Unit
  insn add4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn sub4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mult4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn div4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn floorDiv4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mod4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn pow4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn not_4 as "not4" (operand : Value) (^err (exc : Value)) : Value
  insn uSub4 (operand : Value) (^err (exc : Value)) : Value
  insn eq4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn notEq4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn lt4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn ltE4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn gt4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn gtE4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn is_4 as "is4" (lhs rhs : Value) : Value
  insn isNot4 (lhs rhs : Value) : Value
  insn in_4 as "in4" (lhs rhs : Value) (^err (exc : Value)) : Value
  insn notIn4 (lhs rhs : Value) (^err (exc : Value)) : Value
  insn mkDict4 (*elems : Value) : Value
  insn mkList4 (*elems : Value) : Value
  insn mkSet4 (*elems : Value) : Value
  insn mkTuple4 (*elems : Value) : Value
  insn getItem4 (obj key : Value) (^err (exc : Value)) : Value
  insn setItem4 (obj key val : Value) (^err (exc : Value)) : Unit
  insn getSlice4 (obj lo hi step : Value) (^err (exc : Value)) : Value
  insn tupleExtend4 (tup iterable : Value) (^err (exc : Value)) : Value
  insn tupleLen4 (tup : Value) : Value
  insn dictMerge4 (callee dict other : Value) (^err (exc : Value)) : Value
  insn dictUpdate4 (dict other : Value) (^err (exc : Value)) : Value
  insn dictLen4 (dict : Value) : Value
  insn dictGet4 (dict key fallback : Value) : Value
  insn dictFirstKey4 (dict fallback : Value) : Value
  insn dictDiscard4 (dict key : Value) : Unit
  insn listAppend4 (list value : Value) : Unit
  insn setAdd4 (set value : Value) : Unit
  insn dictSet4 (dict key value : Value) : Unit
  insn getIter4 (obj : Value) (^err (exc : Value)) : Value
  insn next_4 as "next4" (iter : Value) (^err (exc : Value)) : Value
  insn isStopIteration4 (exc : Value) : Bool
  insn fmtValue4 (val : Value) (^err (exc : Value)) : Value
  insn strConcat4 (*parts : Value) (^err (exc : Value)) : Value
  end scale

/-! ## What it generates -/

-- `mem_env`'s list is `names`.  The kernel compares them: the unifier, like `simp`, recurses
-- once per element.
example {n : Name} : n ∈ Scale.env ↔ n ∈ Scale.names :=
  Scale.mem_env.trans (Iff.of_eq (congrArg (n ∈ ·) (by decide +kernel)))
#guard (Scale.strConcat2.sig (e := Scale.env)).variadic.map (·.name) == some "parts"
#guard (Scale.next_2.sig (e := Scale.env)).succs.map (·.name) == #["err"]
#guard (Scale.strConcat4.sig (e := Scale.env)).variadic.map (·.name) == some "parts"

section
variable {e : Env _root_.Unit} [Scale.env ⊑ e]
example : InsnRef e Scale.add2.sig := Scale.add2
example : InsnRef e Scale.strConcat4.sig := Scale.strConcat4
example : InsnRef e Base.refNew.sig := Base.refNew
end

end Strata.Mantle.DSLScaleTest
