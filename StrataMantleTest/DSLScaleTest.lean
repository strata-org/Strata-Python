/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.Refine
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
`mem_env` at 217.  This block is past all four.  A run of instructions is now split into
stages of 64, so a reference to instruction `j` reduces a short literal; `Wide` below is past
the 500 instructions that used to stop a block.

The block takes about 20 s, most of it the DSL's elaboration and the kernel's.  `Wide` takes
about 40 s, most of it its instructions' signatures and references.  Its freshness checks
grow with each stage only: a stage adds its own names to the set of every name before it.
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

/-! ## A block past a stage's size

`Wide` declares 260 types, then 520 instructions over them.  Runs this long are split into
stages of 64, so each reference reduces a short literal; a run of either alone used to stop
the block, at about 250 types or 500 instructions. -/

/-- 260 types and 520 instructions over them. -/
public environment Wide extends Base where
  namespace wide
  type T0
  type T1
  type T2
  type T3
  type T4
  type T5
  type T6
  type T7
  type T8
  type T9
  type T10
  type T11
  type T12
  type T13
  type T14
  type T15
  type T16
  type T17
  type T18
  type T19
  type T20
  type T21
  type T22
  type T23
  type T24
  type T25
  type T26
  type T27
  type T28
  type T29
  type T30
  type T31
  type T32
  type T33
  type T34
  type T35
  type T36
  type T37
  type T38
  type T39
  type T40
  type T41
  type T42
  type T43
  type T44
  type T45
  type T46
  type T47
  type T48
  type T49
  type T50
  type T51
  type T52
  type T53
  type T54
  type T55
  type T56
  type T57
  type T58
  type T59
  type T60
  type T61
  type T62
  type T63
  type T64
  type T65
  type T66
  type T67
  type T68
  type T69
  type T70
  type T71
  type T72
  type T73
  type T74
  type T75
  type T76
  type T77
  type T78
  type T79
  type T80
  type T81
  type T82
  type T83
  type T84
  type T85
  type T86
  type T87
  type T88
  type T89
  type T90
  type T91
  type T92
  type T93
  type T94
  type T95
  type T96
  type T97
  type T98
  type T99
  type T100
  type T101
  type T102
  type T103
  type T104
  type T105
  type T106
  type T107
  type T108
  type T109
  type T110
  type T111
  type T112
  type T113
  type T114
  type T115
  type T116
  type T117
  type T118
  type T119
  type T120
  type T121
  type T122
  type T123
  type T124
  type T125
  type T126
  type T127
  type T128
  type T129
  type T130
  type T131
  type T132
  type T133
  type T134
  type T135
  type T136
  type T137
  type T138
  type T139
  type T140
  type T141
  type T142
  type T143
  type T144
  type T145
  type T146
  type T147
  type T148
  type T149
  type T150
  type T151
  type T152
  type T153
  type T154
  type T155
  type T156
  type T157
  type T158
  type T159
  type T160
  type T161
  type T162
  type T163
  type T164
  type T165
  type T166
  type T167
  type T168
  type T169
  type T170
  type T171
  type T172
  type T173
  type T174
  type T175
  type T176
  type T177
  type T178
  type T179
  type T180
  type T181
  type T182
  type T183
  type T184
  type T185
  type T186
  type T187
  type T188
  type T189
  type T190
  type T191
  type T192
  type T193
  type T194
  type T195
  type T196
  type T197
  type T198
  type T199
  type T200
  type T201
  type T202
  type T203
  type T204
  type T205
  type T206
  type T207
  type T208
  type T209
  type T210
  type T211
  type T212
  type T213
  type T214
  type T215
  type T216
  type T217
  type T218
  type T219
  type T220
  type T221
  type T222
  type T223
  type T224
  type T225
  type T226
  type T227
  type T228
  type T229
  type T230
  type T231
  type T232
  type T233
  type T234
  type T235
  type T236
  type T237
  type T238
  type T239
  type T240
  type T241
  type T242
  type T243
  type T244
  type T245
  type T246
  type T247
  type T248
  type T249
  type T250
  type T251
  type T252
  type T253
  type T254
  type T255
  type T256
  type T257
  type T258
  type T259
  insn w0 (x : T0) (y : T0) : T1
  insn w1 (x : T1) (y : T7) : T2
  insn w2 (x : T2) (y : T14) : T3
  insn w3 (x : T3) (y : T21) : T4
  insn w4 (x : T4) (y : T28) : T5
  insn w5 (x : T5) (y : T35) : T6
  insn w6 (x : T6) (y : T42) : T7
  insn w7 (x : T7) (y : T49) : T8
  insn w8 (x : T8) (y : T56) : T9
  insn w9 (x : T9) (y : T63) : T10
  insn w10 (x : T10) (y : T70) : T11
  insn w11 (x : T11) (y : T77) : T12
  insn w12 (x : T12) (y : T84) : T13
  insn w13 (x : T13) (y : T91) : T14
  insn w14 (x : T14) (y : T98) : T15
  insn w15 (x : T15) (y : T105) : T16
  insn w16 (x : T16) (y : T112) : T17
  insn w17 (x : T17) (y : T119) : T18
  insn w18 (x : T18) (y : T126) : T19
  insn w19 (x : T19) (y : T133) : T20
  insn w20 (x : T20) (y : T140) : T21
  insn w21 (x : T21) (y : T147) : T22
  insn w22 (x : T22) (y : T154) : T23
  insn w23 (x : T23) (y : T161) : T24
  insn w24 (x : T24) (y : T168) : T25
  insn w25 (x : T25) (y : T175) : T26
  insn w26 (x : T26) (y : T182) : T27
  insn w27 (x : T27) (y : T189) : T28
  insn w28 (x : T28) (y : T196) : T29
  insn w29 (x : T29) (y : T203) : T30
  insn w30 (x : T30) (y : T210) : T31
  insn w31 (x : T31) (y : T217) : T32
  insn w32 (x : T32) (y : T224) : T33
  insn w33 (x : T33) (y : T231) : T34
  insn w34 (x : T34) (y : T238) : T35
  insn w35 (x : T35) (y : T245) : T36
  insn w36 (x : T36) (y : T252) : T37
  insn w37 (x : T37) (y : T259) : T38
  insn w38 (x : T38) (y : T6) : T39
  insn w39 (x : T39) (y : T13) : T40
  insn w40 (x : T40) (y : T20) : T41
  insn w41 (x : T41) (y : T27) : T42
  insn w42 (x : T42) (y : T34) : T43
  insn w43 (x : T43) (y : T41) : T44
  insn w44 (x : T44) (y : T48) : T45
  insn w45 (x : T45) (y : T55) : T46
  insn w46 (x : T46) (y : T62) : T47
  insn w47 (x : T47) (y : T69) : T48
  insn w48 (x : T48) (y : T76) : T49
  insn w49 (x : T49) (y : T83) : T50
  insn w50 (x : T50) (y : T90) : T51
  insn w51 (x : T51) (y : T97) : T52
  insn w52 (x : T52) (y : T104) : T53
  insn w53 (x : T53) (y : T111) : T54
  insn w54 (x : T54) (y : T118) : T55
  insn w55 (x : T55) (y : T125) : T56
  insn w56 (x : T56) (y : T132) : T57
  insn w57 (x : T57) (y : T139) : T58
  insn w58 (x : T58) (y : T146) : T59
  insn w59 (x : T59) (y : T153) : T60
  insn w60 (x : T60) (y : T160) : T61
  insn w61 (x : T61) (y : T167) : T62
  insn w62 (x : T62) (y : T174) : T63
  insn w63 (x : T63) (y : T181) : T64
  insn w64 (x : T64) (y : T188) : T65
  insn w65 (x : T65) (y : T195) : T66
  insn w66 (x : T66) (y : T202) : T67
  insn w67 (x : T67) (y : T209) : T68
  insn w68 (x : T68) (y : T216) : T69
  insn w69 (x : T69) (y : T223) : T70
  insn w70 (x : T70) (y : T230) : T71
  insn w71 (x : T71) (y : T237) : T72
  insn w72 (x : T72) (y : T244) : T73
  insn w73 (x : T73) (y : T251) : T74
  insn w74 (x : T74) (y : T258) : T75
  insn w75 (x : T75) (y : T5) : T76
  insn w76 (x : T76) (y : T12) : T77
  insn w77 (x : T77) (y : T19) : T78
  insn w78 (x : T78) (y : T26) : T79
  insn w79 (x : T79) (y : T33) : T80
  insn w80 (x : T80) (y : T40) : T81
  insn w81 (x : T81) (y : T47) : T82
  insn w82 (x : T82) (y : T54) : T83
  insn w83 (x : T83) (y : T61) : T84
  insn w84 (x : T84) (y : T68) : T85
  insn w85 (x : T85) (y : T75) : T86
  insn w86 (x : T86) (y : T82) : T87
  insn w87 (x : T87) (y : T89) : T88
  insn w88 (x : T88) (y : T96) : T89
  insn w89 (x : T89) (y : T103) : T90
  insn w90 (x : T90) (y : T110) : T91
  insn w91 (x : T91) (y : T117) : T92
  insn w92 (x : T92) (y : T124) : T93
  insn w93 (x : T93) (y : T131) : T94
  insn w94 (x : T94) (y : T138) : T95
  insn w95 (x : T95) (y : T145) : T96
  insn w96 (x : T96) (y : T152) : T97
  insn w97 (x : T97) (y : T159) : T98
  insn w98 (x : T98) (y : T166) : T99
  insn w99 (x : T99) (y : T173) : T100
  insn w100 (x : T100) (y : T180) : T101
  insn w101 (x : T101) (y : T187) : T102
  insn w102 (x : T102) (y : T194) : T103
  insn w103 (x : T103) (y : T201) : T104
  insn w104 (x : T104) (y : T208) : T105
  insn w105 (x : T105) (y : T215) : T106
  insn w106 (x : T106) (y : T222) : T107
  insn w107 (x : T107) (y : T229) : T108
  insn w108 (x : T108) (y : T236) : T109
  insn w109 (x : T109) (y : T243) : T110
  insn w110 (x : T110) (y : T250) : T111
  insn w111 (x : T111) (y : T257) : T112
  insn w112 (x : T112) (y : T4) : T113
  insn w113 (x : T113) (y : T11) : T114
  insn w114 (x : T114) (y : T18) : T115
  insn w115 (x : T115) (y : T25) : T116
  insn w116 (x : T116) (y : T32) : T117
  insn w117 (x : T117) (y : T39) : T118
  insn w118 (x : T118) (y : T46) : T119
  insn w119 (x : T119) (y : T53) : T120
  insn w120 (x : T120) (y : T60) : T121
  insn w121 (x : T121) (y : T67) : T122
  insn w122 (x : T122) (y : T74) : T123
  insn w123 (x : T123) (y : T81) : T124
  insn w124 (x : T124) (y : T88) : T125
  insn w125 (x : T125) (y : T95) : T126
  insn w126 (x : T126) (y : T102) : T127
  insn w127 (x : T127) (y : T109) : T128
  insn w128 (x : T128) (y : T116) : T129
  insn w129 (x : T129) (y : T123) : T130
  insn w130 (x : T130) (y : T130) : T131
  insn w131 (x : T131) (y : T137) : T132
  insn w132 (x : T132) (y : T144) : T133
  insn w133 (x : T133) (y : T151) : T134
  insn w134 (x : T134) (y : T158) : T135
  insn w135 (x : T135) (y : T165) : T136
  insn w136 (x : T136) (y : T172) : T137
  insn w137 (x : T137) (y : T179) : T138
  insn w138 (x : T138) (y : T186) : T139
  insn w139 (x : T139) (y : T193) : T140
  insn w140 (x : T140) (y : T200) : T141
  insn w141 (x : T141) (y : T207) : T142
  insn w142 (x : T142) (y : T214) : T143
  insn w143 (x : T143) (y : T221) : T144
  insn w144 (x : T144) (y : T228) : T145
  insn w145 (x : T145) (y : T235) : T146
  insn w146 (x : T146) (y : T242) : T147
  insn w147 (x : T147) (y : T249) : T148
  insn w148 (x : T148) (y : T256) : T149
  insn w149 (x : T149) (y : T3) : T150
  insn w150 (x : T150) (y : T10) : T151
  insn w151 (x : T151) (y : T17) : T152
  insn w152 (x : T152) (y : T24) : T153
  insn w153 (x : T153) (y : T31) : T154
  insn w154 (x : T154) (y : T38) : T155
  insn w155 (x : T155) (y : T45) : T156
  insn w156 (x : T156) (y : T52) : T157
  insn w157 (x : T157) (y : T59) : T158
  insn w158 (x : T158) (y : T66) : T159
  insn w159 (x : T159) (y : T73) : T160
  insn w160 (x : T160) (y : T80) : T161
  insn w161 (x : T161) (y : T87) : T162
  insn w162 (x : T162) (y : T94) : T163
  insn w163 (x : T163) (y : T101) : T164
  insn w164 (x : T164) (y : T108) : T165
  insn w165 (x : T165) (y : T115) : T166
  insn w166 (x : T166) (y : T122) : T167
  insn w167 (x : T167) (y : T129) : T168
  insn w168 (x : T168) (y : T136) : T169
  insn w169 (x : T169) (y : T143) : T170
  insn w170 (x : T170) (y : T150) : T171
  insn w171 (x : T171) (y : T157) : T172
  insn w172 (x : T172) (y : T164) : T173
  insn w173 (x : T173) (y : T171) : T174
  insn w174 (x : T174) (y : T178) : T175
  insn w175 (x : T175) (y : T185) : T176
  insn w176 (x : T176) (y : T192) : T177
  insn w177 (x : T177) (y : T199) : T178
  insn w178 (x : T178) (y : T206) : T179
  insn w179 (x : T179) (y : T213) : T180
  insn w180 (x : T180) (y : T220) : T181
  insn w181 (x : T181) (y : T227) : T182
  insn w182 (x : T182) (y : T234) : T183
  insn w183 (x : T183) (y : T241) : T184
  insn w184 (x : T184) (y : T248) : T185
  insn w185 (x : T185) (y : T255) : T186
  insn w186 (x : T186) (y : T2) : T187
  insn w187 (x : T187) (y : T9) : T188
  insn w188 (x : T188) (y : T16) : T189
  insn w189 (x : T189) (y : T23) : T190
  insn w190 (x : T190) (y : T30) : T191
  insn w191 (x : T191) (y : T37) : T192
  insn w192 (x : T192) (y : T44) : T193
  insn w193 (x : T193) (y : T51) : T194
  insn w194 (x : T194) (y : T58) : T195
  insn w195 (x : T195) (y : T65) : T196
  insn w196 (x : T196) (y : T72) : T197
  insn w197 (x : T197) (y : T79) : T198
  insn w198 (x : T198) (y : T86) : T199
  insn w199 (x : T199) (y : T93) : T200
  insn w200 (x : T200) (y : T100) : T201
  insn w201 (x : T201) (y : T107) : T202
  insn w202 (x : T202) (y : T114) : T203
  insn w203 (x : T203) (y : T121) : T204
  insn w204 (x : T204) (y : T128) : T205
  insn w205 (x : T205) (y : T135) : T206
  insn w206 (x : T206) (y : T142) : T207
  insn w207 (x : T207) (y : T149) : T208
  insn w208 (x : T208) (y : T156) : T209
  insn w209 (x : T209) (y : T163) : T210
  insn w210 (x : T210) (y : T170) : T211
  insn w211 (x : T211) (y : T177) : T212
  insn w212 (x : T212) (y : T184) : T213
  insn w213 (x : T213) (y : T191) : T214
  insn w214 (x : T214) (y : T198) : T215
  insn w215 (x : T215) (y : T205) : T216
  insn w216 (x : T216) (y : T212) : T217
  insn w217 (x : T217) (y : T219) : T218
  insn w218 (x : T218) (y : T226) : T219
  insn w219 (x : T219) (y : T233) : T220
  insn w220 (x : T220) (y : T240) : T221
  insn w221 (x : T221) (y : T247) : T222
  insn w222 (x : T222) (y : T254) : T223
  insn w223 (x : T223) (y : T1) : T224
  insn w224 (x : T224) (y : T8) : T225
  insn w225 (x : T225) (y : T15) : T226
  insn w226 (x : T226) (y : T22) : T227
  insn w227 (x : T227) (y : T29) : T228
  insn w228 (x : T228) (y : T36) : T229
  insn w229 (x : T229) (y : T43) : T230
  insn w230 (x : T230) (y : T50) : T231
  insn w231 (x : T231) (y : T57) : T232
  insn w232 (x : T232) (y : T64) : T233
  insn w233 (x : T233) (y : T71) : T234
  insn w234 (x : T234) (y : T78) : T235
  insn w235 (x : T235) (y : T85) : T236
  insn w236 (x : T236) (y : T92) : T237
  insn w237 (x : T237) (y : T99) : T238
  insn w238 (x : T238) (y : T106) : T239
  insn w239 (x : T239) (y : T113) : T240
  insn w240 (x : T240) (y : T120) : T241
  insn w241 (x : T241) (y : T127) : T242
  insn w242 (x : T242) (y : T134) : T243
  insn w243 (x : T243) (y : T141) : T244
  insn w244 (x : T244) (y : T148) : T245
  insn w245 (x : T245) (y : T155) : T246
  insn w246 (x : T246) (y : T162) : T247
  insn w247 (x : T247) (y : T169) : T248
  insn w248 (x : T248) (y : T176) : T249
  insn w249 (x : T249) (y : T183) : T250
  insn w250 (x : T250) (y : T190) : T251
  insn w251 (x : T251) (y : T197) : T252
  insn w252 (x : T252) (y : T204) : T253
  insn w253 (x : T253) (y : T211) : T254
  insn w254 (x : T254) (y : T218) : T255
  insn w255 (x : T255) (y : T225) : T256
  insn w256 (x : T256) (y : T232) : T257
  insn w257 (x : T257) (y : T239) : T258
  insn w258 (x : T258) (y : T246) : T259
  insn w259 (x : T259) (y : T253) : T0
  insn w260 (x : T0) (y : T0) : T1
  insn w261 (x : T1) (y : T7) : T2
  insn w262 (x : T2) (y : T14) : T3
  insn w263 (x : T3) (y : T21) : T4
  insn w264 (x : T4) (y : T28) : T5
  insn w265 (x : T5) (y : T35) : T6
  insn w266 (x : T6) (y : T42) : T7
  insn w267 (x : T7) (y : T49) : T8
  insn w268 (x : T8) (y : T56) : T9
  insn w269 (x : T9) (y : T63) : T10
  insn w270 (x : T10) (y : T70) : T11
  insn w271 (x : T11) (y : T77) : T12
  insn w272 (x : T12) (y : T84) : T13
  insn w273 (x : T13) (y : T91) : T14
  insn w274 (x : T14) (y : T98) : T15
  insn w275 (x : T15) (y : T105) : T16
  insn w276 (x : T16) (y : T112) : T17
  insn w277 (x : T17) (y : T119) : T18
  insn w278 (x : T18) (y : T126) : T19
  insn w279 (x : T19) (y : T133) : T20
  insn w280 (x : T20) (y : T140) : T21
  insn w281 (x : T21) (y : T147) : T22
  insn w282 (x : T22) (y : T154) : T23
  insn w283 (x : T23) (y : T161) : T24
  insn w284 (x : T24) (y : T168) : T25
  insn w285 (x : T25) (y : T175) : T26
  insn w286 (x : T26) (y : T182) : T27
  insn w287 (x : T27) (y : T189) : T28
  insn w288 (x : T28) (y : T196) : T29
  insn w289 (x : T29) (y : T203) : T30
  insn w290 (x : T30) (y : T210) : T31
  insn w291 (x : T31) (y : T217) : T32
  insn w292 (x : T32) (y : T224) : T33
  insn w293 (x : T33) (y : T231) : T34
  insn w294 (x : T34) (y : T238) : T35
  insn w295 (x : T35) (y : T245) : T36
  insn w296 (x : T36) (y : T252) : T37
  insn w297 (x : T37) (y : T259) : T38
  insn w298 (x : T38) (y : T6) : T39
  insn w299 (x : T39) (y : T13) : T40
  insn w300 (x : T40) (y : T20) : T41
  insn w301 (x : T41) (y : T27) : T42
  insn w302 (x : T42) (y : T34) : T43
  insn w303 (x : T43) (y : T41) : T44
  insn w304 (x : T44) (y : T48) : T45
  insn w305 (x : T45) (y : T55) : T46
  insn w306 (x : T46) (y : T62) : T47
  insn w307 (x : T47) (y : T69) : T48
  insn w308 (x : T48) (y : T76) : T49
  insn w309 (x : T49) (y : T83) : T50
  insn w310 (x : T50) (y : T90) : T51
  insn w311 (x : T51) (y : T97) : T52
  insn w312 (x : T52) (y : T104) : T53
  insn w313 (x : T53) (y : T111) : T54
  insn w314 (x : T54) (y : T118) : T55
  insn w315 (x : T55) (y : T125) : T56
  insn w316 (x : T56) (y : T132) : T57
  insn w317 (x : T57) (y : T139) : T58
  insn w318 (x : T58) (y : T146) : T59
  insn w319 (x : T59) (y : T153) : T60
  insn w320 (x : T60) (y : T160) : T61
  insn w321 (x : T61) (y : T167) : T62
  insn w322 (x : T62) (y : T174) : T63
  insn w323 (x : T63) (y : T181) : T64
  insn w324 (x : T64) (y : T188) : T65
  insn w325 (x : T65) (y : T195) : T66
  insn w326 (x : T66) (y : T202) : T67
  insn w327 (x : T67) (y : T209) : T68
  insn w328 (x : T68) (y : T216) : T69
  insn w329 (x : T69) (y : T223) : T70
  insn w330 (x : T70) (y : T230) : T71
  insn w331 (x : T71) (y : T237) : T72
  insn w332 (x : T72) (y : T244) : T73
  insn w333 (x : T73) (y : T251) : T74
  insn w334 (x : T74) (y : T258) : T75
  insn w335 (x : T75) (y : T5) : T76
  insn w336 (x : T76) (y : T12) : T77
  insn w337 (x : T77) (y : T19) : T78
  insn w338 (x : T78) (y : T26) : T79
  insn w339 (x : T79) (y : T33) : T80
  insn w340 (x : T80) (y : T40) : T81
  insn w341 (x : T81) (y : T47) : T82
  insn w342 (x : T82) (y : T54) : T83
  insn w343 (x : T83) (y : T61) : T84
  insn w344 (x : T84) (y : T68) : T85
  insn w345 (x : T85) (y : T75) : T86
  insn w346 (x : T86) (y : T82) : T87
  insn w347 (x : T87) (y : T89) : T88
  insn w348 (x : T88) (y : T96) : T89
  insn w349 (x : T89) (y : T103) : T90
  insn w350 (x : T90) (y : T110) : T91
  insn w351 (x : T91) (y : T117) : T92
  insn w352 (x : T92) (y : T124) : T93
  insn w353 (x : T93) (y : T131) : T94
  insn w354 (x : T94) (y : T138) : T95
  insn w355 (x : T95) (y : T145) : T96
  insn w356 (x : T96) (y : T152) : T97
  insn w357 (x : T97) (y : T159) : T98
  insn w358 (x : T98) (y : T166) : T99
  insn w359 (x : T99) (y : T173) : T100
  insn w360 (x : T100) (y : T180) : T101
  insn w361 (x : T101) (y : T187) : T102
  insn w362 (x : T102) (y : T194) : T103
  insn w363 (x : T103) (y : T201) : T104
  insn w364 (x : T104) (y : T208) : T105
  insn w365 (x : T105) (y : T215) : T106
  insn w366 (x : T106) (y : T222) : T107
  insn w367 (x : T107) (y : T229) : T108
  insn w368 (x : T108) (y : T236) : T109
  insn w369 (x : T109) (y : T243) : T110
  insn w370 (x : T110) (y : T250) : T111
  insn w371 (x : T111) (y : T257) : T112
  insn w372 (x : T112) (y : T4) : T113
  insn w373 (x : T113) (y : T11) : T114
  insn w374 (x : T114) (y : T18) : T115
  insn w375 (x : T115) (y : T25) : T116
  insn w376 (x : T116) (y : T32) : T117
  insn w377 (x : T117) (y : T39) : T118
  insn w378 (x : T118) (y : T46) : T119
  insn w379 (x : T119) (y : T53) : T120
  insn w380 (x : T120) (y : T60) : T121
  insn w381 (x : T121) (y : T67) : T122
  insn w382 (x : T122) (y : T74) : T123
  insn w383 (x : T123) (y : T81) : T124
  insn w384 (x : T124) (y : T88) : T125
  insn w385 (x : T125) (y : T95) : T126
  insn w386 (x : T126) (y : T102) : T127
  insn w387 (x : T127) (y : T109) : T128
  insn w388 (x : T128) (y : T116) : T129
  insn w389 (x : T129) (y : T123) : T130
  insn w390 (x : T130) (y : T130) : T131
  insn w391 (x : T131) (y : T137) : T132
  insn w392 (x : T132) (y : T144) : T133
  insn w393 (x : T133) (y : T151) : T134
  insn w394 (x : T134) (y : T158) : T135
  insn w395 (x : T135) (y : T165) : T136
  insn w396 (x : T136) (y : T172) : T137
  insn w397 (x : T137) (y : T179) : T138
  insn w398 (x : T138) (y : T186) : T139
  insn w399 (x : T139) (y : T193) : T140
  insn w400 (x : T140) (y : T200) : T141
  insn w401 (x : T141) (y : T207) : T142
  insn w402 (x : T142) (y : T214) : T143
  insn w403 (x : T143) (y : T221) : T144
  insn w404 (x : T144) (y : T228) : T145
  insn w405 (x : T145) (y : T235) : T146
  insn w406 (x : T146) (y : T242) : T147
  insn w407 (x : T147) (y : T249) : T148
  insn w408 (x : T148) (y : T256) : T149
  insn w409 (x : T149) (y : T3) : T150
  insn w410 (x : T150) (y : T10) : T151
  insn w411 (x : T151) (y : T17) : T152
  insn w412 (x : T152) (y : T24) : T153
  insn w413 (x : T153) (y : T31) : T154
  insn w414 (x : T154) (y : T38) : T155
  insn w415 (x : T155) (y : T45) : T156
  insn w416 (x : T156) (y : T52) : T157
  insn w417 (x : T157) (y : T59) : T158
  insn w418 (x : T158) (y : T66) : T159
  insn w419 (x : T159) (y : T73) : T160
  insn w420 (x : T160) (y : T80) : T161
  insn w421 (x : T161) (y : T87) : T162
  insn w422 (x : T162) (y : T94) : T163
  insn w423 (x : T163) (y : T101) : T164
  insn w424 (x : T164) (y : T108) : T165
  insn w425 (x : T165) (y : T115) : T166
  insn w426 (x : T166) (y : T122) : T167
  insn w427 (x : T167) (y : T129) : T168
  insn w428 (x : T168) (y : T136) : T169
  insn w429 (x : T169) (y : T143) : T170
  insn w430 (x : T170) (y : T150) : T171
  insn w431 (x : T171) (y : T157) : T172
  insn w432 (x : T172) (y : T164) : T173
  insn w433 (x : T173) (y : T171) : T174
  insn w434 (x : T174) (y : T178) : T175
  insn w435 (x : T175) (y : T185) : T176
  insn w436 (x : T176) (y : T192) : T177
  insn w437 (x : T177) (y : T199) : T178
  insn w438 (x : T178) (y : T206) : T179
  insn w439 (x : T179) (y : T213) : T180
  insn w440 (x : T180) (y : T220) : T181
  insn w441 (x : T181) (y : T227) : T182
  insn w442 (x : T182) (y : T234) : T183
  insn w443 (x : T183) (y : T241) : T184
  insn w444 (x : T184) (y : T248) : T185
  insn w445 (x : T185) (y : T255) : T186
  insn w446 (x : T186) (y : T2) : T187
  insn w447 (x : T187) (y : T9) : T188
  insn w448 (x : T188) (y : T16) : T189
  insn w449 (x : T189) (y : T23) : T190
  insn w450 (x : T190) (y : T30) : T191
  insn w451 (x : T191) (y : T37) : T192
  insn w452 (x : T192) (y : T44) : T193
  insn w453 (x : T193) (y : T51) : T194
  insn w454 (x : T194) (y : T58) : T195
  insn w455 (x : T195) (y : T65) : T196
  insn w456 (x : T196) (y : T72) : T197
  insn w457 (x : T197) (y : T79) : T198
  insn w458 (x : T198) (y : T86) : T199
  insn w459 (x : T199) (y : T93) : T200
  insn w460 (x : T200) (y : T100) : T201
  insn w461 (x : T201) (y : T107) : T202
  insn w462 (x : T202) (y : T114) : T203
  insn w463 (x : T203) (y : T121) : T204
  insn w464 (x : T204) (y : T128) : T205
  insn w465 (x : T205) (y : T135) : T206
  insn w466 (x : T206) (y : T142) : T207
  insn w467 (x : T207) (y : T149) : T208
  insn w468 (x : T208) (y : T156) : T209
  insn w469 (x : T209) (y : T163) : T210
  insn w470 (x : T210) (y : T170) : T211
  insn w471 (x : T211) (y : T177) : T212
  insn w472 (x : T212) (y : T184) : T213
  insn w473 (x : T213) (y : T191) : T214
  insn w474 (x : T214) (y : T198) : T215
  insn w475 (x : T215) (y : T205) : T216
  insn w476 (x : T216) (y : T212) : T217
  insn w477 (x : T217) (y : T219) : T218
  insn w478 (x : T218) (y : T226) : T219
  insn w479 (x : T219) (y : T233) : T220
  insn w480 (x : T220) (y : T240) : T221
  insn w481 (x : T221) (y : T247) : T222
  insn w482 (x : T222) (y : T254) : T223
  insn w483 (x : T223) (y : T1) : T224
  insn w484 (x : T224) (y : T8) : T225
  insn w485 (x : T225) (y : T15) : T226
  insn w486 (x : T226) (y : T22) : T227
  insn w487 (x : T227) (y : T29) : T228
  insn w488 (x : T228) (y : T36) : T229
  insn w489 (x : T229) (y : T43) : T230
  insn w490 (x : T230) (y : T50) : T231
  insn w491 (x : T231) (y : T57) : T232
  insn w492 (x : T232) (y : T64) : T233
  insn w493 (x : T233) (y : T71) : T234
  insn w494 (x : T234) (y : T78) : T235
  insn w495 (x : T235) (y : T85) : T236
  insn w496 (x : T236) (y : T92) : T237
  insn w497 (x : T237) (y : T99) : T238
  insn w498 (x : T238) (y : T106) : T239
  insn w499 (x : T239) (y : T113) : T240
  insn w500 (x : T240) (y : T120) : T241
  insn w501 (x : T241) (y : T127) : T242
  insn w502 (x : T242) (y : T134) : T243
  insn w503 (x : T243) (y : T141) : T244
  insn w504 (x : T244) (y : T148) : T245
  insn w505 (x : T245) (y : T155) : T246
  insn w506 (x : T246) (y : T162) : T247
  insn w507 (x : T247) (y : T169) : T248
  insn w508 (x : T248) (y : T176) : T249
  insn w509 (x : T249) (y : T183) : T250
  insn w510 (x : T250) (y : T190) : T251
  insn w511 (x : T251) (y : T197) : T252
  insn w512 (x : T252) (y : T204) : T253
  insn w513 (x : T253) (y : T211) : T254
  insn w514 (x : T254) (y : T218) : T255
  insn w515 (x : T255) (y : T225) : T256
  insn w516 (x : T256) (y : T232) : T257
  insn w517 (x : T257) (y : T239) : T258
  insn w518 (x : T258) (y : T246) : T259
  insn w519 (x : T259) (y : T253) : T0
  end wide

#guard (Wide.w519.sig (e := Wide.env)).argTypes.map (·.name) == #["x", "y"]

section
variable {e : Env _root_.Unit} [Wide.env ⊑ e]
example : TypeRef e 0 := Wide.T259.ref
example : InsnRef e Wide.w0.sig := Wide.w0
example : InsnRef e Wide.w519.sig := Wide.w519
end

end Strata.Mantle.DSLScaleTest
