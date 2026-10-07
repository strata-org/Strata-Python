/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
-- Building IR values needs the environment representation at code-generation time.
import StrataMantle.Env.WF
-- Also imported as `meta`, so that the interpreter running `native_decide` below has
-- compiled code for the base environment.
meta import StrataMantle.Env.WF
-- `decide +kernel` unfolds the checker, the base and core's array operations.
import all StrataMantle.WF
import all StrataMantle.Env
import all StrataMantle.Base
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq

set_option autoImplicit false

/-!
# Three functions written against the base environment

A client of `Mantle.IR` reaches types and operations only through `Base`, so
this test is also the check that nothing downstream needs the raw layer, and that an
operation's type arguments reduce where a caller has to write them.

Each function is then run past the checker, and the last section is the mistakes it
has to reject.
-/

namespace Strata.Mantle.IRTest

private def boolT : TypeExpr base 0 := Base.Bool.ty
private def intT  : TypeExpr base 0 := Base.Int.ty
private def strT  : TypeExpr base 0 := Base.String.ty
private def unitT : TypeExpr base 0 := Base.Unit.ty
private def refIntT : TypeExpr base 0 := Base.Ref.ty intT
private def exceptStrIntT : TypeExpr base 0 := Base.Except.ty strT intT

private def d (n : Nat) (t : TypeExpr base 0) : ValDecl base := ⟨⟨n⟩, t⟩

/-- The block called `s`. -/
private def lbl (s : String) : Label := ⟨.str .base s⟩

/-- A transfer to `s`, binding nothing. -/
private def to (s : String) : BlockValue := ⟨lbl s, #[]⟩

/-! ## A cell written under a condition

    f(%0 : Bool) : Int
      entry:
        %1 = const int 0
        %2 = refNew[Int] %1
        branch %0 ^bump() ^done()
      bump:
        %3 = const int 1
        %4 = refSet[Int] %2 %3
        jump ^done()
      done:
        %5 = refGet[Int] %2
        ret %5

`%2` is used in both successors, which the entry dominates — the property the
well-formedness layer will check, and which nothing here relies on. -/

private def fEntry : Block base Unit where
  label  := lbl "entry"
  params := #[d 0 boolT]
  instrs := #[
    .const () (d 1 intT) (.int 0),
    .apply () (d 2 refIntT) Base.refNew #v[intT] #[⟨1⟩] #[] #[]]
  term := .branch () ⟨0⟩ (to "bump") (to "done")
  info := ()

private def fBump : Block base Unit where
  label  := lbl "bump"
  params := #[]
  instrs := #[
    .const () (d 3 intT) (.int 1),
    .apply () (d 4 unitT) Base.refSet #v[intT] #[⟨2⟩, ⟨3⟩] #[] #[]]
  term := .jump () (to "done")
  info := ()

private def fDone : Block base Unit where
  label  := lbl "done"
  params := #[]
  instrs := #[.apply () (d 5 intT) Base.refGet #v[intT] #[⟨2⟩] #[] #[]]
  term := .ret () ⟨5⟩
  info := ()

private def f : Func base Unit where
  name    := .str .base "f"
  retType := intT
  blocks  := #[fEntry, fBump, fDone]
  names   := #[⟨"cond", 0⟩, ⟨"zero", 0⟩, ⟨"cell", 0⟩, ⟨"one", 0⟩,
               ⟨"unit", 0⟩, ⟨"result", 0⟩]
  info    := ()

/-! ## A failing operation with a handler

    g() : Int
      entry:
        %0 = const int 3
        %1 = div %0 %0 ^handler()   -- %1 : Int
        ret %1
      handler(%2 : String):
        %3 = const int (-1)
        ret %3

A handler needs an operation that can fail, and the base declares none: failure is a
language's own business, and `ok` and `error` are constructors rather than operations.  So
this section declares one, which doubles as the smallest environment extending the base.

The handler is `div`'s `err` successor, a `BlockValue` with no arguments bound, so the
payload `String` is exactly what the target still expects. -/

private def divName : Name := .str .base "div"

/-- `div (a b : Int) (^err (msg : String)) : Int`. -/
private def divSig : InsnSig base :=
  { ann := (), argTypes := #[⟨"a", intT⟩, ⟨"b", intT⟩],
    returnType := intT, succs := #[⟨"err", #[strT]⟩] }

private theorem divFresh : divName ∉ base := by native_decide

private def sig1 : Env Unit := base.addInsn divName divSig divFresh
private def s01 : base ⊆ sig1 := Env.subset_addInsn _ _ _ _
local instance : base ⊑ sig1 := ⟨s01⟩
private def divR : InsnRef sig1 (divSig.ofSubset s01) :=
  InsnRef.ofAddInsn base divName divSig divFresh

private def intT1 : TypeExpr sig1 0 := intT.ofSubset s01
private def strT1 : TypeExpr sig1 0 := strT.ofSubset s01
private def d1 (n : Nat) (t : TypeExpr sig1 0) : ValDecl sig1 := ⟨⟨n⟩, t⟩

private def gEntry : Block sig1 Unit where
  label  := lbl "entry"
  params := #[]
  instrs := #[
    .const () (d1 0 intT1) (.int 3),
    .apply () (d1 1 intT1) divR #v[] #[⟨0⟩, ⟨0⟩] #[to "handler"] #[]]
  term := .ret () ⟨1⟩
  info := ()

private def gHandler : Block sig1 Unit where
  label  := lbl "handler"
  params := #[d1 2 strT1]
  instrs := #[.const () (d1 3 intT1) (.int (-1))]
  term := .ret () ⟨3⟩
  info := ()

private def g : Func sig1 Unit where
  name    := .str .base "g"
  retType := intT1
  blocks  := #[gEntry, gHandler]
  names   := #[]
  info    := ()

private def mg : Module sig1 Unit where
  name  := .str .base "failing"
  funcs := #[g]
  info  := ()

/-! ## A failure inspected rather than handled

    h() : Int
      entry:
        %0 = const str "boom"
        %1 = error[String, Int] %0            -- %1 : Except String Int
        Except.case[String, Int] %1 ^ok() ^err()
      ok(%2 : Int):
        ret %2
      err(%3 : String):
        %4 = const int 0
        ret %4

The successors follow `Except`'s declaration order, and each receives the payload of the
constructor it handles — which is what its block parameter is. -/

private def hEntry : Block base Unit where
  label  := lbl "entry"
  params := #[]
  instrs := #[
    .const () (d 0 strT) (.str "boom"),
    .apply () (d 1 exceptStrIntT) Base.Except.error #v[strT, intT] #[⟨0⟩] #[] #[]]
  term := .apply () Base.Except.case #v[strT, intT] #[⟨1⟩] #[to "ok", to "err"] #[]
  info := ()

private def hOk : Block base Unit where
  label  := lbl "ok"
  params := #[d 2 intT]
  instrs := #[]
  term := .ret () ⟨2⟩
  info := ()

private def hErr : Block base Unit where
  label  := lbl "err"
  params := #[d 3 strT]
  instrs := #[.const () (d 4 intT) (.int 0)]
  term := .ret () ⟨4⟩
  info := ()

private def h : Func base Unit where
  name    := .str .base "h"
  retType := intT
  blocks  := #[hEntry, hOk, hErr]
  names   := #[]
  info    := ()

private def m : Module base Unit where
  name  := .str .base "test"
  funcs := #[f, h]
  info  := ()

example : m.funcs.size = 2 := rfl

example : f.blocks.size = 3 := rfl

example : fEntry.instrs.size = 2 := rfl

/-- A constant's type comes from the base, not from a declaration. -/
example : Const.typeOf (.int 0) = intT := rfl

example : Const.typeOf .unit = unitT := rfl

/-- Annotations map at every level, and nothing else moves. -/
example : (fEntry.map (fun _ => 7)).info = 7 := rfl

example : (fEntry.map (fun _ => 7)).instrs.size = 2 := by simp [fEntry]

example : (m.map (fun _ => 7)).funcs.size = 2 := by simp [Module.map, m]

example : (m.map (fun _ => 7)).name = m.name := rfl

/-! ## The checker

Every rule the module owes, decided in the kernel. -/

example : Func.WF #[] f := by decide +kernel

example : Func.WF #[] g := by decide +kernel

example : Func.WF #[] h := by decide +kernel

example : Module.WF m := by decide +kernel

example : Module.WF mg := by decide +kernel

/-! ## What it rejects

One mistake per function, each of a kind a translator actually makes. -/

/-- A result typed as the cell's contents rather than as the cell. -/
private def badResult : Func base Unit :=
  { f with blocks := #[{ fEntry with instrs := #[
      .const () (d 1 intT) (.int 0),
      .apply () (d 2 intT) Base.refNew #v[intT] #[⟨1⟩] #[] #[]] }, fBump, fDone] }

example : ¬ Func.WF #[] badResult := by decide +kernel

/-- An operand that is not the type the signature declares: the cell and the value
swapped. -/
private def badOperand : Func base Unit :=
  { f with blocks := #[fEntry, { fBump with instrs := #[
      .const () (d 3 intT) (.int 1),
      .apply () (d 4 unitT) Base.refSet #v[intT] #[⟨3⟩, ⟨2⟩] #[] #[]] }, fDone] }

example : ¬ Func.WF #[] badOperand := by decide +kernel

/-- Too few operands for the signature. -/
private def badArity : Func base Unit :=
  { f with blocks := #[fEntry, { fBump with instrs := #[
      .const () (d 3 intT) (.int 1),
      .apply () (d 4 unitT) Base.refSet #v[intT] #[⟨2⟩] #[] #[]] }, fDone] }

example : ¬ Func.WF #[] badArity := by decide +kernel

/-- A transfer to a block that does not exist. -/
private def badTarget : Func base Unit :=
  { f with blocks :=
      #[{ fEntry with term := .branch () ⟨0⟩ (to "bump") (to "nowhere") }, fBump, fDone] }

example : ¬ Func.WF #[] badTarget := by decide +kernel

/-- A transfer that supplies an argument its target does not declare. -/
private def badArgs : Func base Unit :=
  { f with blocks := #[fEntry, { fBump with term := .jump () ⟨lbl "done", #[⟨3⟩]⟩ }, fDone] }

example : ¬ Func.WF #[] badArgs := by decide +kernel

/-- Two definitions of one value id, so there is no context at all. -/
private def badDefs : Func base Unit :=
  { f with blocks := #[fEntry, { fBump with instrs := #[
      .const () (d 1 intT) (.int 1),
      .apply () (d 4 unitT) Base.refSet #v[intT] #[⟨2⟩, ⟨1⟩] #[] #[]] }, fDone] }

example : ¬ Func.WF #[] badDefs := by decide +kernel

/-- A successor on an operation that declares none. -/
private def badHandler : Func base Unit :=
  { f with blocks := #[{ fEntry with instrs := #[
      .const () (d 1 intT) (.int 0),
      .apply () (d 2 refIntT) Base.refNew #v[intT] #[⟨1⟩] #[to "done"] #[]] }, fBump, fDone] }

example : ¬ Func.WF #[] badHandler := by decide +kernel

/-- A case successor that expects the wrong payload: `ok` carries the value, not the
error. -/
private def badArm : Func base Unit :=
  { h with blocks :=
      #[{ hEntry with
          term := .apply () Base.Except.case #v[strT, intT] #[⟨1⟩] #[to "err", to "ok"] #[] },
        hOk, hErr] }

/-- Blocks are named, not numbered: reordering the non-entry blocks changes nothing. -/
example : Func.WF #[] { h with blocks := #[hEntry, hErr, hOk] } := by decide +kernel

/-- A transfer to the entry block, whose parameters are the function's. -/
private def badToEntry : Func base Unit :=
  { f with blocks := #[fEntry, { fBump with term := .jump () ⟨lbl "entry", #[⟨0⟩]⟩ }, fDone] }

example : ¬ Func.WF #[] badToEntry := by decide +kernel

/-- Two blocks under one label. -/
private def badLabels : Func base Unit :=
  { f with blocks := #[fEntry, fBump, { fDone with label := lbl "bump" }] }

example : ¬ Func.WF #[] badLabels := by decide +kernel

example : ¬ Func.WF #[] badArm := by decide +kernel

/-- A function with no entry block. -/
private def badEmpty : Func base Unit := { f with blocks := #[] }

example : ¬ Func.WF #[] badEmpty := by decide +kernel

/-! ## Constructors are instructions

`ok` and `error` are the instructions `addData` declared for `Except`, so a constructor is
applied as any polymorphic operation is: at explicit type arguments, which fix the result
type and the payload's. -/

-- `error`'s signature: `[e a] (err : e) : Except e a`.
example : (Base.Except.error.sig (e := base)).typeArgc = 2 := rfl
#guard (Base.Except.error.sig (e := base)).typeParams == #["e", "a"]
#guard (Base.Except.error.sig (e := base)).argTypes.map (·.name) == #["err"]
#guard (Base.Except.ok.sig (e := base)).argTypes.map (·.name) == #["value"]

-- The constructors' references know which constructor of `Except` they are.
#guard (Base.Except.ok (e := base)).ctorAddr?.map (fun a => (a.dataIdx, a.idx)) == some (0, 0)
#guard (Base.Except.error (e := base)).ctorAddr?.map (fun a => (a.dataIdx, a.idx)) ==
  some (0, 1)
#guard (Base.refNew (e := base)).ctorAddr?.isNone

/-- `h`'s constructor, with its operands and type arguments replaced. -/
private def withError (tyArgs : Vector (TypeExpr base 0) 2) (arg : ValId) : Func base Unit :=
  { h with blocks := #[{ hEntry with instrs := #[
      .const () (d 0 strT) (.str "boom"),
      .apply () (d 1 exceptStrIntT) Base.Except.error tyArgs #[arg] #[] #[]] }, hOk, hErr] }

example : Func.WF #[] (withError #v[strT, intT] ⟨0⟩) := by decide +kernel

/-- A wrong payload: `error` at `String, Int` takes a `String`, not an `Int`. -/
private def badPayload : Func base Unit :=
  { h with blocks := #[{ hEntry with instrs := #[
      .const () (d 0 intT) (.int 0),
      .apply () (d 1 exceptStrIntT) Base.Except.error #v[strT, intT] #[⟨0⟩] #[] #[]] },
    hOk, hErr] }

example : ¬ Func.WF #[] badPayload := by decide +kernel

/-- Wrong type arguments: at `Int, String` the result is `Except Int String`, which is not
the type `%1` is declared with. -/
example : ¬ Func.WF #[] (withError #v[intT, strT] ⟨0⟩) := by decide +kernel

/-- A constructor with the wrong number of operands. -/
private def badCtorArity : Func base Unit :=
  { h with blocks := #[{ hEntry with instrs := #[
      .const () (d 0 strT) (.str "boom"),
      .apply () (d 1 exceptStrIntT) Base.Except.error #v[strT, intT] #[⟨0⟩, ⟨0⟩] #[] #[]] },
    hOk, hErr] }

example : ¬ Func.WF #[] badCtorArity := by decide +kernel

/-- `ok` builds the other successor's value: the case still sends `ok` its payload. -/
private def hOkVal : Func base Unit :=
  { h with blocks := #[{ hEntry with instrs := #[
      .const () (d 0 intT) (.int 3),
      .apply () (d 1 exceptStrIntT) Base.Except.ok #v[strT, intT] #[⟨0⟩] #[] #[]] },
    hOk, hErr] }

example : Func.WF #[] hOkVal := by decide +kernel

/-! ## Terminators

A terminator is a terminal operation, checked as any operation is: a case instruction like
`jump` and `branch`, and a return like any jump, to `Label.exit`. -/

/-- `h`'s entry, ending with `term`. -/
private def hWith (term : Terminator base Unit) : Func base Unit :=
  { h with blocks := #[{ hEntry with term }, hOk, hErr] }

/-- A case with a successor too few. -/
example : ¬ Func.WF #[] (hWith (.apply () Base.Except.case #v[strT, intT] #[⟨1⟩] #[to "ok"] #[]))
    := by decide +kernel

/-- A case with a successor too many. -/
example : ¬ Func.WF #[] (hWith
    (.apply () Base.Except.case #v[strT, intT] #[⟨1⟩] #[to "ok", to "err", to "err"] #[])) := by
  decide +kernel

/-- A case at the wrong type arguments: at `Int, String` the scrutinee is `Except Int String`,
and `ok` receives a `String`. -/
example : ¬ Func.WF #[] (hWith
    (.apply () Base.Except.case #v[intT, strT] #[⟨1⟩] #[to "ok", to "err"] #[])) := by
  decide +kernel

/-- A case on a value that is not of the datatype. -/
example : ¬ Func.WF #[] (hWith
    (.apply () Base.Except.case #v[strT, intT] #[⟨0⟩] #[to "ok", to "err"] #[])) := by
  decide +kernel

/-- A non-terminal operation as a terminator: `refGet` falls through. -/
example : ¬ Func.WF #[] { f with blocks := #[fEntry, fBump,
    { fDone with term := .apply () Base.refGet #v[intT] #[⟨2⟩] #[] #[] }] } := by
  decide +kernel

/-- `jump`, applied as an instruction. -/
private def jumpInsn : Instruction base Unit :=
  .apply () (d 6 unitT) Base.jump #v[] #[] #[to "done"] #[]

/-- A terminal operation as an instruction: `jump` never falls through. -/
example : ¬ Func.WF #[] { f with blocks := #[fEntry,
    { fBump with instrs := fBump.instrs.push jumpInsn }, fDone] } := by
  decide +kernel

/-- `ret` is a jump to `Label.exit`, passing the result. -/
example : (Terminator.ret () ⟨5⟩ : Terminator base Unit) = .jump () ⟨Label.exit, #[⟨5⟩]⟩ := rfl

/-- `ret` written out as a jump to the exit is accepted as `ret` is. -/
example : Func.WF #[] { f with blocks := #[fEntry, fBump,
    { fDone with term := .apply () Base.jump #v[] #[] #[⟨Label.exit, #[⟨5⟩]⟩] #[] }] } := by
  decide +kernel

/-- A jump to the exit with a value of the wrong type: `%2` is the cell, not an `Int`. -/
example : ¬ Func.WF #[] { f with blocks := #[fEntry, fBump, { fDone with term := .ret () ⟨2⟩ }] }
    := by decide +kernel

/-- A jump to the exit with no value. -/
example : ¬ Func.WF #[] { f with blocks := #[fEntry, fBump,
    { fDone with term := .jump () ⟨Label.exit, #[]⟩ }] } := by
  decide +kernel

/-- A block no transfer names, under `l`. -/
private def spare (l : Label) : Block base Unit :=
  { label := l, params := #[], instrs := #[], term := .unreachable (), info := () }

example : Func.WF #[] { f with blocks := f.blocks.push (spare (lbl "spare")) } := by
  decide +kernel

/-- A block labelled with the exit, even one no transfer names. -/
example : ¬ Func.WF #[] { f with blocks := f.blocks.push (spare Label.exit) } := by
  decide +kernel

example : ¬ Func.WF #[] { f with blocks := #[{ fEntry with label := Label.exit }, fBump, fDone] }
    := by decide +kernel

/-- `unreachable` takes nothing and goes nowhere. -/
example : Func.WF #[] { f with blocks := #[fEntry, fBump, { fDone with term := .unreachable () }] }
    := by decide +kernel

/-- `branch` takes a `Bool`: `%2` is the cell. -/
example : ¬ Func.WF #[] { f with blocks :=
    #[{ fEntry with term := .branch () ⟨2⟩ (to "bump") (to "done") }, fBump, fDone] } := by
  decide +kernel

/-! ## Function references

A function-reference constant has type `base.Code` and names a function of the module. -/

private def codeT : TypeExpr base 0 := Base.Code.ty

/-- `ref() : Unit`, which takes a code pointer to `target` and returns unit. -/
private def refTo (target : Name) (type : TypeExpr base 0 := codeT) : Func base Unit where
  name    := .str .base "ref"
  retType := unitT
  blocks  := #[{ label := lbl "entry", params := #[], info := (),
                 instrs := #[.const () (d 0 type) (.func target), .const () (d 1 unitT) .unit],
                 term := .ret () ⟨1⟩ }]
  names   := #[⟨"code", 0⟩, ⟨"unit", 0⟩]
  info    := ()

/-- `ref` beside `f`. -/
private def refModule (target : Name) (type : TypeExpr base 0 := codeT) : Module base Unit where
  name  := .str .base "m"
  funcs := #[refTo target type, f]
  info  := ()

example : Module.WF (refModule (.str .base "f")) := by decide +kernel
example : Module.WF (refModule (.str .base "ref")) := by decide +kernel

/-- A reference to a function the module does not define. -/
example : ¬ Module.WF (refModule (.str .base "g")) := by decide +kernel

/-- A code pointer declared at a type other than `base.Code`. -/
example : ¬ Module.WF (refModule (.str .base "f") intT) := by decide +kernel

end Strata.Mantle.IRTest
