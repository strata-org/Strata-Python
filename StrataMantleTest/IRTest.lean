/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
-- Building IR values needs the environment representation at code-generation time.
import StrataMantle.Env.WF
-- The `#guard`s run the checker as compiled code.
meta import StrataMantle.WF

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

private def wf {env : Env Unit} [base ⊑ env] (fn : Func env Unit) : Bool := decide fn.WF

private def illFormed {env : Env Unit} [base ⊑ env] (fn : Func env Unit) : Bool :=
  !decide fn.WF


/-- The type arguments `Int`, `String, Int` and `Int, String`. -/
private def tInt : TypeArgs base #[.type] := ⟨#[.ty Base.Int], rfl⟩
private def tStrInt : TypeArgs base #[.type, .type] := ⟨#[.ty Base.String, .ty Base.Int], rfl⟩
private def tIntStr : TypeArgs base #[.type, .type] := ⟨#[.ty Base.Int, .ty Base.String], rfl⟩

private def d (n : Nat) (t : TypeExpr base) : ValDecl base := ⟨⟨n⟩, t⟩

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
  params := #[d 0 Base.Bool]
  instrs := #[
    .const () (d 1 Base.Int) (.int 0),
    .apply () (d 2 (Base.Ref Base.Int)) Base.refNew tInt #[⟨1⟩] #[] #[]]
  term := .branch () ⟨0⟩ (to "bump") (to "done")
  info := ()

private def fBump : Block base Unit where
  label  := lbl "bump"
  params := #[]
  instrs := #[
    .const () (d 3 Base.Int) (.int 1),
    .apply () (d 4 Base.Unit) Base.refSet tInt #[⟨2⟩, ⟨3⟩] #[] #[]]
  term := .jump () (to "done")
  info := ()

private def fDone : Block base Unit where
  label  := lbl "done"
  params := #[]
  instrs := #[.apply () (d 5 Base.Int) Base.refGet tInt #[⟨2⟩] #[] #[]]
  term := .ret () ⟨5⟩
  info := ()

private def f : Func base Unit where
  name    := .str .base "f"
  retType := Base.Int
  blocks  := #[fEntry, fBump, fDone]
  names   := #["cond", "zero", "cell", "one", "unit", "result"].map fun s => Name.num (.str .base s) 0
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
  { ann := (), argTypes := #[⟨"a", Base.Int⟩, ⟨"b", Base.Int⟩],
    returnType := some Base.Int, succs := #[⟨"err", #[.ty Base.String]⟩] }

/-- `div` is not a base name. -/
private theorem divFresh : divName ∉ base := by rw [Base.mem_env]; decide

private def sig1 : Env Unit := base.addInsn divName divSig divFresh
private theorem s01 : base ⊆ sig1 := Env.subset_addInsn _ _ _ _
local instance : base ⊑ sig1 := ⟨Env.le_of_subset s01⟩
private def divR : InsnRef sig1 (divSig.ofSubset s01) :=
  InsnRef.ofAddInsn base divName divSig divFresh

private def intT1 : TypeExpr sig1 := (Base.Int : TypeExpr base).ofSubset s01
private def strT1 : TypeExpr sig1 := (Base.String : TypeExpr base).ofSubset s01
private def d1 (n : Nat) (t : TypeExpr sig1) : ValDecl sig1 := ⟨⟨n⟩, t⟩

private def gEntry : Block sig1 Unit where
  label  := lbl "entry"
  params := #[]
  instrs := #[
    .const () (d1 0 intT1) (.int 3),
    .apply () (d1 1 intT1) divR ⟨#[], rfl⟩ #[⟨0⟩, ⟨0⟩] #[to "handler"] #[]]
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
  names   := (Array.range 8).map (Name.num .base ·)
  info    := ()

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
    .const () (d 0 Base.String) (.str "boom"),
    .apply () (d 1 (Base.Except Base.String Base.Int)) Base.Except.error tStrInt #[⟨0⟩] #[] #[]]
  term := .apply () Base.Except.case tStrInt #[⟨1⟩] #[to "ok", to "err"] #[]
  info := ()

private def hOk : Block base Unit where
  label  := lbl "ok"
  params := #[d 2 Base.Int]
  instrs := #[]
  term := .ret () ⟨2⟩
  info := ()

private def hErr : Block base Unit where
  label  := lbl "err"
  params := #[d 3 Base.String]
  instrs := #[.const () (d 4 Base.Int) (.int 0)]
  term := .ret () ⟨4⟩
  info := ()

private def h : Func base Unit where
  name    := .str .base "h"
  retType := Base.Int
  blocks  := #[hEntry, hOk, hErr]
  names   := (Array.range 8).map (Name.num .base ·)
  info    := ()

private def m : Module.Raw base Unit where
  name  := .str .base "test"
  funcs := #[f, h]
  info  := ()

example : m.funcs.size = 2 := rfl

example : f.blocks.size = 3 := rfl

example : fEntry.instrs.size = 2 := rfl

/-- A constant's type comes from the base, not from a declaration. -/
example : Const.typeOf (env := base) (.int 0) = Base.Int := rfl

example : Const.typeOf (env := base) .unit = Base.Unit := rfl

/-- Annotations map at every level, and nothing else moves. -/
example : (fEntry.map (fun _ => 7)).info = 7 := rfl

example : (fEntry.map (fun _ => 7)).instrs.size = 2 := by simp [fEntry]

example : (m.map (fun _ => 7)).funcs.size = 2 := by simp [Module.Raw.map, m]

example : (m.map (fun _ => 7)).name = m.name := rfl

/-! ## The checker

Every rule a function owes, decided by the compiled checker. -/

#guard wf f

#guard wf g

#guard wf h

/-! ## What it rejects

One mistake per function, each of a kind a translator actually makes. -/

/-- A result typed as the cell's contents rather than as the cell. -/
private def badResult : Func base Unit :=
  { f with blocks := #[{ fEntry with instrs := #[
      .const () (d 1 Base.Int) (.int 0),
      .apply () (d 2 Base.Int) Base.refNew tInt #[⟨1⟩] #[] #[]] }, fBump, fDone] }

#guard illFormed badResult

/-- An operand that is not the type the signature declares: the cell and the value
swapped. -/
private def badOperand : Func base Unit :=
  { f with blocks := #[fEntry, { fBump with instrs := #[
      .const () (d 3 Base.Int) (.int 1),
      .apply () (d 4 Base.Unit) Base.refSet tInt #[⟨3⟩, ⟨2⟩] #[] #[]] }, fDone] }

#guard illFormed badOperand

/-- Too few operands for the signature. -/
private def badArity : Func base Unit :=
  { f with blocks := #[fEntry, { fBump with instrs := #[
      .const () (d 3 Base.Int) (.int 1),
      .apply () (d 4 Base.Unit) Base.refSet tInt #[⟨2⟩] #[] #[]] }, fDone] }

#guard illFormed badArity

/-- A transfer to a block that does not exist. -/
private def badTarget : Func base Unit :=
  { f with blocks :=
      #[{ fEntry with term := .branch () ⟨0⟩ (to "bump") (to "nowhere") }, fBump, fDone] }

#guard illFormed badTarget

/-- A transfer that supplies an argument its target does not declare. -/
private def badArgs : Func base Unit :=
  { f with blocks := #[fEntry, { fBump with term := .jump () ⟨lbl "done", #[⟨3⟩]⟩ }, fDone] }

#guard illFormed badArgs

/-- Two definitions of one value id, so there is no context at all. -/
private def badDefs : Func base Unit :=
  { f with blocks := #[fEntry, { fBump with instrs := #[
      .const () (d 1 Base.Int) (.int 1),
      .apply () (d 4 Base.Unit) Base.refSet tInt #[⟨2⟩, ⟨1⟩] #[] #[]] }, fDone] }

#guard illFormed badDefs

/-- A successor on an operation that declares none. -/
private def badHandler : Func base Unit :=
  { f with blocks := #[{ fEntry with instrs := #[
      .const () (d 1 Base.Int) (.int 0),
      .apply () (d 2 (Base.Ref Base.Int)) Base.refNew tInt #[⟨1⟩] #[to "done"] #[]] },
    fBump, fDone] }

#guard illFormed badHandler

/-- A case successor that expects the wrong payload: `ok` carries the value, not the
error. -/
private def badArm : Func base Unit :=
  { h with blocks :=
      #[{ hEntry with
          term := .apply () Base.Except.case tStrInt #[⟨1⟩] #[to "err", to "ok"] #[] },
        hOk, hErr] }

-- Blocks are named, not numbered: reordering the non-entry blocks changes nothing.
#guard wf { h with blocks := #[hEntry, hErr, hOk] }

/-- A transfer to the entry block, whose parameters are the function's. -/
private def badToEntry : Func base Unit :=
  { f with blocks := #[fEntry, { fBump with term := .jump () ⟨lbl "entry", #[⟨0⟩]⟩ }, fDone] }

#guard illFormed badToEntry

/-- Two blocks under one label. -/
private def badLabels : Func base Unit :=
  { f with blocks := #[fEntry, fBump, { fDone with label := lbl "bump" }] }

#guard illFormed badLabels

#guard illFormed badArm

/-- A function with no entry block. -/
private def badEmpty : Func base Unit := { f with blocks := #[] }

#guard illFormed badEmpty

/-! ## Constructors are instructions

`ok` and `error` are the instructions `addData` declared for `Except`, so a constructor is
applied as any polymorphic operation is: at explicit type arguments, which fix the result
type and the payload's. -/

-- `error`'s signature: `[e a] (err : e) : Except e a`.
example : (Base.Except.error.sig (e := base)).typeArgc = 2 := rfl
#guard (Base.Except.error.sig (e := base)).typeParams == #[⟨"e", .type⟩, ⟨"a", .type⟩]
#guard (Base.Except.error.sig (e := base)).argTypes.map (·.name) == #["err"]
#guard (Base.Except.ok.sig (e := base)).argTypes.map (·.name) == #["value"]

-- The constructors' references know which constructor of `Except` they are.
#guard (Base.Except.ok (e := base)).ctorAddr?.map (fun a => (a.dataIdx, a.idx)) == some (0, 0)
#guard (Base.Except.error (e := base)).ctorAddr?.map (fun a => (a.dataIdx, a.idx)) ==
  some (0, 1)
#guard (Base.refNew (e := base)).ctorAddr?.isNone

/-- `h`'s constructor, with its operands and type arguments replaced. -/
private def withError (e a : TypeExpr base) (arg : ValId) : Func base Unit :=
  { h with blocks := #[{ hEntry with instrs := #[
      .const () (d 0 Base.String) (.str "boom"),
      .apply () (d 1 (Base.Except Base.String Base.Int)) Base.Except.error ⟨#[.ty e, .ty a], rfl⟩
        #[arg] #[] #[]] },
      hOk, hErr] }

#guard wf (withError Base.String Base.Int ⟨0⟩)

/-- A wrong payload: `error` at `String, Int` takes a `String`, not an `Int`. -/
private def badPayload : Func base Unit :=
  { h with blocks := #[{ hEntry with instrs := #[
      .const () (d 0 Base.Int) (.int 0),
      .apply () (d 1 (Base.Except Base.String Base.Int)) Base.Except.error tStrInt #[⟨0⟩] #[]
        #[]] },
    hOk, hErr] }

#guard illFormed badPayload

-- Wrong type arguments: at `Int, String` the result is `Except Int String`, which is not
-- the type `%1` is declared with.
#guard illFormed (withError Base.Int Base.String ⟨0⟩)

/-- A constructor with the wrong number of operands. -/
private def badCtorArity : Func base Unit :=
  { h with blocks := #[{ hEntry with instrs := #[
      .const () (d 0 Base.String) (.str "boom"),
      .apply () (d 1 (Base.Except Base.String Base.Int)) Base.Except.error tStrInt #[⟨0⟩, ⟨0⟩]
        #[] #[]] },
    hOk, hErr] }

#guard illFormed badCtorArity

/-- `ok` builds the other successor's value: the case still sends `ok` its payload. -/
private def hOkVal : Func base Unit :=
  { h with blocks := #[{ hEntry with instrs := #[
      .const () (d 0 Base.Int) (.int 3),
      .apply () (d 1 (Base.Except Base.String Base.Int)) Base.Except.ok tStrInt #[⟨0⟩] #[] #[]] },
    hOk, hErr] }

#guard wf hOkVal

/-! ## Terminators

A terminator is a terminal operation, checked as any operation is: a case instruction like
`jump` and `branch`, and a return like any jump, to `Label.exit`. -/

/-- `h`'s entry, ending with `term`. -/
private def hWith (term : Terminator base Unit) : Func base Unit :=
  { h with blocks := #[{ hEntry with term }, hOk, hErr] }

-- A case with a successor too few.
#guard illFormed (hWith (.apply () Base.Except.case tStrInt #[⟨1⟩] #[to "ok"] #[]))

-- A case with a successor too many.
#guard illFormed (hWith
    (.apply () Base.Except.case tStrInt #[⟨1⟩] #[to "ok", to "err", to "err"] #[]))

-- A case at the wrong type arguments: at `Int, String` the scrutinee is `Except Int String`,
-- and `ok` receives a `String`.
#guard illFormed (hWith
    (.apply () Base.Except.case tIntStr #[⟨1⟩] #[to "ok", to "err"] #[]))

-- A case on a value that is not of the datatype.
#guard illFormed (hWith
    (.apply () Base.Except.case tStrInt #[⟨0⟩] #[to "ok", to "err"] #[]))

-- A non-terminal operation as a terminator: `refGet` falls through.
#guard illFormed { f with blocks := #[fEntry, fBump,
    { fDone with term := .apply () Base.refGet tInt #[⟨2⟩] #[] #[] }] }

/-- `jump`, applied as an instruction. -/
private def jumpInsn : Instruction base Unit :=
  .apply () (d 6 Base.Unit) Base.jump ⟨#[], rfl⟩ #[] #[to "done"] #[]

-- A terminal operation as an instruction: `jump` never falls through.
#guard illFormed { f with blocks := #[fEntry,
    { fBump with instrs := fBump.instrs.push jumpInsn }, fDone] }

/-- `ret` is a jump to `Label.exit`, passing the result. -/
example : (Terminator.ret () ⟨5⟩ : Terminator base Unit) = .jump () ⟨Label.exit, #[⟨5⟩]⟩ := rfl

-- `ret` written out as a jump to the exit is accepted as `ret` is.
#guard wf { f with blocks := #[fEntry, fBump,
    { fDone with term := .apply () Base.jump ⟨#[], rfl⟩ #[] #[⟨Label.exit, #[⟨5⟩]⟩] #[] }] }

-- A jump to the exit with a value of the wrong type: `%2` is the cell, not an `Int`.
#guard illFormed { f with blocks := #[fEntry, fBump, { fDone with term := .ret () ⟨2⟩ }] }

-- A jump to the exit with no value.
#guard illFormed { f with blocks := #[fEntry, fBump,
    { fDone with term := .jump () ⟨Label.exit, #[]⟩ }] }

/-- A block no transfer names, under `l`. -/
private def spare (l : Label) : Block base Unit :=
  { label := l, params := #[], instrs := #[], term := .unreachable (), info := () }

-- A block no transfer names is unreachable, which `Func.Reachable` rules out.  Named by a
-- transfer, the same block is reachable.
#guard illFormed { f with blocks := f.blocks.push (spare (lbl "spare")) }
#guard wf { f with blocks := #[fEntry, fBump, { fDone with term := .jump () ⟨lbl "spare", #[]⟩ },
  spare (lbl "spare")] }

-- A block labelled with the exit, even one no transfer names.
#guard illFormed { f with blocks := f.blocks.push (spare Label.exit) }

#guard illFormed { f with blocks := #[{ fEntry with label := Label.exit }, fBump, fDone] }

-- `unreachable` takes nothing and goes nowhere.
#guard wf { f with blocks := #[fEntry, fBump, { fDone with term := .unreachable () }] }

-- `branch` takes a `Bool`: `%2` is the cell.
#guard illFormed { f with blocks :=
    #[{ fEntry with term := .branch () ⟨2⟩ (to "bump") (to "done") }, fBump, fDone] }

/-! ## Function references

A function-reference constant names a function of the module, and has that function's code
type, `base.Fn` of its parameter types and its return type, or the untyped `base.Code`.  The
module decides both: a function is well formed with a reference at any type. -/


/-- `ref() : Unit`, which takes a code pointer to `target` and returns unit. -/
private def refTo (target : Name) (type : TypeExpr base := Base.Code) : Func base Unit where
  name    := .str .base "ref"
  retType := Base.Unit
  blocks  := #[{ label := lbl "entry", params := #[], info := (),
                 instrs := #[.const () (d 0 type) (.func target), .const () (d 1 Base.Unit) .unit],
                 term := .ret () ⟨1⟩ }]
  names   := #["code", "unit"].map fun s => Name.num (.str .base s) 0
  info    := ()

/-- `ref` beside `f`. -/
private def refModule (target : Name) (type : TypeExpr base := Base.Code) :
    Module.Raw base Unit where
  name  := .str .base "m"
  funcs := #[refTo target type, f]
  info  := ()

#guard Module.Raw.WF (refModule (.str .base "f"))
#guard Module.Raw.WF (refModule (.str .base "ref"))

-- A reference to a function the module does not define.
#guard ¬ Module.Raw.WF (refModule (.str .base "g"))

/-- `f`'s code type: it takes a `Bool` and returns an `Int`. -/
private def fnBoolIntT : TypeExpr base := Base.Fn [Base.Bool] Base.Int

#guard f.codeType == fnBoolIntT
#guard (refTo (.str .base "f")).codeType == Base.Fn [] Base.Unit

-- A reference at its target's code type, to another function and to itself.
#guard Module.Raw.WF (refModule (.str .base "f") fnBoolIntT)
#guard Module.Raw.WF (refModule (.str .base "ref") (Base.Fn [] Base.Unit))

-- A reference is a code pointer: at `base.Int` the function itself is not well formed, beside
-- the same function at `base.Code` and at a `base.Fn`.
#guard ¬ wf (refTo (.str .base "f") Base.Int)
#guard wf (refTo (.str .base "f") Base.Code)
#guard wf (refTo (.str .base "f") (Base.Fn [Base.Int] Base.Int))
#guard ¬ Module.Raw.WF (refModule (.str .base "f") Base.Int)
-- At a `base.Fn` with another parameter list or another result the function is well formed,
-- but its module is not.
#guard ¬ Module.Raw.WF (refModule (.str .base "f") (Base.Fn [Base.Int] Base.Int))
#guard ¬ Module.Raw.WF (refModule (.str .base "f") (Base.Fn [Base.Bool] Base.Bool))
#guard ¬ Module.Raw.WF (refModule (.str .base "ref") fnBoolIntT)

end Strata.Mantle.IRTest
