/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataMantle.DDM
public import StrataMantleTest.DSLTest
import StrataMantle.Env.WF
-- The builder and the printer run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.DDM
meta import StrataMantle.Env.WF
meta import StrataMantleTest.DSLTest
-- `decide +kernel` unfolds the checker, the environment and core's array operations.
import all StrataMantle.WF
import all StrataMantle.Env
import all StrataMantle.Base
import all StrataMantle.Build
import all StrataMantleTest.DSLTest
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq

set_option autoImplicit false

/-!
# Successors and terminal instructions

Functions over `Demo` using its instructions with successors — `add` and its `err`, and
`fork`, whose two successors receive two values — and its terminal ones: `raise`, `br`, and
`loop`, which also takes a region.  Each is emitted, checked and printed; then the mistakes
the successor and terminal rules reject.
-/

namespace Strata.Mantle.SuccTest

open Strata.Mantle.DSLTest

open Strata.Mantle.Build (freshVal freshLabel startBlock startBlockWith startFreshBlock
  emitConst emitApply finishBlock goto build Errors Holds region)

private abbrev E := Demo.env

private def boolT : TypeExpr E 0 := Base.Bool.ty
private def intT : TypeExpr E 0 := Base.Int.ty
private def unitT : TypeExpr E 0 := Base.Unit.ty
private def valT : TypeExpr E 0 := Demo.Value.ty
private def raisingT : TypeExpr E 0 := Demo.raising.ty valT

/-- Finish the open block by returning `exc` as a failure. -/
private def propagate (exc : ValId) : BuildM E Unit Unit := do
  let r ← emitApply "r" raisingT Base.Except.error #v[valT, valT] #[exc]
  finishBlock (.ret () r)

/-- `f(x : Value)`, whose entry `body x h` emits, and whose handler `h` takes an exception of
type `excT` and returns `x` as a failure. -/
private def handled (body : ValId → Label → BuildM E Unit Unit) (excT : TypeExpr E 0 := valT) :
    Except Errors (Func E Unit) :=
  build (.str .base "f") raisingT () do
    let x ← freshVal "x" valT
    let _ ← startFreshBlock #[x] "entry"
    let h ← freshLabel "handler"
    body x.id h
    let _ ← startBlockWith h "exc" excT
    propagate x.id

/-! ## Successor typing

`add` falls through with the sum, or transfers to `err` with the exception.  `fork`
pre-binds `c` for `right`, which then also receives the two values `fork` passes. -/

private def sum : Except Errors (Func E Unit) :=
  build (.str .base "sum") raisingT () do
    let x ← freshVal "x" valT
    let c ← freshVal "c" boolT
    let _ ← startFreshBlock #[x, c] "entry"
    let h ← freshLabel "handler"
    let l ← freshLabel "left"
    let r ← freshLabel "right"
    let s ← emitApply "s" valT Demo.add #v[] #[x.id, x.id] #[goto h]
    let _ ← emitApply "u" unitT Demo.fork #v[] #[] #[goto l, goto r #[c.id]]
    let ok ← emitApply "ok" raisingT Base.Except.ok #v[valT, valT] #[s]
    finishBlock (.ret () ok)
    propagate <| ← startBlockWith h "exc" valT
    let a ← freshVal "a" valT
    let b ← freshVal "b" valT
    startBlock l #[a, b]
    propagate a.id
    let c' ← freshVal "c" boolT
    let a' ← freshVal "a" valT
    let b' ← freshVal "b" valT
    startBlock r #[c', a', b']
    propagate b'.id

example : Holds (Func.WF #[]) sum := by decide +kernel

/-! ## Terminal instructions

`raise` ends its block with only an `err` successor; `br` with two, neither receiving
anything.  A terminal instruction defines no result. -/

private def raiser : Except Errors (Func E Unit) :=
  build (.str .base "raiser") raisingT () do
    let x ← freshVal "x" valT
    let c ← freshVal "c" boolT
    let _ ← startFreshBlock #[x, c] "entry"
    let yes ← freshLabel "yes"
    let no ← freshLabel "no"
    let h ← freshLabel "handler"
    finishBlock (.apply () Demo.br #v[] #[c.id] #[goto yes, goto no] #[])
    startBlock yes
    finishBlock (.apply () Demo.raise #v[] #[x.id] #[goto h] #[])
    startBlock no
    let ok ← emitApply "ok" raisingT Base.Except.ok #v[valT, valT] #[x.id]
    finishBlock (.ret () ok)
    propagate (← startBlockWith h "exc" valT)

example : Holds (Func.WF #[]) raiser := by decide +kernel

/-! ## A terminal instruction with a region

`loop` runs its body region from `init`, and leaves to `exit` with the last value.  The
region's blocks are the function's, so its labels count with them. -/

private def counter : Except Errors (Func E Unit) :=
  build (.str .base "counter") intT () do
    let _ ← startFreshBlock #[] "entry"
    let zero ← emitConst "zero" (.int 0)
    let i ← freshVal "i" intT
    let body ← region #[i] (base := "body") do
      let t ← emitConst "t" (.bool false)
      finishBlock (.ret () t)
    let done ← freshLabel "done"
    finishBlock (.apply () Demo.loop #v[intT] #[zero] #[goto done] #[body])
    let n ← freshVal "n" intT
    startBlock done #[n]
    finishBlock (.ret () n.id)

example : Holds (Func.WF #[]) counter := by decide +kernel

/-- The region's blocks count among the function's. -/
example : Holds (·.labels.map (·.name) =
    [.num (.str .base "entry") 0, .num (.str .base "body") 0, .num (.str .base "done") 0])
    counter := by
  decide +kernel

private def m : Except Errors (Module E Unit) :=
  return { name := .str .base "succs", funcs := #[← sum, ← raiser, ← counter], info := () }

example : Holds Module.WF m := by decide +kernel

/-! ## Printed

Successors follow the operands, each `^target(args)`; a terminal instruction is the
block's last line, with no result. -/

/-- info: module succs {
  func @sum(%0 : demo.Value, %1 : base.Bool) -> base.Except(demo.Value, demo.Value) {
    entry.0(%0 : demo.Value, %1 : base.Bool):
      %2 : demo.Value = demo.add %0 %0 ^handler.0()
      %3 : base.Unit = demo.fork ^left.0() ^right.0(%1)
      %4 : base.Except(demo.Value, demo.Value) = base.ok[demo.Value, demo.Value] %2
      ret %4
    handler.0(%5 : demo.Value):
      %6 : base.Except(demo.Value, demo.Value) = base.error[demo.Value, demo.Value] %5
      ret %6
    left.0(%7 : demo.Value, %8 : demo.Value):
      %9 : base.Except(demo.Value, demo.Value) = base.error[demo.Value, demo.Value] %7
      ret %9
    right.0(%10 : base.Bool, %11 : demo.Value, %12 : demo.Value):
      %13 : base.Except(demo.Value, demo.Value) = base.error[demo.Value, demo.Value] %12
      ret %13
  }
  func @raiser(%0 : demo.Value, %1 : base.Bool) -> base.Except(demo.Value, demo.Value) {
    entry.0(%0 : demo.Value, %1 : base.Bool):
      demo.br %1 ^yes.0() ^no.0()
    yes.0():
      demo.raise %0 ^handler.0()
    no.0():
      %2 : base.Except(demo.Value, demo.Value) = base.ok[demo.Value, demo.Value] %0
      ret %2
    handler.0(%3 : demo.Value):
      %4 : base.Except(demo.Value, demo.Value) = base.error[demo.Value, demo.Value] %3
      ret %4
  }
  func @counter() -> base.Int {
    entry.0():
      %0 : base.Int = const int 0
      demo.loop[base.Int] %0 ^done.0() {
        body.0(%1 : base.Int):
          %2 : base.Bool = const bool (false)
          ret %2
      }
    done.0(%3 : base.Int):
      ret %3
  }
}
-/
#guard_msgs in
#eval do IO.println (toString (← IO.ofExcept m))

/-! ## What it rejects -/

/-- `x + x`, with successors `ks`, returned as a success. -/
private def addRet (x : ValId) (ks : Array BlockValue) : BuildM E Unit Unit := do
  let s ← emitApply "s" valT Demo.add #v[] #[x, x] ks
  finishBlock (.ret () (← emitApply "ok" raisingT Base.Except.ok #v[valT, valT] #[s]))

/-- `add` declares one successor; here it is given none, and then two. -/
private def wrongCount (n : Nat) : Except Errors (Func E Unit) :=
  handled fun x h => addRet x (Array.replicate n (goto h))

example : Holds (Func.WF #[]) (wrongCount 1) := by decide +kernel
example : Holds (¬ Func.WF #[] ·) (wrongCount 0) := by decide +kernel
example : Holds (¬ Func.WF #[] ·) (wrongCount 2) := by decide +kernel

/-- The handler takes an `Int`, but `err` passes a `Value`: `wrongCount 1` otherwise. -/
example : Holds (¬ Func.WF #[] ·) (handled (fun x h => addRet x #[goto h]) intT) := by
  decide +kernel

/-- A successor inside a region naming a block outside it. -/
private def outsideRegion : Except Errors (Func E Unit) :=
  build (.str .base "f") raisingT () do
    let x ← freshVal "x" valT
    let c ← freshVal "c" boolT
    let _ ← startFreshBlock #[x, c] "entry"
    let h ← freshLabel "handler"
    let thn ← region #[] (base := "then") do
      let s ← emitApply "s" valT Demo.add #v[] #[x.id, x.id] #[goto h]
      finishBlock (.ret () s)
    let els ← region #[] (finishBlock (.ret () x.id)) "else"
    let r ← emitApply "r" valT Demo.«if» #v[valT] #[c.id] (regions := #[thn, els])
    let ok ← emitApply "ok" raisingT Base.Except.ok #v[valT, valT] #[r]
    finishBlock (.ret () ok)
    propagate (← startBlockWith h "exc" valT)

example : Holds (¬ Func.WF #[] ·) outsideRegion := by decide +kernel

/-- A successor naming the entry block, even one whose parameters match the payload. -/
private def toEntry : Except Errors (Func E Unit) :=
  build (.str .base "f") raisingT () do
    let x ← freshVal "x" valT
    let entry ← startFreshBlock #[x] "entry"
    addRet x.id #[goto entry]

example : Holds (¬ Func.WF #[] ·) toEntry := by decide +kernel

/-- A terminal instruction in the middle of a block. -/
example : Holds (¬ Func.WF #[] ·) (handled fun x h => do
    let _ ← emitApply "u" unitT Demo.raise #v[] #[x] #[goto h]
    finishBlock (.ret () (← emitApply "ok" raisingT Base.Except.ok #v[valT, valT] #[x]))) := by
  decide +kernel

/-- A non-terminal instruction in terminator position: `add` would fall through, and
there is nothing to fall through to. -/
example : Holds (¬ Func.WF #[] ·) (handled fun x h =>
    finishBlock (.apply () Demo.add #v[] #[x, x] #[goto h] #[])) := by
  decide +kernel

/-- A terminal instruction's region is still checked: `loop`'s body must return `Bool`. -/
private def badLoopBody : Except Errors (Func E Unit) :=
  build (.str .base "f") intT () do
    let _ ← startFreshBlock #[] "entry"
    let zero ← emitConst "zero" (.int 0)
    let i ← freshVal "i" intT
    let body ← region #[i] (finishBlock (.ret () i.id)) "body"
    let done ← freshLabel "done"
    finishBlock (.apply () Demo.loop #v[intT] #[zero] #[goto done] #[body])
    let n ← freshVal "n" intT
    startBlock done #[n]
    finishBlock (.ret () n.id)

example : Holds (¬ Func.WF #[] ·) badLoopBody := by decide +kernel

end Strata.Mantle.SuccTest
