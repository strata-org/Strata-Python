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
-- The builder, the checker and the printer run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.DDM
meta import StrataMantle.WF
meta import StrataMantle.Env.WF
meta import StrataMantleTest.DSLTest

set_option autoImplicit false

/-!
# Successors and terminal instructions

Functions over `Demo`, each emitted, checked and printed, that use its instructions with
successors and its terminal instructions: `add` and its `err`; `fork`, whose two successors
receive two values; `raise`; `br`; and `loop`, which also takes a region.  Then the mistakes
the successor and terminal rules reject.
-/

namespace Strata.Mantle.SuccTest

open Strata.Mantle.DSLTest

open Strata.Mantle.Build (freshVal freshLabel startBlock startBlockWith startFreshBlock
  emitConst emitApply finishBlock terminate goto build FailedFunc region)

private abbrev E := Demo.env

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF}

/-- The build failed because its function is not well formed, not by a misuse. -/
private def rejected (b : Built) : Bool :=
  match b with
  | .error e => e.misuses.isEmpty
  | .ok _ => false


/-- Finish the open block by returning `exc` as a failure. -/
private def propagate (exc : ValId) : BuildM E Unit Unit := do
  let r ← emitApply (.str .base "r") (Demo.raising Demo.Value) Base.Except.error #[exc]
  finishBlock (.ret () r)

/-- `f(x : Value)`, whose entry `body x h` emits, and whose handler `h` takes an exception of
type `excT` and returns `x` as a failure. -/
private def handled (body : ValId → Label → BuildM E Unit Unit) (excT : TypeExpr E := Demo.Value) :
    Built :=
  build (.str .base "f") (Demo.raising Demo.Value) () do
    let x ← freshVal (.str .base "x") Demo.Value
    let _ ← startFreshBlock #[x] "entry"
    let h ← freshLabel "handler"
    body x.id h
    let _ ← startBlockWith h (.str .base "exc") excT
    propagate x.id

/-! ## Successor typing

`add` falls through with the sum, or transfers to `err` with the exception.  `fork`
pre-binds `c` for `right`, which then also receives the two values `fork` passes. -/

private def sum : Built :=
  build (.str .base "sum") (Demo.raising Demo.Value) () do
    let x ← freshVal (.str .base "x") Demo.Value
    let c ← freshVal (.str .base "c") Base.Bool
    let _ ← startFreshBlock #[x, c] "entry"
    let h ← freshLabel "handler"
    let l ← freshLabel "left"
    let r ← freshLabel "right"
    let s ← emitApply (.str .base "s") Demo.Value Demo.add #[x.id, x.id] #[goto h]
    let _ ← emitApply (.str .base "u") Base.Unit Demo.fork #[] #[goto l, goto r #[c.id]]
    let ok ← emitApply (.str .base "ok") (Demo.raising Demo.Value) Base.Except.ok #[s]
    finishBlock (.ret () ok)
    propagate <| ← startBlockWith h (.str .base "exc") Demo.Value
    let a ← freshVal (.str .base "a") Demo.Value
    let b ← freshVal (.str .base "b") Demo.Value
    startBlock l #[a, b]
    propagate a.id
    let c' ← freshVal (.str .base "c") Base.Bool
    let a' ← freshVal (.str .base "a") Demo.Value
    let b' ← freshVal (.str .base "b") Demo.Value
    startBlock r #[c', a', b']
    propagate b'.id

#guard sum.isOk

/-! ## Terminal instructions

`raise` ends its block with only an `err` successor; `br` with two, neither receiving
anything.  A terminal instruction defines no result. -/

private def raiser : Built :=
  build (.str .base "raiser") (Demo.raising Demo.Value) () do
    let x ← freshVal (.str .base "x") Demo.Value
    let c ← freshVal (.str .base "c") Base.Bool
    let _ ← startFreshBlock #[x, c] "entry"
    let yes ← freshLabel "yes"
    let no ← freshLabel "no"
    let h ← freshLabel "handler"
    finishBlock (.apply () Demo.br ⟨#[], rfl⟩ #[c.id] #[goto yes, goto no] #[])
    startBlock yes
    finishBlock (.apply () Demo.raise ⟨#[], rfl⟩ #[x.id] #[goto h] #[])
    startBlock no
    let ok ← emitApply (.str .base "ok") (Demo.raising Demo.Value) Base.Except.ok #[x.id]
    finishBlock (.ret () ok)
    propagate (← startBlockWith h (.str .base "exc") Demo.Value)

#guard raiser.isOk

/-! ## A terminal instruction with a region

`loop` runs its body region from `init`, and leaves to `exit` with the last value.  The
region's blocks are the function's, so its labels count with them. -/

private def counter : Built :=
  build (.str .base "counter") Base.Int () do
    let _ ← startFreshBlock #[] "entry"
    let zero ← emitConst (.str .base "zero") (.int 0)
    let i ← freshVal (.str .base "i") Base.Int
    let body ← region #[i] (base := "body") do
      let t ← emitConst (.str .base "t") (.bool false)
      finishBlock (.ret () t)
    let done ← freshLabel "done"
    terminate Demo.loop #[zero] #[goto done] #[pure body] (typeArgs := ta[Base.Int])
    let n ← freshVal (.str .base "n") Base.Int
    startBlock done #[n]
    finishBlock (.ret () n.id)

#guard counter.isOk

/-! ## Printed

Successors follow the operands, each `^target(args)`; a terminal instruction is the
block's last line, with no result. -/

/-- info: module succs {
  func @sum(%x.0 : demo.Value, %c.0 : base.Bool) -> base.Except(demo.Value, demo.Value) {
    entry.0(%x.0 : demo.Value, %c.0 : base.Bool):
      %s.0 : demo.Value = demo.add(%x.0, %x.0) ^handler.0()
      %u.0 : base.Unit = demo.fork ^left.0() ^right.0(%c.0)
      %ok.0 : base.Except(demo.Value, demo.Value) = base.ok[demo.Value, demo.Value](%s.0)
      ret(%ok.0)
    handler.0(%exc.0 : demo.Value):
      %r.0 : base.Except(demo.Value, demo.Value) = base.error[demo.Value, demo.Value](%exc.0)
      ret(%r.0)
    left.0(%a.0 : demo.Value, %b.0 : demo.Value):
      %r.1 : base.Except(demo.Value, demo.Value) = base.error[demo.Value, demo.Value](%a.0)
      ret(%r.1)
    right.0(%c.1 : base.Bool, %a.1 : demo.Value, %b.1 : demo.Value):
      %r.2 : base.Except(demo.Value, demo.Value) = base.error[demo.Value, demo.Value](%b.1)
      ret(%r.2)
  }
  func @raiser(%x.0 : demo.Value, %c.0 : base.Bool) -> base.Except(demo.Value, demo.Value) {
    entry.0(%x.0 : demo.Value, %c.0 : base.Bool):
      demo.br(%c.0) ^yes.0() ^no.0()
    yes.0():
      demo.raise(%x.0) ^handler.0()
    no.0():
      %ok.0 : base.Except(demo.Value, demo.Value) = base.ok[demo.Value, demo.Value](%x.0)
      ret(%ok.0)
    handler.0(%exc.0 : demo.Value):
      %r.0 : base.Except(demo.Value, demo.Value) = base.error[demo.Value, demo.Value](%exc.0)
      ret(%r.0)
  }
  func @counter() -> base.Int {
    entry.0():
      demo.loop[base.Int](0) ^done.0() {
        body.0(%i.0 : base.Int):
          ret(false)
      }
    done.0(%n.0 : base.Int):
      ret(%n.0)
  }
} -/
#guard_msgs in
#eval do
  let fs := #[← IO.ofExcept sum, ← IO.ofExcept raiser, ← IO.ofExcept counter]
  match Module.ofChecked (.str .base "succs") fs () with
  | .ok m => IO.println m
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

/-! ## What it rejects -/

/-- `x + x`, with successors `ks`, returned as a success. -/
private def addRet (x : ValId) (ks : Array BlockValue) : BuildM E Unit Unit := do
  let s ← emitApply (.str .base "s") Demo.Value Demo.add #[x, x] ks
  finishBlock (.ret () (← emitApply (.str .base "ok") (Demo.raising Demo.Value) Base.Except.ok
    #[s]))

/-- `add` declares one successor; here it is given none, and then two. -/
private def wrongCount (n : Nat) : Built :=
  handled fun x h => addRet x (Array.replicate n (goto h))

#guard (wrongCount 1).isOk
#guard rejected (wrongCount 0)
#guard rejected (wrongCount 2)

-- The handler takes an `Int`, but `err` passes a `Value`: `wrongCount 1` otherwise.
#guard rejected (handled (fun x h => addRet x #[goto h]) Base.Int)

/-- A successor inside a region naming a block outside it. -/
private def outsideRegion : Built :=
  build (.str .base "f") (Demo.raising Demo.Value) () do
    let x ← freshVal (.str .base "x") Demo.Value
    let c ← freshVal (.str .base "c") Base.Bool
    let _ ← startFreshBlock #[x, c] "entry"
    let h ← freshLabel "handler"
    let thn := region #[] (base := "then") do
      let s ← emitApply (.str .base "s") Demo.Value Demo.add #[x.id, x.id] #[goto h]
      finishBlock (.ret () s)
    let els := region #[] (finishBlock (.ret () x.id)) "else"
    let r ← emitApply (.str .base "r") Demo.Value Demo.«if» #[c.id] (regions := #[thn, els])
    let ok ← emitApply (.str .base "ok") (Demo.raising Demo.Value) Base.Except.ok #[r]
    finishBlock (.ret () ok)
    propagate (← startBlockWith h (.str .base "exc") Demo.Value)

#guard rejected outsideRegion

/-- A successor naming the entry block, even one whose parameters match the payload. -/
private def toEntry : Built :=
  build (.str .base "f") (Demo.raising Demo.Value) () do
    let x ← freshVal (.str .base "x") Demo.Value
    let entry ← startFreshBlock #[x] "entry"
    addRet x.id #[goto entry]

#guard rejected toEntry

-- A terminal instruction in the middle of a block.
#guard rejected (handled fun x h => do
    let _ ← emitApply (.str .base "u") Base.Unit Demo.raise #[x] #[goto h]
    finishBlock (.ret () (← emitApply (.str .base "ok") (Demo.raising Demo.Value) Base.Except.ok
        #[x])))

-- A non-terminal instruction in terminator position: `add` would fall through, and
-- there is nothing to fall through to.
#guard rejected (handled fun x h =>
    finishBlock (.apply () Demo.add ⟨#[], rfl⟩ #[x, x] #[goto h] #[]))

/-- A terminal instruction's region is still checked: `loop`'s body must return `Bool`. -/
private def badLoopBody : Built :=
  build (.str .base "f") Base.Int () do
    let _ ← startFreshBlock #[] "entry"
    let zero ← emitConst (.str .base "zero") (.int 0)
    let i ← freshVal (.str .base "i") Base.Int
    let body ← region #[i] (finishBlock (.ret () i.id)) "body"
    let done ← freshLabel "done"
    terminate Demo.loop #[zero] #[goto done] #[pure body] (typeArgs := ta[Base.Int])
    let n ← freshVal (.str .base "n") Base.Int
    startBlock done #[n]
    finishBlock (.ret () n.id)

#guard rejected badLoopBody

/-! ## A function reference inside a terminator's region

A module checks the references in a terminal instruction's region too: `f`'s only reference
is to `counter`, in its `loop` body. -/

/-- `counter`, named `f`, with a reference to `counter` in its `loop` body. -/
private def refInLoop : Built :=
  build (.str .base "f") Base.Int () do
    let _ ← startFreshBlock #[] "entry"
    let zero ← emitConst (.str .base "zero") (.int 0)
    let i ← freshVal (.str .base "i") Base.Int
    let body ← region #[i] (base := "body") do
      let _ ← Build.emitFunc (.str .base "counter") Base.Code
      finishBlock (.ret () (← emitConst (.str .base "t") (.bool false)))
    let done ← freshLabel "done"
    terminate Demo.loop #[zero] #[goto done] #[pure body] (typeArgs := ta[Base.Int])
    let n ← freshVal (.str .base "n") Base.Int
    startBlock done #[n]
    finishBlock (.ret () n.id)

/-- What a module of `fs` gives through `Module.ofChecked`, then through `Module.Raw.check`:
`ok`, or the names. -/
private def checkBoth (fs : Array {f : Func E Unit // f.WF}) : String × String :=
  let text : Except (Array Name) (Module E Unit) → String
    | .ok _ => "ok"
    | .error bad => s!"{bad.map ToDDM.nameText}"
  (text (Module.ofChecked (.str .base "m") fs ()),
    text (Module.Raw.check { name := .str .base "m", funcs := fs.map (·.val), info := () }))

-- With `counter` defined, the module is well formed.
#guard match refInLoop, counter with
  | .ok f, .ok c => checkBoth #[f, c] == ("ok", "ok")
  | _, _ => false

-- Without it, both checks name `f`, which is well formed on its own.
/--
info: ofChecked: #[f]
check: #[f]
-/
#guard_msgs in
#eval do
  let (a, b) := checkBoth #[← IO.ofExcept refInLoop]
  IO.println s!"ofChecked: {a}\ncheck: {b}"

end Strata.Mantle.SuccTest
