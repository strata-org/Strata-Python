/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataDyn.Build
public import StrataDyn.DDM
public import StrataDyn.DDMRead
import StrataDyn.Env.WF
import StrataDyn.DSL
import StrataDynTest.WFParts
-- The builder, the checker, the printer and the reader run as compiled code below.
meta import StrataDyn.Build
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.WF
meta import StrataDyn.Env.WF
meta import StrataDynTest.WFParts

set_option autoImplicit false

/-!
# Failures in contract regions

An operation that may fail transfers to its failure successor when it fails.  In a contract
region, the rules of `Func.ContractRegionsWF` say where that successor may go, and how blocks
end:

* `failures`: in a clause's own region, to a failure block, which returns `false`, or `true` in a
  `free ensures` clause, or ends in `unreachable`;
* `propagates`: in a region nested in a clause, to a block that ends in `unreachable`, or, if the
  region may propagate, to a propagating block, which passes the failure on with `base.error`;
* `terminators`: every block ends in control flow: `ret`, `jump`, `branch`, `unreachable` or a
  case instruction;
* `acyclic`: the blocks of every contract region, at any depth, form an acyclic graph.

Each function accepted here is built, printed, and read back unchanged.  Each function rejected
here breaks exactly one rule of `Func.WF`, unless its test says otherwise, and the reader names
the problem.
-/

namespace Strata.Dyn.ContractRegionTest

open Strata.Dyn.WFParts (broken failing)

/-- Operations that may fail, operations that run regions, and terminal operations. -/
public environment Demo extends Base where
  namespace demo
  open base
  /-- `lhs ≥ rhs`. -/
  pure insn ge (lhs rhs : Int) : Bool
  /-- `a / b`.  It fails, with an error code, when `b` is zero. -/
  calls insn div (a b : Int) (^err (e : Int)) : Int
  /-- Runs `body`: the value of an `ok`, or a transfer to `err` with the error of an `error`. -/
  pure insn attempt (&body : Except Int Bool) (^err (e : Int)) : Bool
  /-- Runs `body`, and returns what it returns, an `error` included, as a value. -/
  pure insn «try» (&body : Except Int Bool) : Except Int Bool
  /-- Runs `body`, and returns its value, or transfers to `err` by a test that `a` does not
  show. -/
  pure insn guard [a] (&body : a) (^err (e : Int)) : a
  /-- `x`, or a transfer to `zero`, which receives nothing, when `x` is zero. -/
  pure insn nonZero (x : Int) (^zero) : Int
  /-- Run `then` if `cond` holds, else `else`. -/
  pure insn «if» [a] (cond : Bool) (&«then» &«else» : a) : a
  /-- `a / b`, which ends its block: it continues at `ok` with the quotient, or at `err` when `b`
  is zero. -/
  pure terminal insn tryDiv (a b : Int) (^ok (q : Int)) (^err (e : Int))
  /-- Runs `body`, which ends its block, and continues at `k` with its value. -/
  pure terminal insn run (&body : Bool) (^k (b : Bool))
  end demo

open Strata.Dyn.Build (freshVal startBlock startFreshBlock freshLabel emitConst emitApply
  finishBlock terminate goto build FailedFunc region withFailureBlock withPropagatingBlock)

private abbrev E := Demo.env

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF}

/-- The function a build emitted, well formed or not. -/
private def funcOf (b : Built) : Func E Unit :=
  match b with
  | .ok f => f.val
  | .error e => e.func

private def intT : TypeExpr E := Base.Int
private def boolT : TypeExpr E := Base.Bool
/-- `base.Except(base.Int, base.Bool)`, what the region of `demo.attempt` returns. -/
private def exT : TypeExpr E := Base.Except intT boolT

private def nm (s : String) : Name := .str .base s

/-- Check that the built function `b` prints as the module `text`, and that reading `text` gives
it back.  Print the module where it differs, or the diagnostics. -/
private def agrees (b : Built) (text : String) : IO Unit := do
  match b with
  | .error e => IO.println s!"not built: {e}"
  | .ok f =>
    match Module.ofChecked (nm "m") #[f] () with
    | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"
    | .ok m => unless toString m == text do IO.println m
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m => unless toString m == text do IO.println m

/-- Print the built function `b` as a module, or why it was not built, and check that the printed
module reads back unchanged.  Print the module read where it differs, or the diagnostics. -/
private def printBuilt (b : Built) : IO Unit := do
  match b with
  | .error e => IO.println s!"not built: {e}"
  | .ok f =>
    match Module.ofChecked (nm "m") #[f] () with
    | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"
    | .ok m =>
      IO.println m
      match ← Module.read E (toString m) "t.dyn" with
      | .error e => IO.println e
      | .ok r => unless toString r == toString m do IO.println r

/-- Read `text` in `Demo.env`, and print the diagnostics, or the module if it prints otherwise. -/
private def readBack (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m => unless toString m == text do IO.println m

/-- Read `text` in `Demo.env` and print the diagnostics, or that it was read. -/
private def readErrors (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok _ => IO.println "read"

/-! ## Builders -/

/-- `@m.f(x, y) = x`, with the contract that `contract x y` emits after the body. -/
private def withContract (contract : ValId → ValId → BuildM E Unit Unit) : Built :=
  build (.str (nm "m") "f") intT () do
    let x ← freshVal (nm "x") intT
    let y ← freshVal (nm "y") intT
    let _ ← startFreshBlock #[x, y] "entry"
    finishBlock (.ret () x.id)
    contract x.id y.id

/-- The extern `@m.g(x, y) -> base.Int`, with the contract that `contract x y` emits. -/
private def externWith (contract : ValId → ValId → BuildM E Unit Unit) : Built :=
  Build.buildExtern (.str (nm "m") "g") #[(nm "x", intT), (nm "y", intT)] intT () fun ps => do
    if let (some x, some y) := (ps[0]?, ps[1]?) then contract x y

/-- `div(a, b) ≥ 0`, returned, with the failure of `div` going to `fail`. -/
private def quotNonNeg (fail : Label) (a b : ValId) : BuildM E Unit Unit := do
  let q ← emitApply (nm "q") intT Demo.div.ref #[a, b] (succs := #[goto fail])
  let zero ← emitConst (nm "zero") (.int 0)
  finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[q, zero]))

/-- `attempt { body }`, returned, with the failure of `attempt` going to `fail`. -/
private def attempting (fail : Label) (body : BuildM E Unit Unit) : BuildM E Unit Unit := do
  let r := region #[] (base := "body") body
  finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.attempt.ref #[] (succs := #[goto fail])
    (regions := #[r])))

/-- `ok(div(a, b) ≥ 0)`, returned from a region of `attempt`, with the failure of `div` going to
`fail`. -/
private def okQuotNonNeg (fail : Label) (a b : ValId) : BuildM E Unit Unit := do
  let q ← emitApply (nm "q") intT Demo.div.ref #[a, b] (succs := #[goto fail])
  let ge ← emitApply (nm "b") boolT Demo.ge.ref #[q, ← emitConst (nm "zero") (.int 0)]
  finishBlock (.ret () (← emitApply (nm "v") exT Base.Except.ok.ref #[ge]))

/-! ## What the rules accept

A failure that gives the clause's failure value, a failure that goes to a block that ends in
`unreachable`, and a nested region that passes its failure on.  The builder emits each failure
block after the other blocks of its body, so the ids follow `Func.defs`. -/

/-- A `requires` clause whose failure gives `false`. -/
private def reqFalse : Built := withContract fun x y => Build.requires do
  withFailureBlock #[intT] (some false) fun fail => quotNonNeg fail x y

private def reqFalseText : String := "module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %q.0 : base.Int = demo.div(%x.0, %y.0) ^fail.0()
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%x.0)
  }
}
"

#guard failing reqFalse == []
#guard reqFalse.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees reqFalse reqFalseText

-- In full, the failure block is a constant and a `ret`.
/-- info: module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %q.0 : base.Int = demo.div(%x.0, %y.0) ^fail.0()
        %zero.0 : base.Int = const 0
        %ok.0 : base.Bool = demo.ge(%q.0, %zero.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        %value.0 : base.Bool = const false
        ret(%value.0)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%x.0)
  }
} -/
#guard_msgs in
#eval do
  match Module.ofChecked (nm "m") #[← IO.ofExcept reqFalse] () with
  | .ok m => IO.println (m.format .full)
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

/-- A `free ensures` clause of an extern whose failure gives `true`. -/
private def freeTrue : Built := externWith fun _ y =>
  Build.ensures (nm "r") intT (free := true) fun r =>
    withFailureBlock #[intT] (some true) fun fail => quotNonNeg fail r y

private def freeTrueText : String := "module m {
  extern func @m.g(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    free ensures {
      post.0(%r.0 : base.Int):
        %q.0 : base.Int = demo.div(%r.0, %y.0) ^fail.0()
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(true)
    }
}
"

#guard failing freeTrue == []
#guard freeTrue.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees freeTrue freeTrueText

/-- A checked `ensures` clause whose failure gives `false`, and a `requires` clause whose failure
goes to a block that ends in `unreachable`. -/
private def unreachableFail : Built := withContract fun x y => do
  Build.requires (withFailureBlock #[intT] none fun fail => quotNonNeg fail x y)
  Build.ensures (nm "r") intT fun r =>
    withFailureBlock #[intT] (some false) fun fail => quotNonNeg fail r y

private def unreachableFailText : String := "module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %q.0 : base.Int = demo.div(%x.0, %y.0) ^fail.0()
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        unreachable
    }
    ensures {
      post.0(%r.0 : base.Int):
        %q.1 : base.Int = demo.div(%r.0, %y.0) ^fail.1()
        %ok.1 : base.Bool = demo.ge(%q.1, 0)
        ret(%ok.1)
      fail.1(%e.1 : base.Int):
        ret(false)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%x.0)
  }
}
"

#guard failing unreachableFail == []
#guard unreachableFail.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees unreachableFail unreachableFailText

/-- A region nested in a clause that passes the failure of `div` on with `base.error`, so that
the failure of `attempt` carries it to the clause's failure block. -/
private def propagates : Built := withContract fun x y => Build.requires do
  withFailureBlock #[intT] (some false) fun fail => attempting fail do
    withPropagatingBlock intT boolT fun prop => okQuotNonNeg prop x y

private def propagatesText : String := "module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = demo.attempt ^fail.0() {
          body.0():
            %q.0 : base.Int = demo.div(%x.0, %y.0) ^propagate.0()
            %b.0 : base.Bool = demo.ge(%q.0, 0)
            %v.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
            ret(%v.0)
          propagate.0(%exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%exc.0)
            ret(%err.0)
        }
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%x.0)
  }
}
"

#guard failing propagates == []
#guard propagates.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees propagates propagatesText

/-- A region nested two deep, which passes its failure on in the same way. -/
private def propagatesTwice : Built := withContract fun x y => Build.requires do
  withFailureBlock #[intT] (some false) fun fail => attempting fail do
    withPropagatingBlock intT boolT fun prop => do
      let inner := region #[] (base := "body") do
        withPropagatingBlock intT boolT fun p => okQuotNonNeg p x y
      let ok ← emitApply (nm "ok") boolT Demo.attempt.ref #[] (succs := #[goto prop])
        (regions := #[inner])
      finishBlock (.ret () (← emitApply (nm "v") exT Base.Except.ok.ref #[ok]))

private def propagatesTwiceText : String := "module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = demo.attempt ^fail.0() {
          body.0():
            %ok.1 : base.Bool = demo.attempt ^propagate.0() {
              body.1():
                %q.0 : base.Int = demo.div(%x.0, %y.0) ^propagate.1()
                %b.0 : base.Bool = demo.ge(%q.0, 0)
                %v.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
                ret(%v.0)
              propagate.1(%exc.0 : base.Int):
                %err.0 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%exc.0)
                ret(%err.0)
            }
            %v.1 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%ok.1)
            ret(%v.1)
          propagate.0(%exc.1 : base.Int):
            %err.1 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%exc.1)
            ret(%err.1)
        }
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%x.0)
  }
}
"

#guard failing propagatesTwice == []
#guard propagatesTwice.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees propagatesTwice propagatesTwiceText

-- A region of `attempt` may propagate: it declares a failure successor and an `Except` region.
-- The regions of `if` may not, nor that of `try`, which has no failure successor, nor that of
-- `guard`, whose region's type is a variable.
#guard (Demo.attempt.sig (e := E)).mayPropagate == [true]
#guard (Demo.«if».sig (e := E)).mayPropagate == [false, false]
#guard (Demo.«try».sig (e := E)).mayPropagate == [false]
#guard (Demo.guard.sig (e := E)).mayPropagate == [false]
#guard (Demo.run.sig (e := E)).mayPropagate == [false]

-- The successors of a branch are not restricted, and the blocks of a clause need not come in the
-- order of its transfers: `join.0` comes before the blocks that jump to it.
#guard_msgs in
#eval readBack "module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %c.0 : base.Bool = demo.ge(%x.0, %y.0)
        branch(%c.0) ^a.0() ^b.0()
      join.0(%v.0 : base.Bool):
        ret(%v.0)
      a.0():
        jump ^join.0(true)
      b.0():
        jump ^join.0(false)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%x.0)
  }
}
"

-- A case instruction, found by its declaration, may end a block of a clause.
#guard_msgs in
#eval readBack "module m {
  func @m.f(%p.0 : base.Except(base.Int, base.Bool)) -> base.Int
    requires {
      pre.0():
        base.Except.case[base.Int, base.Bool](%p.0) ^isOk.0() ^isErr.0()
      isOk.0(%b.0 : base.Bool):
        ret(%b.0)
      isErr.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%p.0 : base.Except(base.Int, base.Bool)):
      ret(0)
  }
}
"

-- The body is not a contract region: its failures may go anywhere, and it may loop.
/-- info: module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      %q.0 : base.Int = demo.div(%x.0, %y.0) ^handler.0()
      ret(%q.0)
    handler.0(%e.0 : base.Int):
      jump ^handler.0(%e.0)
  }
} -/
#guard_msgs in
#eval printBuilt (build (.str (nm "m") "f") intT () do
  let x ← freshVal (nm "x") intT
  let y ← freshVal (nm "y") intT
  let _ ← startFreshBlock #[x, y] "entry"
  let handler ← freshLabel "handler"
  let q ← emitApply (nm "q") intT Demo.div.ref #[x.id, y.id] (succs := #[goto handler])
  finishBlock (.ret () q)
  let e ← freshVal (nm "e") intT
  startBlock handler #[e]
  finishBlock (.jump () (goto handler #[e.id])))

/-! ## Ids of failure blocks

A failure block comes after the blocks of its body, and gets its ids after theirs.  A failure
block that nothing transfers to is not emitted, so it takes no id and no name. -/

/-- A failure block at a function's top level, and a `requires` clause. -/
private def bodyFail : Built := build (.str (nm "m") "f") intT () do
  let x ← freshVal (nm "x") intT
  let y ← freshVal (nm "y") intT
  let _ ← startFreshBlock #[x, y] "entry"
  withFailureBlock #[intT] none fun fail => do
    let q ← emitApply (nm "q") intT Demo.div.ref #[x.id, y.id] (succs := #[goto fail])
    finishBlock (.ret () q)
  Build.requires do
    finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[x.id, y.id]))

#guard failing bodyFail == []
#guard bodyFail.toOption.any (decide ·.val.Canonical)
#guard bodyFail.toOption.any fun f => f.val.defs.map (·.id.id) == [0, 1, 2, 3, 4]

/-- info: module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = demo.ge(%x.0, %y.0)
        ret(%ok.0)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      %q.0 : base.Int = demo.div(%x.0, %y.0) ^fail.0()
      ret(%q.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }
} -/
#guard_msgs in
#eval printBuilt bodyFail

/-- A failure block that nothing transfers to, then a second clause. -/
private def unusedFail : Built := withContract fun x y => do
  Build.requires (withFailureBlock #[intT] (some false) fun _ => do
    finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[x, y])))
  Build.requires do finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[y, x]))

#guard failing unusedFail == []
#guard unusedFail.toOption.any (decide ·.val.Canonical)
#guard unusedFail.toOption.any fun f => f.val.defs.map (·.id.id) == [0, 1, 2, 3]

/-- info: module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = demo.ge(%x.0, %y.0)
        ret(%ok.0)
    }
    requires {
      pre.1():
        %ok.1 : base.Bool = demo.ge(%y.0, %x.0)
        ret(%ok.1)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%x.0)
  }
} -/
#guard_msgs in
#eval printBuilt unusedFail

-- A propagating block that nothing transfers to is not emitted either.  Emitted, it would not
-- fit this region, which returns a `base.Bool`.
/-- info: module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = demo.ge(%x.0, %y.0)
        ret(%ok.0)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%x.0)
  }
} -/
#guard_msgs in
#eval printBuilt (withContract fun x y => Build.requires do
  withPropagatingBlock intT boolT fun _ => do
    finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[x, y])))

-- An extern has no blocks, and a failure block that nothing transfers to adds none.
/-- info: module m {
  extern func @m.g(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
} -/
#guard_msgs in
#eval printBuilt (externWith fun _ _ => withFailureBlock #[] none fun _ => pure ())

-- A body that leaves a block open when its failure block is due is a misuse.
#guard match withContract (fun x y => Build.requires do
    withFailureBlock #[intT] (some false) fun fail => do
      quotNonNeg fail x y
      let _ ← startFreshBlock #[] "dangling") with
  | .error e => e.misuses == #["block fail.0 opened while block dangling.0 is open"]
  | .ok _ => false

/-! ## What the rules reject

Each rejection breaks one rule, in the builder and in the reader. -/

/-- `@m.f(x, y) -> base.Int` with the contract `clauses`, returning `x`. -/
private def withClauses (clauses : String) : String := s!"module m \{
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
{clauses}
  \{
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%x.0)
  }
}
"

/-! ### A failure in a clause gives the clause's failure value -/

-- A `requires` clause whose failure gives `true`.
#guard failing (withContract fun x y => Build.requires do
  withFailureBlock #[intT] (some true) fun fail => quotNonNeg fail x y) == ["failures"]

/-- info: t.dyn:5:8: in a requires clause of @m.f, the failure successor of %q.0 goes to fail.0, which returns true; a failure must give false or be unreachable -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %q.0 : base.Int = demo.div(%x.0, %y.0) ^fail.0()
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(true)
    }")

-- A checked `ensures` clause whose failure gives `true`.
#guard failing (withContract fun _ y => Build.ensures (nm "r") intT fun r =>
  withFailureBlock #[intT] (some true) fun fail => quotNonNeg fail r y) == ["failures"]

/-- info: t.dyn:5:8: in an ensures clause of @m.f, the failure successor of %q.0 goes to fail.0, which returns true; a failure must give false or be unreachable -/
#guard_msgs in
#eval readErrors (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %q.0 : base.Int = demo.div(%r.0, %y.0) ^fail.0()
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(true)
    }")

-- A `free ensures` clause whose failure gives `false`.
#guard failing (externWith fun _ y => Build.ensures (nm "r") intT (free := true) fun r =>
  withFailureBlock #[intT] (some false) fun fail => quotNonNeg fail r y) == ["failures"]

/-- info: t.dyn:5:8: in a free ensures clause of @m.g, the failure successor of %q.0 goes to fail.0, which returns false; a failure must give true or be unreachable -/
#guard_msgs in
#eval readErrors "module m {
  extern func @m.g(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    free ensures {
      post.0(%r.0 : base.Int):
        %q.0 : base.Int = demo.div(%r.0, %y.0) ^fail.0()
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
}
"

-- A failure block that computes something.
#guard failing (withContract fun x y => Build.requires do
  let fail ← freshLabel "fail"
  quotNonNeg fail x y
  let e ← freshVal (nm "e") intT
  startBlock fail #[e]
  let zero ← emitConst (nm "zero") (.int 0)
  finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[e.id, zero]))) == ["failures"]

/-- info: t.dyn:5:8: in a requires clause of @m.f, the failure successor of %q.0 goes to fail.0, which does more than define constants -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %q.0 : base.Int = demo.div(%x.0, %y.0) ^fail.0()
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        %ok.1 : base.Bool = demo.ge(%e.0, 0)
        ret(%ok.1)
    }")

-- A failure block that only jumps to a block that returns `false`.
/-- info: t.dyn:5:8: in a requires clause of @m.f, the failure successor of %q.0 goes to fail.0, which does not end in unreachable or in ret of a constant that it defines -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %q.0 : base.Int = demo.div(%x.0, %y.0) ^fail.0()
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        jump ^no.0()
      no.0():
        ret(false)
    }")

-- A failure block returns a constant that it defines itself.  This one returns its parameter, to
-- which the failure successor binds `true`, though it defines the constant `false`.
#guard failing (withContract fun x y => Build.requires do
  let fail ← freshLabel "fail"
  let t ← emitConst (nm "t") (.bool true)
  let q ← emitApply (nm "q") intT Demo.div.ref #[x, y] (succs := #[goto fail #[t]])
  let zero ← emitConst (nm "zero") (.int 0)
  finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[q, zero]))
  let b ← freshVal (nm "b") boolT
  let e ← freshVal (nm "e") intT
  startBlock fail #[b, e]
  let _ ← emitConst (nm "f") (.bool false)
  finishBlock (.ret () b.id)) == ["failures"]

/-- info: t.dyn:5:8: in a requires clause of @m.f, the failure successor of %q.0 goes to fail.0, which does not end in unreachable or in ret of a constant that it defines -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %q.0 : base.Int = demo.div(%x.0, %y.0) ^fail.0(true)
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%b.0 : base.Bool, %e.0 : base.Int):
        %f.0 : base.Bool = const false
        ret(%b.0)
    }")

-- This one returns the constant `false` that the clause's entry defines.
#guard failing (withContract fun x y => Build.requires do
  let fail ← freshLabel "fail"
  let f ← emitConst (nm "f") (.bool false)
  quotNonNeg fail x y
  let _ ← Build.startBlockWith fail (nm "e") intT
  finishBlock (.ret () f)) == ["failures"]

/-- info: t.dyn:6:8: in a requires clause of @m.f, the failure successor of %q.0 goes to fail.0, which does not end in unreachable or in ret of a constant that it defines -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %f.0 : base.Bool = const false
        %q.0 : base.Int = demo.div(%x.0, %y.0) ^fail.0()
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(%f.0)
    }")

-- A failure successor that leaves the clause, with `true` bound to the exit's parameter.
#guard failing (withContract fun x y => Build.requires do
  let t ← emitConst (nm "t") (.bool true)
  let n ← emitApply (nm "n") intT Demo.nonZero.ref #[y] (succs := #[goto Label.exit #[t]])
  finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[x, n]))) == ["failures"]

/-- info: t.dyn:5:8: in a requires clause of @m.f, the failure successor of %n.0 leaves the region; a failure must give false or be unreachable -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %n.0 : base.Int = demo.nonZero(%y.0) ^_(true)
        %ok.0 : base.Bool = demo.ge(%x.0, %n.0)
        ret(%ok.0)
    }")

-- The failure of an operation with a region counts too.
/-- info: t.dyn:5:8: in a requires clause of @m.f, the failure successor of %ok.0 goes to fail.0, which returns true; a failure must give false or be unreachable -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = demo.attempt ^fail.0() {
          body.0():
            %b.0 : base.Bool = demo.ge(%x.0, %y.0)
            %v.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
            ret(%v.0)
        }
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(true)
    }")

/-! ### A region nested in a clause passes its failures on -/

-- A nested region that returns `ok` on a failure.
#guard failing (withContract fun x y => Build.requires do
  withFailureBlock #[intT] (some false) fun fail => attempting fail do
    let recover ← freshLabel "recover"
    okQuotNonNeg recover x y
    let e ← freshVal (nm "e") intT
    startBlock recover #[e]
    let t ← emitConst (nm "t") (.bool true)
    finishBlock (.ret () (← emitApply (nm "v") exT Base.Except.ok.ref #[t]))) == ["propagates"]

/-- info: t.dyn:7:12: in a region nested in a contract of @m.f, the failure successor of %q.0 goes to recover.0, which does not pass the failure on with base.error -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = demo.attempt ^fail.0() {
          body.0():
            %q.0 : base.Int = demo.div(%x.0, %y.0) ^recover.0()
            %b.0 : base.Bool = demo.ge(%q.0, 0)
            %v.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
            ret(%v.0)
          recover.0(%e.0 : base.Int):
            %v.1 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](true)
            ret(%v.1)
        }
        ret(%ok.0)
      fail.0(%e.1 : base.Int):
        ret(false)
    }")

-- A failure block that gives a value is not enough in a nested region.
/-- info: t.dyn:8:12: in a region nested in a contract of @m.f, the failure successor of %q.0 goes to no.0, which does not pass the failure on with base.error -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %c.0 : base.Bool = demo.ge(%x.0, 0)
        %v.0 : base.Bool = demo.if[base.Bool](%c.0) {
          then.0():
            %q.0 : base.Int = demo.div(%x.0, %y.0) ^no.0()
            %ok.0 : base.Bool = demo.ge(%q.0, 0)
            ret(%ok.0)
          no.0(%e.0 : base.Int):
            ret(false)
        } {
          else.0():
            ret(true)
        }
        ret(%v.0)
    }")

-- A failure that goes to the exit of a nested region turns into the region's value.
#guard failing (withContract fun x y => Build.requires do
  let c ← emitApply (nm "c") boolT Demo.ge.ref #[x, y]
  let thn := region #[] (base := "then") do
    let q ← emitApply (nm "q") intT Demo.div.ref #[x, y] (succs := #[goto Label.exit])
    finishBlock (.ret () q)
  let els := region #[] (base := "else") (finishBlock (.ret () x))
  let v ← emitApply (nm "v") intT Demo.«if».ref #[c] (regions := #[thn, els])
  finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[v, y]))) == ["propagates"]

/-- info: t.dyn:8:12: in a region nested in a contract of @m.f, the failure successor of %q.0 leaves its region, so it does not pass the failure on with base.error -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %c.0 : base.Bool = demo.ge(%x.0, 0)
        %v.0 : base.Int = demo.if[base.Int](%c.0) {
          then.0():
            %q.0 : base.Int = demo.div(%x.0, %y.0) ^_()
            ret(%q.0)
        } {
          else.0():
            ret(%x.0)
        }
        %ok.0 : base.Bool = demo.ge(%v.0, 0)
        ret(%ok.0)
    }")

-- A region nested two deep that returns `ok` on a failure.
#guard failing (withContract fun x y => Build.requires do
  withFailureBlock #[intT] (some false) fun fail => attempting fail do
    withPropagatingBlock intT boolT fun prop => do
      let inner := region #[] (base := "body") do
        let recover ← freshLabel "recover"
        okQuotNonNeg recover x y
        let e ← freshVal (nm "e") intT
        startBlock recover #[e]
        let t ← emitConst (nm "t") (.bool true)
        finishBlock (.ret () (← emitApply (nm "v") exT Base.Except.ok.ref #[t]))
      let ok ← emitApply (nm "ok") boolT Demo.attempt.ref #[] (succs := #[goto prop])
        (regions := #[inner])
      finishBlock (.ret () (← emitApply (nm "v") exT Base.Except.ok.ref #[ok]))) == ["propagates"]

-- A propagating block passes on the failure it receives, its last parameter.
/-- info: t.dyn:7:12: in a region nested in a contract of @m.f, the failure successor of %q.0 goes to propagate.0, which does not pass the failure on with base.error -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = demo.attempt ^fail.0() {
          body.0():
            %q.0 : base.Int = demo.div(%x.0, %y.0) ^propagate.0()
            %b.0 : base.Bool = demo.ge(%q.0, 0)
            %v.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
            ret(%v.0)
          propagate.0(%exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%x.0)
            ret(%err.0)
        }
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

-- A propagating block returns the result of its `base.error`.  This one applies `base.error` to
-- the failure, but returns the `ok(true)` that the failure successor passes to it.
#guard failing (withContract fun x y => Build.requires do
  withFailureBlock #[intT] (some false) fun fail => attempting fail do
    let prop ← freshLabel "propagate"
    let u ← emitApply (nm "u") exT Base.Except.ok.ref #[← emitConst (nm "t") (.bool true)]
    let q ← emitApply (nm "q") intT Demo.div.ref #[x, y] (succs := #[goto prop #[u]])
    let b ← emitApply (nm "b") boolT Demo.ge.ref #[q, ← emitConst (nm "zero") (.int 0)]
    finishBlock (.ret () (← emitApply (nm "v") exT Base.Except.ok.ref #[b]))
    let w ← freshVal (nm "w") exT
    let exc ← freshVal (nm "exc") intT
    startBlock prop #[w, exc]
    let _ ← emitApply (nm "err") exT Base.Except.error.ref #[exc.id]
    finishBlock (.ret () w.id)) == ["propagates"]

/-- info: t.dyn:8:12: in a region nested in a contract of @m.f, the failure successor of %q.0 goes to propagate.0, which does not return the result of its base.error -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = demo.attempt ^fail.0() {
          body.0():
            %u.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](true)
            %q.0 : base.Int = demo.div(%x.0, %y.0) ^propagate.0(%u.0)
            %b.0 : base.Bool = demo.ge(%q.0, 0)
            %v.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
            ret(%v.0)
          propagate.0(%w.0 : base.Except(base.Int, base.Bool), %exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%exc.0)
            ret(%w.0)
        }
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

/-! ### Only a region whose operation passes failures on may propagate

`if`, used at an `Except` type, returns the `error` of a propagating block as its value, and a
case instruction can then turn it into `true`.  So a propagating block is accepted only in a
region that may propagate. -/

-- A propagating block in a region of the generic `if`, used at an `Except` type.
#guard failing (withContract fun x y => Build.requires do
  let c ← emitApply (nm "c") boolT Demo.ge.ref #[x, y]
  let thn := region #[] (base := "then") do
    withPropagatingBlock intT boolT fun prop => okQuotNonNeg prop x y
  let els := region #[] (base := "else") do
    let t ← emitConst (nm "t") (.bool true)
    finishBlock (.ret () (← emitApply (nm "u") exT Base.Except.ok.ref #[t]))
  let v ← emitApply (nm "v") exT Demo.«if».ref #[c] (regions := #[thn, els])
  let isOk ← freshLabel "isOk"
  let isErr ← freshLabel "isErr"
  terminate Base.Except.case.ref #[v] (succs := #[goto isOk, goto isErr])
  finishBlock (.ret () (← Build.startBlockWith isOk (nm "r") boolT))
  let _ ← Build.startBlockWith isErr (nm "e") intT
  finishBlock (.ret () (← emitConst (nm "t") (.bool true)))) == ["propagates"]

/-- info: t.dyn:8:12: in a region nested in a contract of @m.f, the failure successor of %q.0 goes to propagate.0, but this region's operation does not pass failures on, so the failure must be unreachable -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %c.0 : base.Bool = demo.ge(%x.0, 0)
        %v.0 : base.Except(base.Int, base.Bool) = demo.if[base.Except(base.Int, base.Bool)](%c.0) {
          then.0():
            %q.0 : base.Int = demo.div(%x.0, %y.0) ^propagate.0()
            %b.0 : base.Bool = demo.ge(%q.0, 0)
            %w.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
            ret(%w.0)
          propagate.0(%exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%exc.0)
            ret(%err.0)
        } {
          else.0():
            %u.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](true)
            ret(%u.0)
        }
        base.Except.case[base.Int, base.Bool](%v.0) ^isOk.0() ^isErr.0()
      isOk.0(%r.0 : base.Bool):
        ret(%r.0)
      isErr.0(%e.0 : base.Int):
        ret(true)
    }")

-- A propagating block in the region of `try`, which has no failure successor.
/-- info: t.dyn:7:12: in a region nested in a contract of @m.f, the failure successor of %q.0 goes to propagate.0, but this region's operation does not pass failures on, so the failure must be unreachable -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %v.0 : base.Except(base.Int, base.Bool) = demo.try {
          body.0():
            %q.0 : base.Int = demo.div(%x.0, %y.0) ^propagate.0()
            %b.0 : base.Bool = demo.ge(%q.0, 0)
            %w.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
            ret(%w.0)
          propagate.0(%exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%exc.0)
            ret(%err.0)
        }
        base.Except.case[base.Int, base.Bool](%v.0) ^isOk.0() ^isErr.0()
      isOk.0(%r.0 : base.Bool):
        ret(%r.0)
      isErr.0(%e.0 : base.Int):
        ret(true)
    }")

-- A propagating block in the region of `guard`, whose failure successor is there, but whose
-- region's type is a variable, here an `Except` type.
/-- info: t.dyn:7:12: in a region nested in a contract of @m.f, the failure successor of %q.0 goes to propagate.0, but this region's operation does not pass failures on, so the failure must be unreachable -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %v.0 : base.Except(base.Int, base.Bool) = demo.guard[base.Except(base.Int, base.Bool)] ^fail.0() {
          body.0():
            %q.0 : base.Int = demo.div(%x.0, %y.0) ^propagate.0()
            %b.0 : base.Bool = demo.ge(%q.0, 0)
            %w.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
            ret(%w.0)
          propagate.0(%exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%exc.0)
            ret(%err.0)
        }
        base.Except.case[base.Int, base.Bool](%v.0) ^isOk.0() ^isErr.0()
      isOk.0(%r.0 : base.Bool):
        ret(%r.0)
      isErr.0(%e.0 : base.Int):
        ret(true)
      fail.0(%e.1 : base.Int):
        ret(false)
    }")

/-! ### Contract regions end their blocks in control flow -/

/-- A `requires` clause whose block `pre.0` ends with `tryDiv`, a terminal operation that may
fail, going on to `ok.0` or to `fail`. -/
private def tryDivIn (fail : Label) (x y : ValId) : BuildM E Unit Unit := do
  let ok ← freshLabel "ok"
  terminate Demo.tryDiv.ref #[x, y] (succs := #[goto ok, goto fail])
  let q ← Build.startBlockWith ok (nm "q") intT
  let zero ← emitConst (nm "zero") (.int 0)
  finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[q, zero]))

-- A terminal operation that may fail, in a clause's own blocks.
#guard failing (withContract fun x y => Build.requires do
  withFailureBlock #[intT] (some true) fun fail => tryDivIn fail x y) == ["terminators"]

/-- info: t.dyn:5:8: a contract region of @m.f ends pre.0 with demo.tryDiv; a contract region may end a block only with ret, jump, branch, unreachable or a case instruction -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        demo.tryDiv(%x.0, %y.0) ^ok.0() ^fail.0()
      ok.0(%q.0 : base.Int):
        %ok.0 : base.Bool = demo.ge(%q.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(true)
    }")

-- The same, in a region nested in a clause.
#guard failing (withContract fun x y => Build.requires do
  withFailureBlock #[intT] (some false) fun fail => attempting fail do
    let ok ← freshLabel "ok"
    let no ← freshLabel "no"
    terminate Demo.tryDiv.ref #[x, y] (succs := #[goto ok, goto no])
    let q ← Build.startBlockWith ok (nm "q") intT
    let ge ← emitApply (nm "b") boolT Demo.ge.ref #[q, ← emitConst (nm "zero") (.int 0)]
    finishBlock (.ret () (← emitApply (nm "v") exT Base.Except.ok.ref #[ge]))
    let _ ← Build.startBlockWith no (nm "e") intT
    let t ← emitConst (nm "t") (.bool true)
    finishBlock (.ret () (← emitApply (nm "v") exT Base.Except.ok.ref #[t]))) == ["terminators"]

/-- info: t.dyn:7:12: a contract region of @m.f ends body.0 with demo.tryDiv; a contract region may end a block only with ret, jump, branch, unreachable or a case instruction -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = demo.attempt ^fail.0() {
          body.0():
            demo.tryDiv(%x.0, %y.0) ^ok.0() ^no.0()
          ok.0(%q.0 : base.Int):
            %b.0 : base.Bool = demo.ge(%q.0, 0)
            %v.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
            ret(%v.0)
          no.0(%e.0 : base.Int):
            %v.1 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](true)
            ret(%v.1)
        }
        ret(%ok.0)
      fail.0(%e.1 : base.Int):
        ret(false)
    }")

/-- A `requires` clause that ends `pre.0` with `run`, a terminal operation with a region, whose
failure goes to a block that returns `false`. -/
private def runs : Built := withContract fun x y => Build.requires do
  let done ← freshLabel "done"
  let body := region #[] (base := "body") do
    let no ← freshLabel "no"
    let q ← emitApply (nm "q") intT Demo.div.ref #[x, y] (succs := #[goto no])
    finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[q, y]))
    let _ ← Build.startBlockWith no (nm "e") intT
    finishBlock (.ret () (← emitConst (nm "f") (.bool false)))
  terminate Demo.run.ref (succs := #[goto done]) (regions := #[body])
  let b ← Build.startBlockWith done (nm "b") boolT
  finishBlock (.ret () b)

-- The region of a terminator is nested in the clause, and may not propagate.  Its failure
-- breaks the rule for nested regions, and the terminator itself the rule for terminators.
#guard (Region.nestedList (funcOf runs).contract.regions).map (·.2) == [false]
#guard failing runs == ["propagates", "terminators"]

/-! ### Contract regions have no cycles -/

-- A clause with a loop.
#guard failing (withContract fun x _ => Build.requires do
  let loop ← freshLabel "loop"
  let done ← freshLabel "done"
  finishBlock (.jump () (goto loop #[x]))
  let n ← freshVal (nm "n") intT
  startBlock loop #[n]
  let ok ← emitApply (nm "ok") boolT Demo.ge.ref #[n.id, ← emitConst (nm "zero") (.int 0)]
  finishBlock (.branch () ok (goto done) (goto loop #[n.id]))
  startBlock done
  finishBlock (.ret () (← emitConst (nm "t") (.bool true)))) == ["acyclic"]

/-- info: t.dyn:6:6: a contract region of @m.f has a cycle through loop.0 -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        jump ^loop.0(%x.0)
      loop.0(%n.0 : base.Int):
        %ok.0 : base.Bool = demo.ge(%n.0, 0)
        branch(%ok.0) ^done.0() ^loop.0(%n.0)
      done.0():
        ret(true)
    }")

-- A cycle of two blocks, in a region nested in a clause.
/-- info: t.dyn:8:10: a contract region of @m.f has a cycle through a.0 -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = demo.attempt ^fail.0() {
          body.0():
            jump ^a.0()
          a.0():
            %c.0 : base.Bool = demo.ge(%x.0, %y.0)
            branch(%c.0) ^b.0() ^done.0()
          b.0():
            jump ^a.0()
          done.0():
            %v.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](true)
            ret(%v.0)
        }
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

/-! ## Acyclicity

`Body.Acyclic` decides by `Body.acyclicB`, which removes, round after round, the blocks that
transfer to no block left.  It rejects every body with a cycle (`Body.Acyclic.eq_nil`).  Compiled
code runs `Body.acyclicFast` in its place, Kahn's algorithm with its answer checked, so the
`#guard`s on `Body.Acyclic` below run that.  The last ones run the reference itself. -/

/-- A block labelled `l` that jumps to each of `ts`, by a terminator that this check does not
type. -/
private def jumps (l : String) (ts : List String) : Block E Unit :=
  { label := ⟨nm l⟩, params := #[], instrs := #[], info := ()
    term := .apply () Base.jump.ref ⟨#[], rfl⟩ #[] (ts.toArray.map fun t => goto ⟨nm t⟩) #[] }

#guard decide (Body.Acyclic ([] : List (Block E Unit)))
#guard decide (Body.Acyclic [jumps "a" ["b"], jumps "b" ["c"], jumps "c" []])
-- Listed against the order of the transfers, and a diamond.
#guard decide (Body.Acyclic [jumps "c" [], jumps "b" ["c"], jumps "a" ["b"]])
#guard decide (Body.Acyclic
  [jumps "a" ["b", "c"], jumps "d" [], jumps "b" ["d"], jumps "c" ["d"]])
-- A transfer to a label of no block is not an edge.
#guard decide (Body.Acyclic [jumps "a" ["x"]])
-- A loop of one block, a cycle of two, and a cycle that a block before it leads into.
#guard !decide (Body.Acyclic [jumps "a" ["a"]])
#guard !decide (Body.Acyclic [jumps "a" ["b"], jumps "b" ["a"]])
#guard !decide (Body.Acyclic [jumps "a" ["b"], jumps "b" ["c", "d"], jumps "c" ["b"], jumps "d" []])
-- Two blocks labelled `x`: a transfer to `x` is a transfer to both, so `a` and the second `x`
-- form a cycle.  Kahn's algorithm sends a transfer to the first `x` only, so its order fails its
-- check, and the reference check answers.
#guard !decide (Body.Acyclic [jumps "a" ["x"], jumps "x" [], jumps "x" ["a"]])

-- The reference check, `Body.peel`, gives the same answers.
/-- Whether `Body.peel`, run as `Body.acyclicB` runs it, removes every block. -/
private def peelsAll (bs : List (Block E Unit)) : Bool := (Body.peel bs.length bs).isEmpty

#guard peelsAll [jumps "c" [], jumps "b" ["c"], jumps "a" ["b"]]
#guard peelsAll [jumps "a" ["b", "c"], jumps "d" [], jumps "b" ["d"], jumps "c" ["d"]]
#guard !peelsAll [jumps "a" ["b"], jumps "b" ["c", "d"], jumps "c" ["b"], jumps "d" []]
#guard !peelsAll [jumps "a" ["x"], jumps "x" [], jumps "x" ["a"]]
-- What it leaves of a body with a cycle: the cycle, and the block that leads into it.
#guard (Body.peel 4 [jumps "a" ["b"], jumps "b" ["c", "d"], jumps "c" ["b"], jumps "d" []]).map
    (·.label) == [⟨nm "a"⟩, ⟨nm "b"⟩, ⟨nm "c"⟩]

end Strata.Dyn.ContractRegionTest
