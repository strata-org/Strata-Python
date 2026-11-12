/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataDyn.Build
public import StrataDyn.Build.Typed
public import StrataDyn.DDM
public import StrataDyn.DDMRead
public import StrataDyn.Traverse
import StrataDyn.Env.WF
import StrataDyn.DSL
import StrataDynTest.WFParts
-- The builder, the checker, the printer and the reader run as compiled code below.
meta import StrataDyn.Build
meta import StrataDyn.Build.Typed
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.Traverse
meta import StrataDyn.WF
meta import StrataDyn.Env.WF
meta import StrataDynTest.WFParts

set_option autoImplicit false

/-!
# Loop invariants

A loop invariant is an application of `base.loopInvariant` at the start of a block, usually a
loop's head.  Its region returns a `base.Bool`, and the rules for contract regions apply to it,
with failure value `false`.  The rules of `Func.LoopInvariantsWF`, by the names that
`WFParts.broken` gives them:

* `invariants first`: in every block, at any depth, the invariants come before every other
  instruction, constants included;
* `invariant results`: no instruction uses an invariant's result;
* `invariant place`: no contract region and no invariant's region holds an invariant;
* `invariant writes`, `invariant failures`, `invariant propagates`, `invariant terminators`,
  `invariant acyclic`: an invariant's region applies no operation declared `writes`, sends the
  failures of its own blocks to a failure block that gives `false` or ends in `unreachable`, its
  nested regions pass their failures on, its blocks end in control flow, and they are acyclic.

The body names no ghost, invariants included (`ghosts`), and only an `ensures` clause applies
`base.old` (`old`).  A ghost's regions hold no invariant (`Ghost.WF`).

Each function accepted here reads back unchanged, and some stay well formed when their invariants
are dropped.  For each function rejected here, the reader names the rule that it breaks.
-/

namespace Strata.Dyn.LoopInvariantTest

open Strata.Dyn.WFParts (broken failing)

/-- Integer operations, one that may fail, one that writes, and operations that run regions, one
of them a terminator. -/
public environment Demo extends Base where
  namespace demo
  open base
  /-- `lhs ≥ rhs`. -/
  pure insn ge (lhs rhs : Int) : Bool
  /-- `lhs < rhs`. -/
  pure insn lt (lhs rhs : Int) : Bool
  /-- `lhs + rhs`. -/
  pure insn add (lhs rhs : Int) : Int
  /-- `a / b`.  It fails, with an error code, when `b` is zero. -/
  calls insn div (a b : Int) (^err (e : Int)) : Int
  /-- Writes `value` to a log. -/
  writes insn log (value : Int) : Unit
  /-- Runs `body`: the value of an `ok`, or a transfer to `err` with the error of an `error`. -/
  pure insn attempt (&body : Except Int Bool) (^err (e : Int)) : Bool
  /-- Runs `body`, and returns what it returns, an `error` included, as a value. -/
  pure insn «try» (&body : Except Int Bool) : Except Int Bool
  /-- Runs `body` once, and returns its value. -/
  pure insn once (&body : Int) : Int
  /-- `a / b`, which ends its block: it continues at `ok` with the quotient, or at `err` when `b`
  is zero. -/
  pure terminal insn tryDiv (a b : Int) (^ok (q : Int)) (^err (e : Int))
  /-- Ends its block: runs `body`, and continues at `k` with the value that `body` returns. -/
  pure terminal insn run (&body : Bool) (^k (b : Bool))
  end demo

open Strata.Dyn.Build (freshVal emitConst emitApply finishBlock build FailedFunc loopInvariant)
open Strata.Dyn.Build.Raw (startBlock startFreshBlock freshLabel goto jump branch)

private abbrev E := Demo.env

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF}

private def intT : TypeExpr E := Base.Int
private def boolT : TypeExpr E := Base.Bool

private def nm (s : String) : Name := .str .base s

/-- Read `text` in `Demo.env`, and print the module if it reads back differently, or the
diagnostics. -/
private def readBack (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m => unless toString m == text do IO.println m

/-- Read `text` in `Demo.env` and print the diagnostics, or that it was read. -/
private def readErrors (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok _ => IO.println "read"

/-- Print the built function as a module, or why it was not built. -/
private def printBuilt (b : Built) : IO Unit := do
  match b with
  | .error e => IO.println s!"not built: {broken e.func} {e.misuses}"
  | .ok f =>
    match Module.ofChecked (nm "m") #[f] () with
    | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"
    | .ok m => IO.println m

/-! ## The instruction -/

#guard (Base.loopInvariant.sig (e := E)).effect == .pure
#guard (Base.loopInvariant.sig (e := E)).mayPropagate == [false]
#guard (Base.loopInvariant.sig (e := E)).succs.isEmpty

/-! ## The builder

`@m.count(n)` counts `i` from `0` up to `n`, with the invariant `i ≥ 0` at the loop's head. -/

/-- `@m.count`, with the invariants that `invs i` emits at the start of the head. -/
private def counting (invs : ValId → BuildM E Unit Unit) : Built :=
  build (.str (nm "m") "count") intT () do
    let n ← freshVal (nm "n") intT
    let _ ← startFreshBlock #[n] "entry"
    let head ← freshLabel "head"
    let body ← freshLabel "body"
    let done ← freshLabel "done"
    let zero ← emitConst (nm "zero") (.int 0)
    jump ⟨head, #[zero]⟩
    let i ← freshVal (nm "i") intT
    startBlock head #[i]
    invs i.id
    let c ← emitApply (nm "c") boolT Demo.lt.ref #[i.id, n.id]
    branch c ⟨body, #[]⟩ ⟨done, #[]⟩
    startBlock body #[]
    let one ← emitConst (nm "one") (.int 1)
    let j ← emitApply (nm "j") intT Demo.add.ref #[i.id, one]
    jump ⟨head, #[j]⟩
    startBlock done #[]
    finishBlock (.ret () i.id)

/-- `i ≥ 0`. -/
private def nonNeg (i : ValId) : BuildM E Unit Unit :=
  loopInvariant #[intT] fun _ => do
    let zero ← emitConst (nm "zero") (.int 0)
    finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[i, zero]))

/-- info: module m {
  func @m.count(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %c.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%c.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      jump ^head.0(%j.0)
    done.0():
      ret(%i.0)
  }
} -/
#guard_msgs in
#eval printBuilt (counting nonNeg)

#guard failing (counting nonNeg) == []
#guard (counting nonNeg).toOption.any (decide ·.val.Canonical)

/-- `0 ≤ n / i`, whose failure, when `i` is zero, goes to the failure block that the builder
makes. -/
private def quotNonNeg (n : ValId) (i : ValId) : BuildM E Unit Unit :=
  loopInvariant #[intT] fun fail => do
    let q ← emitApply (nm "q") intT Demo.div.ref #[n, i] (succs := #[goto fail])
    let zero ← emitConst (nm "zero") (.int 0)
    finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[q, zero]))

/-- info: module m {
  func @m.count(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %inv.1 : base.Unit = base.loopInvariant {
        inv.1():
          %q.0 : base.Int = demo.div(%n.0, %i.0) ^fail.1()
          %ok.1 : base.Bool = demo.ge(%q.0, 0)
          ret(%ok.1)
        fail.1(%e.0 : base.Int):
          ret(false)
      }
      %c.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%c.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      jump ^head.0(%j.0)
    done.0():
      ret(%i.0)
  }
} -/
#guard_msgs in
#eval printBuilt (counting fun i => do nonNeg i; quotNonNeg ⟨0⟩ i)

/-- `0 ≤ n / i` again, emitted with the typed `Emit.loopInvariant`, whose failure block comes as
a target that takes the failure's code. -/
private def quotNonNegTyped (n : ValId) (i : ValId) : BuildM E Unit Unit :=
  Emit.loopInvariant [intT] fun fail => do
    let q ← emitApply (nm "q") intT Demo.div.ref #[n, i] (succs := #[← Build.checkedTarget fail])
    let zero ← emitConst (nm "zero") (.int 0)
    finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[q, zero]))

/-- info: module m {
  func @m.count(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %q.0 : base.Int = demo.div(%n.0, %i.0) ^fail.0()
          %ok.0 : base.Bool = demo.ge(%q.0, 0)
          ret(%ok.0)
        fail.0(%e.0 : base.Int):
          ret(false)
      }
      %c.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%c.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      jump ^head.0(%j.0)
    done.0():
      ret(%i.0)
  }
} -/
#guard_msgs in
#eval printBuilt (counting (quotNonNegTyped ⟨0⟩))

/-- `i ≥ 0`, emitted with `Emit.loopInvariant` from a front end's monad over the builder, here one
that counts the invariants it emits. -/
private def nonNegCounted (i : ValId) : StateT Nat (BuildM E Unit) Unit :=
  Emit.loopInvariant [intT] fun _ => do
    modify (· + 1)
    liftBuild do
      let zero ← emitConst (nm "zero") (.int 0)
      finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[i, zero]))

/-- The built function, printed as a module, or nothing if it was not built. -/
private def printed (b : Built) : Option String :=
  b.toOption.bind fun f => (Module.ofChecked (nm "m") #[f] ()).toOption.map toString

-- The front end's monad runs the body: the count is 1, and the function is the one that `nonNeg`
-- gives.
private def counted : Built :=
  counting fun i => do
    let (_, k) ← (nonNegCounted i).run 0
    unless k == 1 do Build.error s!"counted {k}"

#guard failing counted == []
#guard (printed counted).isSome && printed counted == printed (counting nonNeg)

-- An invariant after another instruction of its block is a misuse of the builder.
/-- info: not built: [invariants first] #[a loop invariant after another instruction of its block] -/
#guard_msgs in
#eval printBuilt (counting fun i => do
  discard <| emitConst (nm "k") (.int 1)
  nonNeg i)

/-! ## What the rules accept

Every function here reads back unchanged. -/

/-- `@m.count` with `inv` as the first lines of its head, and `rest` as the head's other
instructions. -/
private def countText (inv : String) (rest : String := "") : String := s!"module m \{
  func @m.count(%n.0 : base.Int) -> base.Int \{
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
{inv}{rest}      %c.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%c.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      jump ^head.0(%j.0)
    done.0():
      ret(%i.0)
  }
}
"

/-- The invariant `i ≥ 0`, named `inv.k`, with result `%inv.k` and value `%ok.k`. -/
private def geZero (k : Nat) : String := s!"      %inv.{k} : base.Unit = base.loopInvariant \{
        inv.{k}():
          %ok.{k} : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.{k})
      }
"

/-- `@m.f(n)`, whose entry block ends in `demo.run`, with `inv` as the first lines of the block of
its region. -/
private def runText (inv : String) : String := s!"module m \{
  func @m.f(%n.0 : base.Int) -> base.Int \{
    entry.0(%n.0 : base.Int):
      demo.run ^k.0() \{
        r.0():
{inv}          ret(true)
      }
    k.0(%b.0 : base.Bool):
      ret(%n.0)
  }
}
"

#guard_msgs in
#eval readBack (countText (geZero 0))

-- Two invariants, and an invariant whose region ends in `unreachable`, which is accepted: a
-- consumer reads it as an ill-defined region, never as `assume(false)`.
#guard_msgs in
#eval readBack (countText (geZero 0 ++ geZero 1 ++ "      %inv.2 : base.Unit = base.loopInvariant {
        inv.2():
          unreachable
      }
"))

-- An invariant in a block that is not a loop's head: the function's entry block.
#guard_msgs in
#eval readBack "module m {
  func @m.f(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%x.0, 0)
          ret(%ok.0)
      }
      ret(%x.0)
  }
}
"

-- Nested loops, each with an invariant at its head; the inner one sees the outer head's
-- parameter.
#guard_msgs in
#eval readBack "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^outer.0(0)
    outer.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %c.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%c.0) ^inner.0(0) ^done.0()
    inner.0(%k.0 : base.Int):
      %inv.1 : base.Unit = base.loopInvariant {
        inv.1():
          %ok.1 : base.Bool = demo.ge(%k.0, 0)
          %ok.2 : base.Bool = demo.lt(%i.0, %n.0)
          ret(%ok.2)
      }
      %d.0 : base.Bool = demo.lt(%k.0, %i.0)
      branch(%d.0) ^step.0() ^next.0()
    step.0():
      %k.1 : base.Int = demo.add(%k.0, 1)
      jump ^inner.0(%k.1)
    next.0():
      %i.1 : base.Int = demo.add(%i.0, 1)
      jump ^outer.0(%i.1)
    done.0():
      ret(%i.0)
  }
}
"

/-- A loop inside a region of the body, with an invariant at its head that reads a cell. -/
private def onceLoop := "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%n.0)
      %r.0 : base.Int = demo.once {
        once.0():
          jump ^head.0(0)
        head.0(%i.0 : base.Int):
          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %v.0 : base.Int = base.refGet[base.Int](%c.0)
              %ok.0 : base.Bool = demo.ge(%v.0, %i.0)
              ret(%ok.0)
          }
          %d.0 : base.Bool = demo.lt(%i.0, %n.0)
          branch(%d.0) ^body.0() ^done.0()
        body.0():
          %j.0 : base.Int = demo.add(%i.0, 1)
          jump ^head.0(%j.0)
        done.0():
          ret(%i.0)
      }
      ret(%r.0)
  }
}
"

#guard_msgs in
#eval readBack onceLoop

-- A region nested in an invariant passes its failure on with `base.error`.
#guard_msgs in
#eval readBack (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.attempt ^fail.0() {
            try.0():
              %q.0 : base.Int = demo.div(%n.0, %i.0) ^propagate.0()
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
")

-- An invariant in a block of a terminator's region.
#guard_msgs in
#eval readBack (runText "          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %ok.0 : base.Bool = demo.ge(%n.0, 0)
              ret(%ok.0)
          }
")

/-- Read `text`, and print, for each function, whether it is well formed and how many invariants it
has, at any depth, before and after every invariant is dropped. -/
private def withoutInvariants (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    for f in m.raw.funcs do
      let drop (b : Block E Info) : Id (List (Block E Info)) :=
        pure [{ b with instrs := b.instrs.filter (!·.isLoopInvariant) }]
      let g : Func E Info :=
        { f with blocks := (Id.run (Block.traverseBlocksList drop f.blocks.toList)).toArray }
      let name := ToDDM.nameText f.name
      IO.println s!"{name}: {decide f.WF}, {f.invariantRegions.length} invariants; \
        without them: {decide g.WF}, {g.invariantRegions.length}"

-- No instruction uses an invariant's result, so dropping the invariants leaves a function well
-- formed: two invariants at a loop's head, one in a terminator's region, and one at the head of a
-- loop inside a region of the body.
/--
info: m.count: true, 2 invariants; without them: true, 0
m.f: true, 1 invariants; without them: true, 0
m.f: true, 1 invariants; without them: true, 0
-/
#guard_msgs in
#eval do
  withoutInvariants (countText (geZero 0 ++ geZero 1))
  withoutInvariants (runText "          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %ok.0 : base.Bool = demo.ge(%n.0, 0)
              ret(%ok.0)
          }
")
  withoutInvariants onceLoop

/-! ## What the rules reject -/

-- `invariants first`: an invariant after another instruction.  The builder's test above shows
-- that a constant before it counts too.
/-- info: t.dyn:5:4: base.loopInvariant must come before every other instruction of its block, but head.0 of @m.count has one after another instruction -/
#guard_msgs in
#eval readErrors (countText "" (rest := "      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
" ++ geZero 0))

-- `invariant results`: a second invariant uses the first one's result.
/-- info: t.dyn:12:10: @m.count uses %inv.0, the result of a loop invariant -/
#guard_msgs in
#eval readErrors (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          ret(true)
      }
      %inv.1 : base.Unit = base.loopInvariant {
        inv.1():
          %r.0 : base.Ref(base.Unit) = base.refNew[base.Unit](%inv.0)
          ret(true)
      }
")

-- `invariant results`: the code after the invariants uses one's result.
/-- info: t.dyn:10:6: @m.count uses %inv.0, the result of a loop invariant -/
#guard_msgs in
#eval readErrors (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          ret(true)
      }
" (rest := "      %r.0 : base.Ref(base.Unit) = base.refNew[base.Unit](%inv.0)
"))

-- `invariant results`: a terminator passes an invariant's result.
/-- info: t.dyn:8:6: @m.f uses %inv.0, the result of a loop invariant -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f() -> base.Unit {
    entry.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          ret(true)
      }
      ret(%inv.0)
  }
}
"

-- `invariant place`: an invariant in a `requires` clause, and one in another invariant.
/-- info: t.dyn:5:8: base.loopInvariant is allowed only in a body, but @m.f uses it in its contract -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %inv.0 : base.Unit = base.loopInvariant {
          inv.0():
            ret(true)
        }
        ret(true)
    }
  {
    entry.0(%x.0 : base.Int):
      ret(%x.0)
  }
}
"
/-- info: t.dyn:8:10: a loop invariant of @m.count holds another loop invariant -/
#guard_msgs in
#eval readErrors (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %inv.1 : base.Unit = base.loopInvariant {
            inv.1():
              ret(true)
          }
          ret(true)
      }
")

-- `invariant writes`: an invariant that writes.
/-- info: t.dyn:8:10: a loop invariant of @m.count applies demo.log, which is declared writes -/
#guard_msgs in
#eval readErrors (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %u.0 : base.Unit = demo.log(%i.0)
          ret(true)
      }
")

-- `invariant failures`: a failure that gives `true`.
/-- info: t.dyn:8:10: in a loop invariant of @m.count, the failure successor of %q.0 goes to fail.0, which returns true; a failure must give false or be unreachable -/
#guard_msgs in
#eval readErrors (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %q.0 : base.Int = demo.div(%n.0, %i.0) ^fail.0()
          %ok.0 : base.Bool = demo.ge(%q.0, 0)
          ret(%ok.0)
        fail.0(%e.0 : base.Int):
          ret(true)
      }
")

-- `invariant propagates`: a nested region that turns its failure into a value.
/-- info: t.dyn:10:14: in a region nested in a contract of @m.count, the failure successor of %q.0 goes to caught.0, which does not pass the failure on with base.error -/
#guard_msgs in
#eval readErrors (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.attempt ^fail.0() {
            try.0():
              %q.0 : base.Int = demo.div(%n.0, %i.0) ^caught.0()
              %v.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](true)
              ret(%v.0)
            caught.0(%exc.0 : base.Int):
              %w.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](true)
              ret(%w.0)
          }
          ret(%ok.0)
        fail.0(%e.0 : base.Int):
          ret(false)
      }
")

-- `invariant terminators`: a block that ends in an operation that may fail.
/-- info: t.dyn:8:10: a contract region of @m.count ends inv.0 with demo.tryDiv; a contract region may end a block only with ret, jump, branch, unreachable or a case instruction -/
#guard_msgs in
#eval readErrors (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          demo.tryDiv(%n.0, %i.0) ^ok.0() ^bad.0()
        ok.0(%q.0 : base.Int):
          ret(true)
        bad.0(%e.0 : base.Int):
          ret(false)
      }
")

-- `invariant acyclic`: a cycle in an invariant.
/-- info: t.dyn:9:8: a contract region of @m.count has a cycle through spin.0 -/
#guard_msgs in
#eval readErrors (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          jump ^spin.0()
        spin.0():
          jump ^spin.0()
      }
")

-- `old`: an invariant does not read the state at the call yet.
/-- info: t.dyn:8:10: base.old is allowed only in an ensures clause, but @m.count uses it in its body -/
#guard_msgs in
#eval readErrors (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
            old.0():
              %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%n.0)
              ret(%w.0)
          }
          %ok.0 : base.Bool = demo.ge(%o.0, %i.0)
          ret(%ok.0)
        fail.0(%e.0 : base.Int):
          ret(false)
      }
")

-- `ghosts`: an invariant does not name a ghost; and a ghost's invariant holds no loop invariant.
/-- info: t.dyn:10:50: @m.f uses ghost @m.g outside its contract -/
#guard_msgs in
#eval readErrors "module m {
  ghost @m.g : base.Int = {
    init.0():
      ret(0)
  }
  func @m.f(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %v.0 : base.Int = base.refGet[base.Int](ghost @m.g)
          %ok.0 : base.Bool = demo.ge(%v.0, 0)
          ret(%ok.0)
      }
      ret(%x.0)
  }
}
"
/-- info: t.dyn:4:6: base.loopInvariant is allowed only in a body, but ghost @m.g uses it -/
#guard_msgs in
#eval readErrors "module m {
  ghost @m.g : base.Int = {
    init.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          ret(true)
      }
      ret(0)
  }
}
"

/-! ## More places where an invariant is rejected -/

-- `invariant place`: an invariant in an `ensures` clause.
/-- info: t.dyn:5:8: base.loopInvariant is allowed only in a body, but @m.f uses it in its contract -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%x.0 : base.Int) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %inv.0 : base.Unit = base.loopInvariant {
          inv.0():
            ret(true)
        }
        ret(true)
    }
  {
    entry.0(%x.0 : base.Int):
      ret(%x.0)
  }
}
"

-- `invariant place`: an invariant in a `writes` frame region.
/-- info: t.dyn:5:8: base.loopInvariant is allowed only in a body, but @m.f uses it in its contract -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int
    writes({
      loc.0():
        %inv.0 : base.Unit = base.loopInvariant {
          inv.0():
            ret(true)
        }
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.0)
    })
  {
    entry.0(%c.0 : base.Ref(base.Int)):
      ret(0)
  }
}
"

-- `invariant place`: an invariant in an `old` region of an `ensures` clause.
/-- info: t.dyn:7:12: base.loopInvariant is allowed only in a body, but @m.f uses it in its contract -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%x.0 : base.Int) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %inv.0 : base.Unit = base.loopInvariant {
              inv.0():
                ret(true)
            }
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
            ret(%w.0)
        }
        ret(true)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%x.0 : base.Int):
      ret(%x.0)
  }
}
"

-- `invariant place`: an invariant in a region nested in another invariant.
/-- info: t.dyn:10:14: a loop invariant of @m.count holds another loop invariant -/
#guard_msgs in
#eval readErrors (countText "      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %v.0 : base.Int = demo.once {
            once.0():
              %inv.1 : base.Unit = base.loopInvariant {
                inv.1():
                  ret(true)
              }
              ret(%i.0)
          }
          ret(true)
      }
")

-- `invariants first`, at depth: an invariant after another instruction in a block of a region
-- of the body.
/-- info: t.dyn:5:8: base.loopInvariant must come before every other instruction of its block, but once.0 of @m.f has one after another instruction -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %r.0 : base.Int = demo.once {
        once.0():
          %k.0 : base.Int = demo.add(%n.0, 1)
          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              ret(true)
          }
          ret(%k.0)
      }
      ret(%r.0)
  }
}
"

-- `invariant writes` and `invariant failures` in a terminator's region: an invariant there that
-- writes, and one whose failure gives `true`.
/-- info: t.dyn:8:14: a loop invariant of @m.f applies demo.log, which is declared writes -/
#guard_msgs in
#eval readErrors (runText "          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %u.0 : base.Unit = demo.log(%n.0)
              ret(true)
          }
")
/-- info: t.dyn:8:14: in a loop invariant of @m.f, the failure successor of %q.0 goes to fail.0, which returns true; a failure must give false or be unreachable -/
#guard_msgs in
#eval readErrors (runText "          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %q.0 : base.Int = demo.div(%n.0, %n.0) ^fail.0()
              %ok.0 : base.Bool = demo.ge(%q.0, 0)
              ret(%ok.0)
            fail.0(%e.0 : base.Int):
              ret(true)
          }
")

-- A ghost's invariant holds no loop invariant.
/-- info: t.dyn:7:6: base.loopInvariant is allowed only in a body, but ghost @m.g uses it -/
#guard_msgs in
#eval readErrors "module m {
  ghost @m.g : base.Int = {
    init.0():
      ret(0)
  } invariant {
    gi.0(%v.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          ret(true)
      }
      ret(true)
  }
}
"

end Strata.Dyn.LoopInvariantTest
