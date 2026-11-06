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
# `old` in `ensures` clauses

`base.old` runs its region in the state at the call.  Two rules of `Func.OldWF` say where it may
be and what its region may see:

* `old`: it appears only in an `ensures` clause, at any depth, never in the body or in a
  `requires` clause;
* `old scope`: an `old` region sees only the function's parameters, constants, the parameters of
  the regions that enclose it, and its own values.  An `old` nested in an `old` also sees the
  values of the enclosing `old` region, since both run in the state at the call.

The rules for contract regions apply to an `old` region as to any region nested in a clause: it
applies no operation declared `writes`, and passes its failures on with `base.error`.

Each function accepted here is built, printed, and read back unchanged.  Each function rejected
here breaks exactly one rule of `Func.WF`, and the reader names the problem.
-/

namespace Strata.Dyn.OldTest

open Strata.Dyn.WFParts (broken failing)

/-- A comparison, an operation that may fail, a quantifier, an `if`, a binding and a terminal
operation with a region. -/
public environment Demo extends Base where
  namespace demo
  open base
  /-- `lhs ≥ rhs`. -/
  pure insn ge (lhs rhs : Int) : Bool
  /-- `a / b`.  It fails, with an error code, when `b` is zero. -/
  calls insn div (a b : Int) (^err (e : Int)) : Int
  /-- Whether `body` returns `ok(true)` for every element `x` of `xs`.  An `error` that it
  returns transfers to `err` with its error. -/
  pure insn every (xs : Sequence Int) (&body (x : Int) : Except Int Bool) (^err (e : Int)) : Bool
  /-- Run `then` if `cond` holds, else `else`. -/
  pure insn «if» [a] (cond : Bool) (&«then» &«else» : a) : a
  /-- Runs `body` with `x` bound to `v`, and returns what it returns. -/
  pure insn bind [a b] (v : a) (&body (x : a) : b) : b
  /-- Runs `body`, which ends its block, and continues at `k` with its value. -/
  pure terminal insn run (&body : Bool) (^k (b : Bool))
  end demo

open Strata.Dyn.Build (freshVal emitConst emitApply finishBlock terminate build FailedFunc region
  withFailureBlock withPropagatingBlock)
open Strata.Dyn.Build.Raw (startBlock startFreshBlock freshLabel goto)

private abbrev E := Demo.env

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF}

private def intT : TypeExpr E := Base.Int
private def boolT : TypeExpr E := Base.Bool
private def cellT : TypeExpr E := Base.Ref intT
private def seqT : TypeExpr E := Base.Sequence intT
/-- `base.Except(base.Int, base.Int)`, what an `old` region of `base.Int` returns. -/
private def exIntT : TypeExpr E := Base.Except intT intT
/-- `base.Except(base.Int, base.Bool)`, what the region of `demo.every` returns. -/
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

/-- Read `text` in `Demo.env`, and print the diagnostics, or the module if it prints otherwise. -/
private def readBack (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m => unless toString m == text do IO.println m

/-! ## Builders -/

/-- `@m.f(c, xs) = 0`, over the cell `c` and the sequence `xs`, with the contract that
`contract c xs` emits after the body. -/
private def withContract (contract : ValId → ValId → BuildM E Unit Unit) : Built :=
  build (.str (nm "m") "f") intT () do
    let c ← freshVal (nm "c") cellT
    let xs ← freshVal (nm "xs") seqT
    let _ ← startFreshBlock #[c, xs] "entry"
    finishBlock (.ret () (← emitConst (nm "z") (.int 0)))
    contract c.id xs.id

/-- The extern `@m.g(c) -> base.Int`, with the contract that `contract c` emits. -/
private def externWith (contract : ValId → BuildM E Unit Unit) : Built :=
  Build.buildExtern (.str (nm "m") "g") #[(nm "c", cellT)] intT () fun ps => do
    if let some c := ps[0]? then contract c

/-- An `old` region of `base.Int` that returns `ok(v)`. -/
private def okInt (v : ValId) : BuildM E Unit Unit := do
  finishBlock (.ret () (← emitApply (nm "w") exIntT Base.Except.ok.ref #[v]))

/-- `old(refGet(c))`, named `o`, with the failure of `old` going to `err`. -/
private def oldGet (err : Label) (c : ValId) : BuildM E Unit ValId :=
  Build.old (nm "o") intT intT err fun _ => do
    okInt (← emitApply (nm "v") intT Base.refGet.ref #[c])

/-- `r ≥ o`, returned. -/
private def retGe (r o : ValId) : BuildM E Unit Unit := do
  finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[r, o]))

/-- An `ensures` clause, `r ≥ o` with `o` what `old` gives, whose failures give `false`. -/
private def ensuresGe (old : Label → ValId → BuildM E Unit ValId) : BuildM E Unit Unit :=
  Build.ensures (nm "r") intT fun r =>
    withFailureBlock #[intT] (some false) fun fail => do retGe r (← old fail r)

/-- An `ensures` clause, `every(xs, x => ok(o ≥ x))` with `o` what `old x prop` gives, `prop`
the label of the propagating block of the region of `every`.  Its failures give `false`. -/
private def ensuresEvery (xs : ValId) (old : ValId → Label → BuildM E Unit ValId) :
    BuildM E Unit Unit :=
  Build.ensures (nm "r") intT fun _ =>
    withFailureBlock #[intT] (some false) fun fail => do
      let body : BuildM E Unit (Region E Unit) := do
        let x ← freshVal (nm "x") intT
        region #[x] (base := "body") do
          withPropagatingBlock intT boolT fun prop => do
            let o ← old x.id prop
            let b ← emitApply (nm "b") boolT Demo.ge.ref #[o, x.id]
            finishBlock (.ret () (← emitApply (nm "u") exT Base.Except.ok.ref #[b]))
      finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.every.ref #[xs] (succs := #[goto fail])
        (regions := #[body])))

/-- The parameters of the regions that enclose each outermost `old` region of each `ensures`
clause of a built function. -/
private def oldSites (b : Built) : Option (List (List ValId)) :=
  b.toOption.map fun f => f.val.contract.ensures.toList.flatMap fun c =>
    (Block.oldRegionsList [] c.region.blocks.toList).map (·.2)

/-- `@m.f(c, xs) -> base.Int` with the contract `clauses`, returning `0`. -/
private def withClauses (clauses : String) : String := s!"module m \{
  func @m.f(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)) -> base.Int
{clauses}
  \{
    entry.0(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)):
      ret(0)
  }
}
"

/-! ## What the rules accept -/

/-- `old` over a read of a parameter: the result is at least the cell's contents at the call. -/
private def oldParam : Built := withContract fun c _ => ensuresGe fun fail _ => oldGet fail c

private def oldParamText : String := "module m {
  func @m.f(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)):
      ret(0)
  }
}
"

#guard failing oldParam == []
#guard oldParam.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees oldParam oldParamText

-- `base.old` is a `reads` operation, and its region may propagate: it declares a failure
-- successor and an `Except` region.
#guard (Base.old.sig (e := E)).effect == .reads
#guard (Base.old.sig (e := E)).mayPropagate == [true]

/-- `old` inside the region of `every`, which uses the region's parameter `x`: for every `x` of
`xs`, the cell's contents at the call, divided by `x`, are at least `x`.  A failure of the
division passes through the `old` region and the region of `every` to the clause's failure
block. -/
private def oldBinder : Built := withContract fun c xs => ensuresEvery xs fun x prop =>
  Build.old (nm "o") intT intT prop fun p => do
    let v ← emitApply (nm "v") intT Base.refGet.ref #[c]
    okInt (← emitApply (nm "d") intT Demo.div.ref #[v, x] (succs := #[goto p]))

private def oldBinderText : String := "module m {
  func @m.f(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %ok.0 : base.Bool = demo.every(%xs.0) ^fail.0() {
          body.0(%x.0 : base.Int):
            %o.0 : base.Int = base.old[base.Int, base.Int] ^propagate.0() {
              old.0():
                %v.0 : base.Int = base.refGet[base.Int](%c.0)
                %d.0 : base.Int = demo.div(%v.0, %x.0) ^propagate.1()
                %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%d.0)
                ret(%w.0)
              propagate.1(%exc.0 : base.Int):
                %err.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%exc.0)
                ret(%err.0)
            }
            %b.0 : base.Bool = demo.ge(%o.0, %x.0)
            %u.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
            ret(%u.0)
          propagate.0(%exc.1 : base.Int):
            %err.1 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%exc.1)
            ret(%err.1)
        }
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)):
      ret(0)
  }
}
"

#guard failing oldBinder == []
#guard oldBinder.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees oldBinder oldBinderText

/-- `old` nested in `old`: the inner one runs in the state at the call too. -/
private def oldInOld : Built := withContract fun c _ =>
  ensuresGe fun fail _ => Build.old (nm "o") intT intT fail fun p => do okInt (← oldGet p c)

private def oldInOldText : String := "module m {
  func @m.f(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %o.1 : base.Int = base.old[base.Int, base.Int] ^propagate.0() {
              old.1():
                %v.0 : base.Int = base.refGet[base.Int](%c.0)
                %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
                ret(%w.0)
            }
            %w.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%o.1)
            ret(%w.1)
          propagate.0(%exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%exc.0)
            ret(%err.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)):
      ret(0)
  }
}
"

#guard failing oldInOld == []
#guard oldInOld.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees oldInOld oldInOldText

-- Only the outermost `old` regions are checked, each with the parameters of the regions nested in
-- the clause that enclose it: `%x.0`, value 5, for the `old` in the region of `every`, and none
-- for the `old` that holds another.
#guard oldSites oldBinder == some [[⟨5⟩]]
#guard oldSites oldInOld == some [[]]

/-- An `old` nested in an `old` that uses a value of the enclosing `old` region, which that
region computes in the state at the call. -/
private def oldUsesOld : Built := withContract fun c _ =>
  ensuresGe fun fail _ => Build.old (nm "o") intT intT fail fun p => do
    let v ← emitApply (nm "v") intT Base.refGet.ref #[c]
    okInt (← Build.old (nm "i") intT intT p fun _ => okInt v)

private def oldUsesOldText : String := "module m {
  func @m.f(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %i.0 : base.Int = base.old[base.Int, base.Int] ^propagate.0() {
              old.1():
                %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
                ret(%w.0)
            }
            %w.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%i.0)
            ret(%w.1)
          propagate.0(%exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%exc.0)
            ret(%err.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)):
      ret(0)
  }
}
"

#guard failing oldUsesOld == []
#guard oldUsesOld.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees oldUsesOld oldUsesOldText

-- So may an `old` nested in a region nested in an `old`, and it may use that region's parameter.
#guard_msgs in
#eval readBack "module m {
  func @m.f(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Bool = base.old[base.Int, base.Bool] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %a.0 : base.Bool = demo.every(%xs.0) ^propagate.0() {
              body.0(%x.0 : base.Int):
                %i.0 : base.Bool = base.old[base.Int, base.Bool] ^no.0() {
                  old.1():
                    %b.0 : base.Bool = demo.ge(%v.0, %x.0)
                    %u.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
                    ret(%u.0)
                }
                %u.1 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%i.0)
                ret(%u.1)
              no.0(%e.1 : base.Int):
                unreachable
            }
            %u.2 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%a.0)
            ret(%u.2)
          propagate.0(%exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%exc.0)
            ret(%err.0)
        }
        ret(%o.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)):
      ret(0)
  }
}
"

/-- An `old` region that uses a constant that the clause defines outside it: a constant is the
same in every state. -/
private def oldUsesConst : Built := withContract fun c _ =>
  ensuresGe fun fail _ => do
    let one ← emitConst (nm "one") (.int 1)
    Build.old (nm "o") intT intT fail fun p => do
      let v ← emitApply (nm "v") intT Base.refGet.ref #[c]
      okInt (← emitApply (nm "d") intT Demo.div.ref #[v, one] (succs := #[goto p]))

private def oldUsesConstText : String := "module m {
  func @m.f(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %d.0 : base.Int = demo.div(%v.0, 1) ^propagate.0()
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%d.0)
            ret(%w.0)
          propagate.0(%exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%exc.0)
            ret(%err.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)):
      ret(0)
  }
}
"

#guard failing oldUsesConst == []
#guard oldUsesConst.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees oldUsesConst oldUsesConstText

/-- An `old` region that allocates a cell holding the contents of `c` at the call, and a read of
that cell after the `old`.  The cell is new at the exit too, and holds there what the region gave
it. -/
private def oldAlloc : Built := withContract fun c _ => Build.ensures (nm "r") intT fun r =>
  withFailureBlock #[intT] (some false) fun fail => do
    let n ← Build.old (nm "n") intT cellT fail fun _ => do
      let v ← emitApply (nm "v") intT Base.refGet.ref #[c]
      let k ← emitApply (nm "k") cellT Base.refNew.ref #[v]
      finishBlock (.ret () (← emitApply (nm "w") (Base.Except intT cellT) Base.Except.ok.ref #[k]))
    retGe r (← emitApply (nm "g") intT Base.refGet.ref #[n])

private def oldAllocText : String := "module m {
  func @m.f(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %n.0 : base.Ref(base.Int) = base.old[base.Int, base.Ref(base.Int)] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %k.0 : base.Ref(base.Int) = base.refNew[base.Int](%v.0)
            %w.0 : base.Except(base.Int, base.Ref(base.Int)) = base.ok[base.Int, base.Ref(base.Int)](%k.0)
            ret(%w.0)
        }
        %g.0 : base.Int = base.refGet[base.Int](%n.0)
        %ok.0 : base.Bool = demo.ge(%r.0, %g.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int), %xs.0 : base.Sequence(base.Int)):
      ret(0)
  }
}
"

#guard failing oldAlloc == []
#guard oldAlloc.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees oldAlloc oldAllocText

-- An `old` may use the parameter of a region that encloses it even when that parameter holds the
-- result, as the parameter of `bind` does here.  The checker accepts this on purpose: the
-- parameter keeps its value, so the result of this `old` is the function's result, not a value of
-- the state at the call.  The same holds for a quantifier's binder.
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %v.0 : base.Bool = demo.bind[base.Int, base.Bool](%r.0) {
          body.0(%x.0 : base.Int):
            %o.0 : base.Int = base.old[base.Int, base.Int] ^no.0() {
              old.0():
                %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
                ret(%w.0)
            }
            %ok.0 : base.Bool = demo.ge(%o.0, 0)
            ret(%ok.0)
          no.0(%e.0 : base.Int):
            unreachable
        }
        ret(%v.0)
    }")

/-- A `free ensures` clause of an extern, with `old`: its failure gives `true`. -/
private def freeOld : Built := externWith fun c =>
  Build.ensures (nm "r") intT (free := true) fun r =>
    withFailureBlock #[intT] (some true) fun fail => do retGe r (← oldGet fail c)

private def freeOldText : String := "module m {
  extern func @m.g(%c.0 : base.Ref(base.Int)) -> base.Int
    free ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(true)
    }
}
"

#guard failing freeOld == []
#guard freeOld.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees freeOld freeOldText

/-! ## What the rules reject

Each rejection breaks one rule. -/

/-! ### `base.old` appears only in an `ensures` clause -/

-- In a `requires` clause.
#guard failing (withContract fun c _ => Build.requires do
  withFailureBlock #[intT] (some false) fun fail => do
    retGe (← oldGet fail c) (← emitConst (nm "zero") (.int 0))) == ["old"]

/-- info: t.dyn:5:8: base.old is allowed only in an ensures clause, but @m.f uses it in a requires clause -/
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%o.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

-- In a region nested in a `requires` clause.
#guard failing (withContract fun c _ => Build.requires do
  let t ← emitConst (nm "t") (.bool true)
  let thn := region #[] (base := "then") do
    withFailureBlock #[intT] none fun fail => do
      retGe (← oldGet fail c) (← emitConst (nm "zero") (.int 0))
  let els := region #[] (base := "else") (finishBlock (.ret () t))
  finishBlock (.ret () (← emitApply (nm "v") boolT Demo.«if».ref #[t] (regions := #[thn, els])))) ==
  ["old"]

/-- info: t.dyn:7:12: base.old is allowed only in an ensures clause, but @m.f uses it in a requires clause -/
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %v.0 : base.Bool = demo.if[base.Bool](true) {
          then.0():
            %o.0 : base.Int = base.old[base.Int, base.Int] ^no.0() {
              old.0():
                %v.1 : base.Int = base.refGet[base.Int](%c.0)
                %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.1)
                ret(%w.0)
            }
            %ok.0 : base.Bool = demo.ge(%o.0, 0)
            ret(%ok.0)
          no.0(%e.0 : base.Int):
            unreachable
        } {
          else.0():
            ret(true)
        }
        ret(%v.0)
    }")

-- In the body.
#guard failing (build (.str (nm "m") "f") intT () do
  let c ← freshVal (nm "c") cellT
  let _ ← startFreshBlock #[c] "entry"
  withFailureBlock #[intT] none fun fail => do finishBlock (.ret () (← oldGet fail c.id))) ==
  ["old"]

/-- info: t.dyn:4:6: base.old is allowed only in an ensures clause, but @m.f uses it in its body -/
#guard_msgs in
#eval readBack "module m {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int {
    entry.0(%c.0 : base.Ref(base.Int)):
      %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
        old.0():
          %v.0 : base.Int = base.refGet[base.Int](%c.0)
          %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
          ret(%w.0)
      }
      ret(%o.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }
}
"

-- In a region of the body's terminator.
#guard failing (build (.str (nm "m") "f") intT () do
  let c ← freshVal (nm "c") cellT
  let _ ← startFreshBlock #[c] "entry"
  let done ← freshLabel "done"
  let body := region #[] (base := "body") do
    withFailureBlock #[intT] none fun fail => do
      retGe (← oldGet fail c.id) (← emitConst (nm "zero") (.int 0))
  terminate Demo.run.ref (succs := #[goto done]) (regions := #[body])
  let _ ← Build.Raw.startBlockWith done (nm "b") boolT
  finishBlock (.ret () (← emitConst (nm "z") (.int 0)))) == ["old"]

/-- info: t.dyn:6:10: base.old is allowed only in an ensures clause, but @m.f uses it in its body -/
#guard_msgs in
#eval readBack "module m {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int {
    entry.0(%c.0 : base.Ref(base.Int)):
      demo.run ^done.0() {
        body.0():
          %o.0 : base.Int = base.old[base.Int, base.Int] ^no.0() {
            old.0():
              %v.0 : base.Int = base.refGet[base.Int](%c.0)
              %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
              ret(%w.0)
          }
          %ok.0 : base.Bool = demo.ge(%o.0, 0)
          ret(%ok.0)
        no.0(%e.0 : base.Int):
          unreachable
      }
    done.0(%b.0 : base.Bool):
      ret(0)
  }
}
"

/-! ### An `old` region sees, from outside it, only parameters and constants -/

-- A use of the result.
#guard failing (withContract fun _ _ =>
  ensuresGe fun fail r => Build.old (nm "o") intT intT fail fun _ => okInt r) == ["old scope"]

/-- info: t.dyn:7:12: the old region in @m.f uses %r.0, which is the result -/
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%r.0)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

-- The same in a `free ensures` clause of an extern.
/-- info: t.dyn:7:12: the old region in @m.g uses %r.0, which is the result -/
#guard_msgs in
#eval readBack "module m {
  extern func @m.g(%c.0 : base.Ref(base.Int)) -> base.Int
    free ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%r.0)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(true)
    }
}
"

-- A use of a value that the clause defines outside the `old` region: the cell's contents at the
-- exit.
#guard failing (withContract fun c _ =>
  ensuresGe fun fail _ => do
    let t ← emitApply (nm "t") intT Base.refGet.ref #[c]
    Build.old (nm "o") intT intT fail fun _ => okInt t) == ["old scope"]

/-- info: t.dyn:8:12: the old region in @m.f uses %t.0, which the clause defines outside the old region -/
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %t.0 : base.Int = base.refGet[base.Int](%c.0)
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.0)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

-- A use of a value that a region nested in the clause defines outside the `old` region.
#guard failing (withContract fun c xs => ensuresEvery xs fun _ prop => do
  let t ← emitApply (nm "t") intT Base.refGet.ref #[c]
  Build.old (nm "o") intT intT prop fun _ => okInt t) == ["old scope"]

-- The same use in an `old` nested in an `old`: the outermost `old` region uses it.
#guard failing (withContract fun c xs => ensuresEvery xs fun _ prop => do
  let t ← emitApply (nm "t") intT Base.refGet.ref #[c]
  Build.old (nm "o") intT intT prop fun p => do
    okInt (← Build.old (nm "i") intT intT p fun _ => okInt t)) == ["old scope"]

-- A use of the result of another `old`.  Both run in the state at the call, but each outermost
-- `old` region is checked on its own, so this is rejected: a conservative limit.
/-- info: t.dyn:13:12: the old region in @m.f uses %o.0, which the clause defines outside the old region -/
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
            ret(%w.0)
        }
        %p.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.1():
            %w.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%o.0)
            ret(%w.1)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %p.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

-- A use of the result in a region nested in the `old` region.
/-- info: t.dyn:9:16: the old region in @m.f uses %r.0, which is the result -/
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = demo.if[base.Int](true) {
              then.0():
                ret(%r.0)
            } {
              else.0():
                ret(0)
            }
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

-- A use of a parameter of a block of the clause other than its entry.
/-- info: t.dyn:14:12: the old region in @m.f uses %n.0, which the clause defines outside the old region -/
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %c.1 : base.Bool = demo.ge(%r.0, 0)
        branch(%c.1) ^a.0() ^b.0()
      a.0():
        jump ^join.0(1)
      b.0():
        jump ^join.0(2)
      join.0(%n.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%n.0)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

/-! ### The rules for contract regions apply to an `old` region -/

-- A `writes` operation inside an `old` region.
#guard failing (withContract fun c _ =>
  ensuresGe fun fail _ => Build.old (nm "o") intT intT fail fun _ => do
    let one ← emitConst (nm "one") (.int 1)
    let _ ← emitApply (nm "s") Base.Unit Base.refSet.ref #[c, one]
    okInt one) == ["contract"]

/-- info: t.dyn:7:12: a contract region of @m.f may not change state, but base.refSet is declared writes -/
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %s.0 : base.Unit = base.refSet[base.Int](%c.0, 1)
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](1)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

-- A failure of `old` that gives `true` in a checked `ensures` clause.
#guard failing (withContract fun c _ => Build.ensures (nm "r") intT fun r =>
  withFailureBlock #[intT] (some true) fun fail => do retGe r (← oldGet fail c)) == ["failures"]

/-- info: t.dyn:5:8: in an ensures clause of @m.f, the failure successor of %o.0 goes to fail.0, which returns true; a failure must give false or be unreachable -/
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(true)
    }")

-- A failure of `old` that gives `false` in a `free ensures` clause.
#guard failing (externWith fun c => Build.ensures (nm "r") intT (free := true) fun r =>
  withFailureBlock #[intT] (some false) fun fail => do retGe r (← oldGet fail c)) == ["failures"]

/-- info: t.dyn:5:8: in a free ensures clause of @m.g, the failure successor of %o.0 goes to fail.0, which returns false; a failure must give true or be unreachable -/
#guard_msgs in
#eval readBack "module m {
  extern func @m.g(%c.0 : base.Ref(base.Int)) -> base.Int
    free ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
}
"

-- A failure inside an `old` region that turns into a value.
#guard failing (withContract fun c _ =>
  ensuresGe fun fail _ => Build.old (nm "o") intT intT fail fun _ => do
    let recover ← freshLabel "recover"
    let v ← emitApply (nm "v") intT Base.refGet.ref #[c]
    okInt (← emitApply (nm "d") intT Demo.div.ref #[v, v] (succs := #[goto recover]))
    let _ ← Build.Raw.startBlockWith recover (nm "e") intT
    okInt (← emitConst (nm "zero") (.int 0))) == ["propagates"]

/-- info: t.dyn:8:12: in a region nested in a contract of @m.f, the failure successor of %d.0 goes to recover.0, which does not pass the failure on with base.error -/
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %v.0 : base.Int = base.refGet[base.Int](%c.0)
            %d.0 : base.Int = demo.div(%v.0, %v.0) ^recover.0()
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%d.0)
            ret(%w.0)
          recover.0(%e.1 : base.Int):
            %w.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](0)
            ret(%w.1)
        }
        %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }")

end Strata.Dyn.OldTest
