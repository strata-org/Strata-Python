/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Examples.While.Env
public import StrataDyn.Build.Typed
public import StrataDyn.DDM
import StrataDyn.Env.WF
meta import StrataDyn.Examples.While.Env
meta import StrataDyn.Build.Typed
meta import StrataDyn.DDM
meta import StrataDyn.Env.WF

/-!
The guide's builder listings, compiled against the package: the running example's two
functions, built with the typed emitters.  `checks/run.sh` elaborates this file, and the
`#guard_msgs` blocks pin the folded print, which is `data/mean.folded.dyn`.
-/

-- While's environment module does not import the typed builder, so its emitters are made here.
namespace Strata.Dyn
dyn_emitters While
end Strata.Dyn

namespace Strata.Dyn.Guide

open Strata.Dyn.Emit

abbrev W := While.env

def n (s : String) : Name := .str .base s

/-- What both functions return. -/
abbrev R : TypeExpr W := Base.Except Base.Int Base.Int

/-- What `Emit.func` gives: the checked function, or why it was not built. -/
abbrev Built := Except (Build.FailedFunc W Unit Unit) ({fn : Func W Unit // fn.WF} × Unit)

/-- `mean`, built with the typed emitters. -/
def mean : Built :=
  Emit.func (n "mean") [(n "n", Base.Int), (n "d", Base.Int)] R ()
      fun (.cons n₀ (.cons d₀ .nil)) funcExit => do
    let% head ← freshLabel [Base.Int, Base.Int, Base.Int, Base.Int]
    let% body ← freshLabel []
    let% exit ← freshLabel []
    let handler ← freshLabel [Base.Int, Base.Int, Base.Int, Base.Int, Base.Int] "catch"
    let k₀ ← int (n "k") 0
    let k₁ ← int (n "k") 1
    Base.jump (head.goto.bindAll vals[n₀, d₀, k₀, k₁])
    -- The loop header takes every variable in scope.
    let (nd₁, n₁) ← param (n "n") Base.Int
    let (dd₁, d₁) ← param (n "d") Base.Int
    let (sd, s) ← param (n "s") Base.Int
    let (id, i) ← param (n "i") Base.Int
    Build.Raw.startBlock head.label #[nd₁, dd₁, sd, id]
    let% t ← While.le i n₁
    Base.branch t body.goto exit.goto
    let _ ← Emit.startBlock body
    let% t ← While.add s i
    let t₁ ← While.add i (← int (n "k") 1) (result := n "t")
    Base.jump (head.goto.bindAll vals[n₁, d₁, t, t₁])
    let _ ← Emit.startBlock exit
    -- The handler in effect is `catch`: the division's `^err` binds the variables first.
    let% t ← While.div s d₁ (handler.goto.bind n₁ |>.bind d₁ |>.bind s |>.bind i)
    let% ok ← Base.Except.ok t
    ret funcExit ok
    let (nd₂, _) ← param (n "n") Base.Int
    let (dd₂, _) ← param (n "d") Base.Int
    let (sd₁, _) ← param (n "s") Base.Int
    let (id₁, _) ← param (n "i") Base.Int
    let (ed, e) ← param (n "e") Base.Int
    Build.Raw.startBlock handler.label #[nd₂, dd₂, sd₁, id₁, ed]
    let% t ← While.sub (← int (n "k") 0) e
    let% ok ← Base.Except.ok t
    ret funcExit ok

/-- `main`, built with the typed emitters: a call through a typed code pointer, and the
`Except.case` that follows it. -/
def main : Built :=
  Emit.func (n "main") [(n "n", Base.Int)] R () fun (.cons n₀ .nil) funcExit => do
    let% ok ← freshLabel [Base.Int]
    let% raise ← freshLabel [Base.Int]
    let% t ← While.sub n₀ (← int (n "k") 10)
    let f : Val W (Base.Fn [Base.Int, Base.Int] R) ← code (n "mean")
    let% r ← Base.callCode f vals[n₀, t]
    Base.Except.case r ok.goto raise.goto
    let% x ← startBlock₁ ok
    let _ ← While.print x (result := n "u")
    let% ok ← Base.Except.ok x
    ret funcExit ok
    let% e ← startBlock₁ raise
    let% error ← Base.Except.error e
    ret funcExit error

/-- `mean` with its loop as `while.loop`, whose condition and body are regions, and its variables
in cells. -/
def meanRegion : Built :=
  Emit.func (n "mean") [(n "n", Base.Int), (n "d", Base.Int)] R ()
      fun (.cons n₀ (.cons d₀ .nil)) funcExit => do
    let% raise ← freshLabel [Base.Int]
    let% s ← Base.refNew (← int (n "k") 0)
    let% i ← Base.refNew (← int (n "k") 1)
    let _ ← While.loop
      (fun exit => do
        let% t ← While.le (← Base.refGet i) n₀
        Base.jump (exit.bind t))
      (fun exit => do
        let _ ← Base.refSet s (← While.add (← Base.refGet s) (← Base.refGet i))
        let _ ← Base.refSet i (← While.add (← Base.refGet i) (← int (n "k") 1))
        Base.jump (exit.bind (← While.Flow.next)))
      raise.goto
    let% q ← While.div (← Base.refGet s) d₀ raise.goto
    ret funcExit (← Base.Except.ok q)
    let% e ← startBlock₁ raise
    ret funcExit (← Base.Except.error e)

/-- `f`, printed, or why it was not built. -/
def printFunc (f : Built) : String :=
  match f with
  | .ok (f, _) => match Module.ofChecked (n "m") #[f] () with
    | .ok m => m.format
    | .error _ => "the module is not well formed"
  | .error e => toString e

/-- info: module m {
  func @mean(%n.0 : base.Int, %d.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int, %d.0 : base.Int):
      %s.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %i.0 : base.Ref(base.Int) = base.refNew[base.Int](1)
      %loop.0 : base.Unit = while.loop ^raise.0() {
        cond.0():
          %refGet.0 : base.Int = base.refGet[base.Int](%i.0)
          %t.0 : base.Bool = while.le(%refGet.0, %n.0)
          ret(%t.0)
      } {
        body.0():
          %refGet.1 : base.Int = base.refGet[base.Int](%s.0)
          %refGet.2 : base.Int = base.refGet[base.Int](%i.0)
          %add.0 : base.Int = while.add(%refGet.1, %refGet.2)
          %refSet.0 : base.Unit = base.refSet[base.Int](%s.0, %add.0)
          %refGet.3 : base.Int = base.refGet[base.Int](%i.0)
          %add.1 : base.Int = while.add(%refGet.3, 1)
          %refSet.1 : base.Unit = base.refSet[base.Int](%i.0, %add.1)
          %next.0 : while.Flow = while.next
          ret(%next.0)
      }
      %refGet.4 : base.Int = base.refGet[base.Int](%s.0)
      %q.0 : base.Int = while.div(%refGet.4, %d.0) ^raise.0()
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%q.0)
      ret(%ok.0)
    raise.0(%e.0 : base.Int):
      %error.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%e.0)
      ret(%error.0)
  }
} -/
#guard_msgs in
#eval IO.println (printFunc meanRegion)

/-- The module of `mean` and `main`, printed folded, or why it was not built. -/
def printed : String :=
  match mean, main with
  | .ok (f, _), .ok (g, _) => match Module.ofChecked (n "main") #[f, g] () with
    | .ok m => m.format
    | .error _ => "the module is not well formed"
  | .error e, _ | _, .error e => toString e

/-- info: module main {
  func @mean(%n.0 : base.Int, %d.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int, %d.0 : base.Int):
      jump ^head.0(%n.0, %d.0, 0, 1)
    head.0(%n.1 : base.Int, %d.1 : base.Int, %s.0 : base.Int, %i.0 : base.Int):
      %t.0 : base.Bool = while.le(%i.0, %n.1)
      branch(%t.0) ^body.0() ^exit.0()
    body.0():
      %t.1 : base.Int = while.add(%s.0, %i.0)
      %t.2 : base.Int = while.add(%i.0, 1)
      jump ^head.0(%n.1, %d.1, %t.1, %t.2)
    exit.0():
      %t.3 : base.Int = while.div(%s.0, %d.1) ^catch.0(%n.1, %d.1, %s.0, %i.0)
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.3)
      ret(%ok.0)
    catch.0(%n.2 : base.Int, %d.2 : base.Int, %s.1 : base.Int, %i.1 : base.Int, %e.0 : base.Int):
      %t.4 : base.Int = while.sub(0, %e.0)
      %ok.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%t.4)
      ret(%ok.1)
  }
  func @main(%n.0 : base.Int) -> base.Except(base.Int, base.Int) {
    entry.0(%n.0 : base.Int):
      %t.0 : base.Int = while.sub(%n.0, 10)
      %r.0 : base.Except(base.Int, base.Int) = base.callCode[[base.Int, base.Int], base.Except(base.Int, base.Int)](@mean, %n.0, %t.0)
      base.Except.case[base.Int, base.Int](%r.0) ^ok.0() ^raise.0()
    ok.0(%x.0 : base.Int):
      %u.0 : base.Unit = while.print(%x.0)
      %ok.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
      ret(%ok.0)
    raise.0(%e.0 : base.Int):
      %error.0 : base.Except(base.Int, base.Int) = base.error[base.Int, base.Int](%e.0)
      ret(%error.0)
  }
} -/
#guard_msgs in
#eval IO.println printed
