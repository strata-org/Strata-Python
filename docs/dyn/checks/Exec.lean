/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Examples.While.Elab
public import StrataDyn.Examples.While.Run
import StrataDyn.Env.WF
meta import StrataDyn.Examples.While.Elab
meta import StrataDyn.Examples.While.Run
meta import StrataDyn.Env.WF

/-!
The guide's listings of the execution engine, compiled against the package: a run of the
running example, what the first steps of its run show, and the wrappers and tags that
`#dyn_sem_table` generates for While.
`checks/run.sh` elaborates this file.
-/

namespace Strata.Dyn.Guide

open Strata.Dyn.While Strata.Dyn.Exec

def prog : Ast.Program := #while
  fun mean(n : Int, d : Int) : Int {
    var s : Int := 0;
    var i : Int := 1;
    while (i <= n) { s := s + i; i := i + 1; }
    try { return s / d; } catch e => { return 0 - e; }
  }
  fun main(n : Int) : Int {
    var m : Int := mean(n, n - 10);
    print(m);
    return m;
  }
#end

/-- `main n`, run on the fused engine, or `none` if the lowering failed. -/
def runMain (n : Int) : Option (Outcome WhileSem.model) := (lower prog).toOption.map fun m =>
  runModule WhileSem.model m (.str .base "main") #[WhileSem.model.arg n] 100000

/-- The result, read as an `Except Int Int`, and the printed output. -/
def describe (o : Outcome WhileSem.model) : String :=
  let r := match o.read? (Except Int Int) with
    | some (.ok v) => s!"ok {v}"
    | some (.error e) => s!"error {e}"
    | none => "not an Except Int Int"
  s!"{r}, printed {o.snapshot.world.out.items}"

/-- info: some "ok 21, printed #[21]" -/
#guard_msgs in #eval (runMain 20).map describe
/-- info: some "ok -1, printed #[-1]" -/
#guard_msgs in #eval (runMain 10).map describe

/-! The run of `main` under one oracle, step by step. -/

/-- What the first `k` steps of `main n` show of the output, and its result if the run has
ended by then. -/
def observe (n : Int) (k : Nat) : Option (List (Array Int) × Option String) := do
  let m ← (lower prog).toOption
  let ⟨_, hw, i⟩ ← (prepare WhileSem.model m (.str .base "main")).toOption
  let ⟨_, c, h⟩ ← (startCore hw i [WhileSem.model.arg n Run]).toOption
  let s : State WhileSem.model.at := ⟨c, .exec, 0, ()⟩
  let shown := obsTrace hw (fun _ => 0) (obsW (M := WhileSem.model.at) (·.out.items)) s h k
  let ended := match trace hw (fun _ => 0) s h k with
    | .ended f => some (describe ⟨f.result, f.snapshot, k, f.drawn⟩)
    | .running _ => none
  return (shown, ended)

/-- info: some ([#[], #[21]], some "ok 21, printed #[21]") -/
#guard_msgs in #eval observe 20 184
/-- info: some ([#[], #[21]], none) -/
#guard_msgs in #eval observe 20 183
/-- info: some [#[]] -/
#guard_msgs in #eval (observe 20 10).map (·.1)

/-! The wrappers. -/

/--
info: @[expose] def Strata.Dyn.WhileSem.rule.while.div : (σ : Type) →
  [inst : Store σ] →
    Fn (WhileSem.interp σ)
      (Tree (WhileSem.interp σ) σ (WhileSem.W σ) [] [[WhileSem.T.base.Int]] Empty
        (WhileSem.interp σ WhileSem.T.base.Int))
      [WhileSem.T.base.Int, WhileSem.T.base.Int] :=
fun σ [Store σ] a0 a1 => WhileRules.div a0 a1 { exit := fun p0 => Out.exit (Exit.here (Args.cons p0 Args.nil)) }
-/
#guard_msgs in #print WhileSem.rule.while.div

/--
info: @[expose] def Strata.Dyn.WhileSem.again.while.loop : (σ : Type) →
  [inst : Store σ] →
    Unit →
      Sem (MEff (WhileSem.interp σ) σ (WhileSem.W σ) [([], WhileSem.T.base.Bool), ([], WhileSem.T.while.Flow)])
        (Out (WhileSem.interp σ) [[WhileSem.T.base.Int]] Unit) Unit :=
fun σ [Store σ] st =>
  WhileRules.loop (Region.slot ⟨0, WhileSem.rule.while.loop._proof_1⟩ fun x => Args.nil)
    (Region.slot ⟨1, WhileSem.rule.while.loop._proof_2⟩ fun x => Args.nil)
    { exit := fun p0 => Out.exit (Exit.here (Args.cons p0 Args.nil)) } (some st) { exit := Out.again }
-/
#guard_msgs in #print WhileSem.again.while.loop

/--
info: @[expose] def Strata.Dyn.WhileSem.rule.while.le : (σ : Type) →
  [inst : Store σ] →
    Fn (WhileSem.interp σ) (WhileSem.interp σ WhileSem.T.base.Bool) [WhileSem.T.base.Int, WhileSem.T.base.Int] :=
fun σ [Store σ] a0 a1 => WhileRules.le a0 a1
-/
#guard_msgs in #print WhileSem.rule.while.le

/-! The tags. -/

/--
info: @[reducible, expose] def Strata.Dyn.WhileSem.T.base.Except : Ty → Ty → Ty :=
fun x0 x1 => Ty.app 8 [x0, x1]
-/
#guard_msgs in #print WhileSem.T.base.Except

/--
info: @[reducible, expose] def Strata.Dyn.WhileSem.H : (σ : Type) → [Store σ] → Nat → List Type → Type :=
fun σ [Store σ] h as =>
  match h, as with
  | 2, [] => Unit
  | 3, [] => Bool
  | 4, [] => Int
  | 5, [] => Float
  | 6, [] => String
  | 7, [x0] => Array x0
  | 8, [x0, x1] => Except x0 x1
  | 9, [] => NoLoc
  | 10, [] => IntList.Val
  | 11, [] => Flow.Val
  | x, x_1 => Empty
-/
#guard_msgs in #print WhileSem.H

end Strata.Dyn.Guide
