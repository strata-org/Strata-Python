/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Examples.While.Programs
public import StrataDyn.Exec.Fused
import all StrataDyn.Util.Trace
import StrataDyn.Env.WF
-- `#guard` runs the lowering, the checks and the engine as compiled code.
meta import StrataDynTest.Examples.While.Programs
meta import StrataDyn.Exec.Fused
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Traces and behaviours

Behaviours are not computable, so this file proves them for the runs of small machines on the
library's own terms, and checks what While programs show on prefixes of their runs under one
oracle, computed in one pass by `Exec.obsTrace` (`Exec.oracleRun_obsUpTo`), which
`Run.beh_extends_iff` and `Run.beh_ended` turn into facts about their behaviours.
-/

namespace Strata.Dyn.TraceTest

open Strata.Dyn.Trace

/-! ## Small machines

A state is the output so far.  `idle` is `while true {}`, `ticker` is
`i := 0; while true { print i; i := i + 1 }`, and `countdown` adds `k, k - 1, …, 1` and returns
the total.  Each observes the output. -/

/-- `while true {}`: every step comes back to the same state. -/
def idle (out : List Nat) : Config (List Nat) Nat := .running out

/-- A loop that prints the next number at each step. -/
def ticker (out : List Nat) : Config (List Nat) Nat := .running (out ++ [out.length])

/-- The counter left and the total so far; it prints nothing. -/
def countdown : Nat × Nat → Config (Nat × Nat) Nat
  | (0, acc) => .ended acc
  | (k + 1, acc) => .running (k, acc + k + 1)

/-! ### `while true {}` diverges silently -/

/-- `while true {}` is running in its first state after every number of steps. -/
theorem idle_trace (out : List Nat) : ∀ n, trace idle out n = .running out
  | 0 => rfl
  | n + 1 => (trace_succ_running rfl n).trans (idle_trace out n)

/-- The run of `while true {}`. -/
def idleRun : Run (graph idle) [] := Run.ofFun idle []

/-- `while true {}` never ends. -/
theorem idle_diverges : idleRun.Diverges :=
  fun n => ⟨[], idle_trace [] n⟩

/-- `while true {}` shows only the empty output, forever. -/
theorem idle_obsUpTo : ∀ n, idleRun.obsUpTo id n = [[]]
  | 0 => rfl
  | n + 1 => by
    rw [idleRun.obsUpTo_running (idle_trace [] (n + 1)), idle_obsUpTo n]
    rfl

/-- `while true {}` diverges silently, showing only the empty output. -/
theorem idle_beh : idleRun.beh id id = .silent [[]] := by
  rw [← idle_obsUpTo 0]
  exact idleRun.beh_silent idle_diverges fun n _ => by rw [idle_obsUpTo, idle_obsUpTo]

/-- Its twin, a run that ends, does not diverge: no run of `countdown` from `(2, 0)` does. -/
theorem countdown_not_diverges : ¬ Diverges (graph countdown) (2, 0) := by
  rintro ⟨r, h⟩
  obtain ⟨_, h₃⟩ := h 3
  rw [r.eq_trace] at h₃
  exact nomatch h₃

/-! ### The printing loop reacts -/

/-- After `n` steps the ticker is running, having printed `0, …, n - 1`. -/
theorem ticker_trace : ∀ n, trace ticker [] n = .running (List.range n)
  | 0 => rfl
  | n + 1 => by
    rw [trace_succ, ticker_trace n, List.range_succ]
    show Config.running (List.range n ++ [(List.range n).length]) = _
    rw [List.length_range]

/-- The run of the ticker. -/
def tickerRun : Run (graph ticker) [] := Run.ofFun ticker []

/-- The ticker shows every prefix of its output in turn. -/
theorem ticker_obsUpTo : ∀ n, tickerRun.obsUpTo id n = (List.range (n + 1)).map List.range
  | 0 => rfl
  | n + 1 => by
    rw [tickerRun.obsUpTo_running (ticker_trace (n + 1)), ticker_obsUpTo n]
    show addObs ((List.range (n + 1)).map List.range) (List.range (n + 1)) = _
    rw [addObs_of_ne]
    · rw [List.range_succ (n := n + 1), List.map_append]
      rfl
    · have e : (List.range (n + 1)).map List.range =
          (List.range n).map List.range ++ [List.range n] := by
        rw [List.range_succ, List.map_append]
        rfl
      rw [e, List.getLast?_concat]
      intro h
      have hlen := congrArg List.length (Option.some.inj h)
      rw [List.length_range, List.length_range] at hlen
      exact Nat.succ_ne_self n hlen.symm

/-- The ticker reacts, showing every prefix of its output in turn. -/
theorem ticker_beh : tickerRun.beh id id = .react List.range := by
  apply tickerRun.beh_react (fun n => ⟨_, ticker_trace n⟩)
  · intro n i hi
    simp only [ticker_obsUpTo, List.getElem_map, List.getElem_range]
  · intro i
    exact ⟨i, by rw [ticker_obsUpTo, List.length_map, List.length_range]; exact Nat.lt_succ_self i⟩

-- Its twin, `while true {}`, does not react.
example : ∀ σ, idleRun.beh id id ≠ .react σ := by
  intro σ h
  rw [idle_beh] at h
  exact nomatch h

/-! ### `countdown` terminates with its total -/

/-- `countdown` from `10` has ended after 11 steps, with `55`. -/
theorem countdown_trace : trace countdown (10, 0) 11 = .ended 55 := rfl

/-- Every run of `countdown` from `10` terminates with `55`. -/
theorem countdown_beh (r : Run (graph countdown) (10, 0)) :
    r.beh (fun _ => ()) id = .term [()] 55 := by
  rw [r.beh_ended ((r.eq_trace 11).trans countdown_trace),
    Run.obsUpTo_congr r (Run.ofFun countdown (10, 0)) r.eq_trace]
  rfl

-- A run that ends is not a divergence.
example : ((Run.ofFun countdown (10, 0)).beh (fun _ => ()) id).IsTerm := by
  rw [countdown_beh]
  trivial

example : ¬ (idleRun.beh id id).IsTerm := idleRun.beh_not_isTerm idle_diverges

/-! ## While programs

The run of a While function under one oracle: what its first `n` steps show of the output and
the choices made, and whether it has ended. -/

open Strata.Dyn.While Strata.Dyn.While.Ast Strata.Dyn.While.Programs
open Strata.Dyn.Exec (prepare startCore State)

/-- What the first `n` steps of `f`'s run on `args` show of the output and the choices made,
and how the run stands after them: `none` if it is still running. -/
def observe (p : Program) (f : String) (args : Array Int) (n : Nat) :
    Except String (List (Array Int × Nat) × Option String) := do
  let m ← lower p
  match prepare WhileSem.model m (nm f) with
  | .error e => throw (showFault e)
  | .ok ⟨_, hw, i⟩ =>
    match startCore hw i (args.map fun x => WhileSem.model.arg x Exec.Run).toList with
    | .error e => throw (showFault e)
    | .ok ⟨_, c, h⟩ =>
      let s : State WhileSem.model.at := ⟨c, .exec, 0, ()⟩
      let shown := Exec.obsTrace hw (fun _ => 0)
        (Exec.obsCfg (M := WhileSem.model.at) fun w => w.out.items) s h n
      let ended := match Exec.trace hw (fun _ => 0) s h n with
        | .ended f => some (showOutcome ⟨f.result, f.snapshot, n, f.drawn⟩)
        | .running _ => none
      return (shown, ended)

/-- A loop that prints forever. -/
def printer : Program := #while
  fun printer() : Int { var i : Int := 0; while (true) { print(i); i := i + 1; } return 0; }
#end

-- The printing loop: each output is a prefix of its behaviour (`Run.beh_extends`), so it prints
-- `0, 1, 2, …` in order, and after 60 steps it is still running.
#guard (observe printer "printer" #[] 60).toOption.map (·.1.map (·.1)) =
  some [#[], #[0], #[0, 1], #[0, 1, 2], #[0, 1, 2, 3], #[0, 1, 2, 3, 4], #[0, 1, 2, 3, 4, 5]]
#guard (observe printer "printer" #[] 60).toOption.map (·.2) = some none

-- `while true {}` shows nothing over a long prefix and is still running.
#guard (observe Programs.spin "spin" #[] 2000).toOption = some ([(#[], 0)], none)

-- `sum 100` ends within 810 steps with `5050`, having printed nothing: by `Run.beh_ended`, its
-- behaviour is `.term [(#[], 0)] (ok 5050)`.
#guard (observe Programs.sum "sum" #[100] 810).toOption = some ([(#[], 0)], some "ok 5050")
#guard (observe Programs.sum "sum" #[100] 809).toOption = some ([(#[], 0)], none)

-- `logged 3` prints as it goes, then ends.
#guard (observe logged "logged" #[3] 100).toOption.map (fun (t, r) => (t.map (·.1), r)) =
  some ([#[], #[0], #[0, 10], #[0, 10, 20], #[0, 10, 20, 1]], some "ok 5")

/-! ## Axioms -/

/-- info: 'Strata.Dyn.Trace.Sim.improves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sim.improves

/-- info: 'Strata.Dyn.Trace.Run.beh_extends_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Run.beh_extends_iff

/-- info: 'Strata.Dyn.Exec.diverges_iff_fused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exec.diverges_iff_fused

/-- info: 'Strata.Dyn.Exec.reach_runFused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exec.reach_runFused

/-- info: 'Strata.Dyn.Exec.always' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exec.always

/-- info: 'Strata.Dyn.Exec.beh_of_runFused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exec.beh_of_runFused

end Strata.Dyn.TraceTest
