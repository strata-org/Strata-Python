/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Programs
public import StrataDyn.Exec.Run
import StrataDyn.Env.WF
-- `#eval` runs the engine and the programs as compiled code.
meta import StrataDynTest.Exec.Programs
meta import StrataDyn.Exec.Run
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Runs, compiled

Each program of `Programs.lean` under `#eval`, on both engines: its outcome, and how many steps
each engine took.
-/

namespace Strata.Dyn.ExecTest.EvalTest

open Strata.Dyn.ExecTest.Programs
open Strata.Dyn.Exec

/-- The functions a run of `f` needs: `f` and those it calls. -/
def needs (f : String) : List (Func E Unit) :=
  match f with
  | "arith" => [arith]
  | "sum" => [sum]
  | "safeDiv" => [safeDiv]
  | "chain" => [inc, fail, chain]
  | "fib" => [fib]
  | "closure" => [addRef, closure]
  | "count" => [count]
  | "squares" => [squares]
  | "squaresR" => [squaresR]
  | "tables" => [tables]
  | "powAbove" => [powAbove]
  | "noisy" => [noisy]
  | "coins" => [coins]
  | "gapAfter" => [gapAfter]
  | "halts" => [halts]
  | "fibC" => [fibC]
  | "useTwice" => [incI, twice, useTwice]
  | "viaCell" => [incI, viaCell]
  | _ => []

/-- Run `f` on `args`, in a module of what it needs. -/
def run (f : String) (args : Array Int) (fuel : Nat := 10000) (oracle : Nat → Nat := fun _ => 0)
    (engine : Engine := .fused) : Outcome ExSem.model :=
  match mod (needs f) with
  | .ok m => runModule ExSem.model m (nm f) (args.map (ExSem.model.arg ·)) fuel oracle engine
  | .error e => .failed ExSem.model e

section
variable {σ : Type} [Store σ]

/-- The `Int` a run returned, if any. -/
def intOf (r : Result (ExSem.model.interp σ)) : Option Int := ExSem.model.read? r Int

/-- The `Except Int Int` a run returned, if any, as whether it is `ok` and its value. -/
def excOf (r : Result (ExSem.model.interp σ)) : Option (Bool × Int) :=
  (ExSem.model.read? r (Except Int Int)).map fun
    | .ok v => (true, v)
    | .error e => (false, e)

/-- The fault a run ended with, if any. -/
def faultOf (r : Result (ExSem.model.interp σ)) : Option Fault := match r with
  | .ok _ => none
  | .fault f => some f

end

/-- What a run produced, for comparing engines: its value, its fault, the world and the
choices made. -/
def summary (o : Outcome ExSem.model) :
    Option Int × Option (Bool × Int) × Option Fault × ExRules.World × Nat :=
  (intOf o.result, excOf o.result, faultOf o.result, o.snapshot.world, o.drawn)

/-- A run, as a line. -/
def line (f : String) (args : Array Int) (oracle : Nat → Nat := fun _ => 0) : String :=
  let show₁ (o : Outcome ExSem.model) : String :=
    let r := match intOf o.result, excOf o.result, faultOf o.result with
      | some v, _, _ => s!"{v}"
      | _, some (ok, v), _ => if ok then s!"ok {v}" else s!"error {v}"
      | _, _, some f => s!"fault {repr f}"
      | _, _, _ => "?"
    s!"{r} after {o.steps}"
  let a := run f args (oracle := oracle)
  let b := run f args (oracle := oracle) (engine := .frames)
  s!"{f} {args}: {show₁ a} fused, {b.steps} by step; drawn {a.drawn}, \
    printed {a.snapshot.world.out.items}"

/--
info: arith #[3, 4]: 6 after 4 fused, 6 by step; drawn 0, printed #[]
sum #[10]: 45 after 65 fused, 89 by step; drawn 0, printed #[]
safeDiv #[7, 0]: -1 after 3 fused, 6 by step; drawn 0, printed #[]
chain #[5]: 106 after 13 fused, 20 by step; drawn 0, printed #[]
fib #[10]: ok 55 after 1589 fused, 2120 by step; drawn 0, printed #[]
closure #[5]: 19 after 21 fused, 30 by step; drawn 0, printed #[]
count #[4]: 4 after 44 fused, 64 by step; drawn 0, printed #[]
noisy #[5]: 5 after 6 fused, 12 by step; drawn 1, printed #[5]
coins #[]: 123 after 10 fused, 15 by step; drawn 3, printed #[]
gapAfter #[2]: fault Strata.Dyn.Exec.Fault.gap "ex.gap" after 2 fused, 4 by step; drawn 0, printed #[2]
halts #[]: fault Strata.Dyn.Exec.Fault.failure "ex.halt" after 1 fused, 2 by step; drawn 0, printed #[]
fibC #[10]: 55 after 1412 fused, 1943 by step; drawn 0, printed #[]
useTwice #[5]: 7 after 13 fused, 21 by step; drawn 0, printed #[]
viaCell #[5]: 6 after 8 fused, 12 by step; drawn 0, printed #[]
squares #[4, -1]: 10409 after 32 fused, 50 by step; drawn 0, printed #[0, 1, 2, 3]
squares #[0, -1]: 0 after 4 fused, 6 by step; drawn 0, printed #[]
squares #[5, 2]: -2 after 24 fused, 39 by step; drawn 0, printed #[0, 1, 2]
squaresR #[4, -1]: 10409 after 32 fused, 50 by step; drawn 0, printed #[0, 1, 2, 3]
squaresR #[0, -1]: 0 after 4 fused, 6 by step; drawn 0, printed #[]
squaresR #[5, 2]: -2 after 24 fused, 39 by step; drawn 0, printed #[0, 1, 2]
tables #[3]: 10404 after 55 fused, 81 by step; drawn 0, printed #[]
powAbove #[100]: 128 after 54 fused, 93 by step; drawn 0, printed #[1, 2, 4, 8, 16, 32, 64]
-/
#guard_msgs in
#eval IO.println ("\n".intercalate [line "arith" #[3, 4], line "sum" #[10], line "safeDiv" #[7, 0],
  line "chain" #[5], line "fib" #[10], line "closure" #[5], line "count" #[4],
  line "noisy" #[5] (fun _ => 3), line "coins" #[] (fun i => i + 1), line "gapAfter" #[2],
  line "halts" #[], line "fibC" #[10], line "useTwice" #[5], line "viaCell" #[5],
  line "squares" #[4, -1], line "squares" #[0, -1], line "squares" #[5, 2],
  line "squaresR" #[4, -1], line "squaresR" #[0, -1], line "squaresR" #[5, 2],
  line "tables" #[3], line "powAbove" #[100]])

end Strata.Dyn.ExecTest.EvalTest
