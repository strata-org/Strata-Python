/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Examples.While.Programs
import StrataDyn.Env.WF
-- `#guard` and `#eval` run the lowering, the checks and the engine as compiled code.
meta import StrataDynTest.Examples.While.Programs
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Running While programs

Every example program lowers to a well-formed module, and every example runs to its expected
outcome.  Then the world, the oracle, and the lowering's errors.
-/

namespace Strata.Dyn.While.RunTest

open Strata.Dyn.While Strata.Dyn.While.Programs Strata.Dyn.While.Ast
open Strata.Dyn.Exec

/-- Every program of `Programs.lean`, by name. -/
def programs : List (String × Program) :=
  [("arith", arith), ("sum", sum), ("gcd", gcd), ("fact", fact), ("fib", fib), ("lists", lists),
   ("exceptions", exceptions), ("spin", spin), ("power", power), ("loop", Programs.loop),
   ("calls", calls), ("cells", cells), ("rcounter", rcounter), ("rnested", rnested),
   ("rgap", rgap), ("rspin", rspin), ("rcatch", rcatch), ("rescape", rescape),
   ("logged", logged), ("wcells", wcells), ("coins", coins)]

/-! ## Well-formedness

Each program lowers, and its module satisfies `Module.WF`. -/

/-- info: [] -/
#guard_msgs in
#eval programs.filterMap fun (n, p) => match lower p with
  | .ok _ => none
  | .error e => some s!"{n}: {e}"

/-- A `catch` that nothing raises to, in a loop: lowering drops its handler, so the loop's back
edge still passes everything its header's scope holds. -/
def deadCatch : Program := #while
  fun f(n : Int) : Int {
    var i : Int := 0;
    while (i < n) { try { i := i + 1; } catch e => { i := e; } }
    return i;
  }
#end

#guard (lower deadCatch).toBool
#guard (run deadCatch "f" #[3]).toOption.map showOutcome = some "ok 3"

/-! ## The examples -/

/-- The run of example `e`, or the lowering's error. -/
def outcome (e : Example) : Except String (Outcome WhileSem.model) :=
  run e.prog e.entry e.args

/-- How example `e` ended. -/
def showRun (e : Example) : String :=
  match outcome e with
  | .ok o => showOutcome o
  | .error msg => s!"lowering error: {msg}"

-- Every example ends as expected.
#guard examples.all fun e => showRun e == e.expected

/-- An example, as a line: its outcome, its fused steps, and what it printed. -/
def line (e : Example) : String :=
  match outcome e with
  | .ok a => s!"{e.name}: {showOutcome a} after {a.steps} fused steps; \
      printed {a.snapshot.world.out.items}"
  | .error _ => s!"{e.name}: {showRun e}"

/--
info: arith: ok 37 after 11 fused steps; printed #[]
sum 100: ok 5050 after 606 fused steps; printed #[]
gcd 12 18: ok 6 after 21 fused steps; printed #[]
gcd 1071 462: ok 21 after 21 fused steps; printed #[]
fact 20: ok 2432902008176640000 after 139 fused steps; printed #[]
fib 15: ok 610 after 17752 fused steps; printed #[]
length (range 10): ok 10 after 155 fused steps; printed #[]
total (range 100): ok 5050 after 1315 fused steps; printed #[]
reverse (range 4): ok 4 :: 3 :: 2 :: 1 :: nil after 67 fused steps; printed #[]
head (range 0) or 7: ok 7 after 11 fused steps; printed #[]
safeDiv 7 2: ok 3 after 3 fused steps; printed #[]
safeDiv 7 0: ok -1 after 5 fused steps; printed #[]
viaCall 5: ok 6 after 15 fused steps; printed #[]
viaCall -1: ok 42 after 13 fused steps; printed #[]
nested 0: ok 101 after 9 fused steps; printed #[]
boom 1: raised 1 after 4 fused steps; printed #[]
spin: fault out of fuel after 100000 fused steps; printed #[]
cube 2: fault gap: while.pow: not implemented after 2 fused steps; printed #[]
counter 10: ok 10 after 88 fused steps; printed #[]
escape 1: ok 16 after 19 fused steps; printed #[]
alias 21: ok 42 after 7 fused steps; printed #[]
two 3: ok 74 after 20 fused steps; printed #[]
stack 3: ok 2 :: 1 :: 0 :: nil after 44 fused steps; printed #[]
rcounter 10: ok 10 after 109 fused steps; printed #[]
nested 3: ok 304 after 251 fused steps; printed #[]
rgap 2: fault gap: while.pow: not implemented after 7 fused steps; printed #[]
rgap -1: ok -1 after 9 fused steps; printed #[]
rspin: fault out of fuel after 100000 fused steps; printed #[]
rcatch 5: ok 1000 after 108 fused steps; printed #[]
rescape 3: ok 21 after 45 fused steps; printed #[]
logged 3: ok 5 after 55 fused steps; printed #[0, 10, 20, 1]
coins 3: ok 0 after 62 fused steps; printed #[]
wcounter 7: ok 7 after 64 fused steps; printed #[]
-/
#guard_msgs in
#eval IO.println ("\n".intercalate (examples.map line))

/-! ## The world and the oracle -/

/-- `run`'s outcome, its world, and its choices, if the program lowers. -/
def world (p : Program) (f : String) (args : Array Int) (oracle : Nat → Nat := fun _ => 0) :
    Option (String × WhileRules.World × Nat) :=
  (run p f args (oracle := oracle)).toOption.map fun o =>
    (showOutcome o, o.snapshot.world, o.drawn)

-- `print` appends to the output, inside a region too, and `tick` counts.
#guard (world logged "logged" #[3]).map (fun (s, w, _) => (s, w.out.items, w.ticks.n)) =
  some ("ok 5", #[0, 10, 20, 1], 3)

-- A cell that rules make, read and write on the machine's heap: the world holds nothing.
#guard world wcells "wcounter" #[5] = some ("ok 5", {}, 0)

-- `pick(1)` asks the oracle, which answers from a tape, then `0`.
#guard (world coins "coins" #[3] (tapeOracle [1, 0, 1])).map (fun (s, _, d) => (s, d)) =
  some ("ok 5", 3)
-- An answer above the bound is reduced below it: `7 % 2 = 1`.
#guard (world coins "coins" #[2] (tapeOracle [7, 7])).map (·.1) = some "ok 3"

/-! ## Lowering errors -/

/-- The error lowering `p` reports, if any. -/
def lowerError (p : Program) : Option String :=
  match lower p with
  | .ok _ => none
  | .error e => some e

#guard lowerError #while fun f() : Unit { var x : Int := 0; x := true; } #end =
  some "f: assignment to x: expected Int, got Bool"
#guard lowerError #while fun f() : Int { return g(); } #end = some "f: unknown function g"
#guard lowerError #while fun f(x : Int) : Int { var x : Int := 1; return x; } #end =
  some "f: x is already declared"
#guard lowerError #while
    fun f() : Int { var c : Ref := ref 0; region while (true) { return 1; } return 0; }
  #end = some "f: a region cannot return"
#guard lowerError #while
    fun f() : Int { var i : Int := 0; region while (i < 3) { i := i + 1; } return i; }
  #end = some "f: i is assigned inside a region, which reads it but cannot assign it; use a cell"
#guard lowerError #while
    fun f(x : Int) : Int { var c : Ref := ref 0; region while (1 / x == 0) { } return 0; }
  #end = some "f: the condition of a region while cannot raise"

/-! ## Cells through `Except`

The running example: `mk` makes a cell, or raises; it may raise, so it returns
`base.Except Int (base.Ref Int)`, and the cell travels in the `ok` and through `use`'s
`base.Except.case` before `use` reads it. -/

def mkUse : Program := #while
  fun mk(x : Int) : Ref { if (x == 0) { raise 1; } return ref x; }
  fun use(x : Int) : Int { var r : Ref := mk(x); return *r; }
#end

#guard (run mkUse "use" #[5]).toOption.map showOutcome = some "ok 5"
#guard (run mkUse "use" #[0]).toOption.map showOutcome = some "raised 1"

-- `mk`'s own result: its cell in the `ok`, or what it raised.
#guard (run mkUse "mk" #[5]).toOption.map showOutcome = some "ok <cell>"
#guard (run mkUse "mk" #[0]).toOption.map showOutcome = some "raised 1"

/-- A function that returns a cell and cannot raise. -/
def plainRef : Program := #while
  fun mk(x : Int) : Ref { return ref x; }
#end

#guard (run plainRef "mk" #[5]).toOption.map showOutcome = some "ok <cell>"

end Strata.Dyn.While.RunTest
