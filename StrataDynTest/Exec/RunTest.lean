/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Programs
public import StrataDyn.Exec.Run
import StrataDyn.Env.WF
-- `#guard` runs the engine and the programs as compiled code.
meta import StrataDynTest.Exec.Programs
meta import StrataDyn.Exec.Run
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Runs

Each program of `Programs.lean`, checked by `#guard`.
-/

namespace Strata.Dyn.ExecTest.RunTest

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
  | "bad" => [inc, fail, chain, bad]
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
  | "badC" => [inc, badC]
  | "sumLate" => [sumLate]
  | "typed" => [incI, typed]
  | "closure" => [addRef, closure]
  | "callsClo" => [addRef, callsClo]
  | "assumePos" => [assumePos]
  | "pickN" => [pickN]
  | "pickI" => [pickI]
  | "pick2" => [pick2]
  | "twoCells" => [addCells, twoCells]
  | "noCells" => [incI, noCells]
  | _ => []

/-- Run `f` of the checked module `m` on `args`; a module that is not well formed faults
before the first step. -/
def runIn (m : Except Fault (Module E Unit)) (f : Name) (args : Array ExSem.model.Arg)
    (fuel : Nat := 10000) (oracle : Nat → Nat := fun _ => 0) : Outcome ExSem.model :=
  match m with
  | .ok m => runModule ExSem.model m f args fuel oracle
  | .error e => .failed ExSem.model e

/-- Run `f` on `args`, in a module of what it needs. -/
def run (f : String) (args : Array Int) (fuel : Nat := 10000) (oracle : Nat → Nat := fun _ => 0) :
    Outcome ExSem.model :=
  runIn (mod (needs f)) (nm f) (args.map (ExSem.model.arg ·)) fuel oracle

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

/-- What a run produced: its value, its fault, the world and the
choices made. -/
def summary (o : Outcome ExSem.model) :
    Option Int × Option (Bool × Int) × Option Fault × ExRules.World × Nat :=
  (intOf o.result, excOf o.result, faultOf o.result, o.snapshot.world, o.drawn)

/-! ## Results

Each program on `runFused`. -/

-- Straight-line code, and the leave out of the function.
#guard intOf (run "arith" #[3, 4]).result = some 6

-- A result read at its type, and at another: `arith` returns an `Int`, not a `Bool` nor an
-- `Except Int Int`.
#guard (run "arith" #[3, 4]).read? Int = some 6
#guard (run "arith" #[3, 4]).read? Bool = none
#guard ((run "arith" #[3, 4]).read? (Except Int Int)).isNone
-- `fib` returns an `Except Int Int`, not an `Int`.
#guard excOf (run "fib" #[10]).result = some (true, 55)
#guard (run "fib" #[10]).read? Int = none
-- A fault has no value at any type.
#guard (run "halts" #[]).read? Int = none

-- A block loop: edges, and a header that reads the entry block's parameter.
#guard intOf (run "sum" #[10]).result = some 45

-- A rule that falls through, and one that takes its `^err` successor.
#guard intOf (run "safeDiv" #[7, 2]).result = some 3
#guard intOf (run "safeDiv" #[7, 0]).result = some (-1)

-- Calls: a return to the rule, and an `error` the rule raises along `^err`.
#guard intOf (run "chain" #[5]).result = some 106

-- Recursive calls, returning `Except`.
#guard excOf (run "fib" #[10]).result = some (true, 55)

-- A code pointer at another signature than its function's is rejected before the first step:
-- the module is not well formed.
#guard faultOf (run "bad" #[1]).result = some (.invalid "not well formed: [bad]")

-- A rule's call of a closure, which the machine checks.
#guard intOf (run "typed" #[5]).result = some 6

-- A partial application, called by a rule and by `base.callCode`, which sees a write to the
-- ref it captured.
#guard intOf (run "closure" #[5]).result = some 19
#guard intOf (run "callsClo" #[10]).result = some 10

-- Static calls: recursion, a code pointer as an argument, and one read from a cell.
#guard intOf (run "fibC" #[8]).result = some 21
#guard intOf (run "useTwice" #[5]).result = some 7
#guard intOf (run "viaCell" #[5]).result = some 6

-- A code pointer typed at another signature than its function's is rejected before the first
-- step: the module is not well formed.
#guard faultOf (run "badC" #[1]).result = some (.invalid "not well formed: [badC]")

-- Blocks out of dominator order run as they do in order.
#guard intOf (run "sumLate" #[10]).result = some 45

-- Regions over a cell, and a jump to its `Again`.
#guard intOf (run "count" #[4]).result = some 4

-- Comprehensions, whose state is their rules' own: squares, of no elements, and with a body
-- that raises at the third element, which stops the comprehension; the same from a first run
-- that only sets the state up; and one comprehension in another's body.
#guard summary (run "squares" #[4, -1]) = (some 10409, none, none, { out := ⟨#[0, 1, 2, 3]⟩ }, 0)
#guard summary (run "squares" #[0, -1]) = (some 0, none, none, {}, 0)
#guard summary (run "squares" #[5, 2]) = (some (-2), none, none, { out := ⟨#[0, 1, 2]⟩ }, 0)
#guard summary (run "squaresR" #[4, -1]) = (some 10409, none, none, { out := ⟨#[0, 1, 2, 3]⟩ }, 0)
#guard summary (run "squaresR" #[0, -1]) = (some 0, none, none, {}, 0)
#guard summary (run "squaresR" #[5, 2]) = (some (-2), none, none, { out := ⟨#[0, 1, 2]⟩ }, 0)
#guard intOf (run "tables" #[3]).result = some 10404

-- A fold, whose state is its accumulator: it doubles from `1` while below `n`, and not at
-- all if `1` is not below `n`.
#guard summary (run "powAbove" #[100]) =
  (some 128, none, none, { out := ⟨#[1, 2, 4, 8, 16, 32, 64]⟩ }, 0)
#guard summary (run "powAbove" #[1]) = (some 1, none, none, {}, 0)

-- The world and the oracle.
#guard summary (run "noisy" #[5] (oracle := fun _ => 3)) =
  (some 5, none, none, { out := ⟨#[5]⟩, ticks := ⟨2⟩ }, 1)

-- Three choices, in order.
#guard intOf (run "coins" #[] (oracle := fun i => i + 1)).result = some 123

-- A gap after a world update keeps the update.
#guard summary (run "gapAfter" #[2]) =
  (none, none, some (.gap "ex.gap"), { out := ⟨#[2]⟩ }, 0)

-- A terminator's failure.
#guard faultOf (run "halts" #[]).result = some (.failure "ex.halt")

-- An assumption that holds continues, and one that fails blocks the path.
#guard intOf (run "assumePos" #[5]).result = some 5
#guard faultOf (run "assumePos" #[-5]).result = some (.blocked "ex.assume")

-- An unbounded choice is the oracle's number, under each oracle, and `chooseInt` numbers the
-- integers `0, -1, 1, -2, 2, …`.
#guard intOf (run "pickN" #[] (oracle := fun _ => 7)).result = some 7
#guard intOf (run "pickN" #[] (oracle := fun _ => 123456789)).result = some 123456789
#guard (List.range 5).map (fun k => intOf (run "pickI" #[] (oracle := fun _ => k)).result) =
  [some 0, some (-1), some 1, some (-2), some 2]

-- A closure over two cells, made by one rule's binds, reads the cells when it is called; one
-- over no cells is the code pointer.
#guard intOf (run "twoCells" #[3]).result = some 123
#guard intOf (run "noCells" #[3]).result = some 4

-- `choose 2` reduces the oracle's `7` below `3`.
#guard intOf (run "pick2" #[] (oracle := fun _ => 7)).result = some 1

-- Running out of fuel.
#guard faultOf (run "sum" #[100] (fuel := 50)).result = some .outOfFuel

-- Faults before the first step: a missing rule, and a module that is not well formed, since
-- it reads a value out of scope.
#guard faultOf (runIn missing (nm "f") #[] 100).result =
  some (.missingRules #[.str (.str .base "ex") "nope"])
#guard faultOf (runIn unscoped (nm "f") #[ExSem.model.arg true] 100).result =
  some (.invalid "not well formed: [f]")

-- A function constant that names no function of the module: the module is not well formed.
#guard faultOf (runIn (mod [Programs.chain]) (nm "chain") #[ExSem.model.arg (1 : Int)] 100).result =
  some (.invalid "not well formed: [chain]")

/-! ## Checked calls

Every closure a module makes is at its function's signature, so a call's check fails only on a
closure from outside: here, a start argument at the machine's token.  `twiceAt` calls its
argument twice by `base.callCode`. -/

/-- Run `twiceAt` on a closure of function `idx` with captures cell `captured`, and `x`. -/
def twiceOn (idx captured : Nat) (x : Int) : Option Fault × Option Int :=
  match mod [incI, inc, twiceAt] with
  | .error e => (some e, none)
  | .ok m => match prepare ExSem.model m (nm "twiceAt") with
    | .error e => (some e, none)
    | .ok ⟨_, hw, i⟩ =>
      let f : FnRef Run [Int] Int := ⟨⟨idx, captured, trivial⟩⟩
      let o := runPrepared hw i #[⟨ExSem.T.base.Fn (.list [ExSem.T.base.Int]) ExSem.T.base.Int, f⟩,
        ⟨ExSem.T.base.Int, x⟩] 1000 (fun _ => 0)
      (faultOf o.result, intOf o.result)

-- At `incI`, its signature: two calls.
#guard twiceOn 0 0 5 = (none, some 7)
-- At `inc`, which returns an `Except`, and at `incI` with a captures cell that does not exist.
#guard twiceOn 1 0 5 = (some (.badCall (nm "inc")), none)
#guard twiceOn 0 3 5 = (some (.badCall (nm "incI")), none)
-- Past the module's functions.
#guard twiceOn 7 0 5 = (some (.badCall (.num .base 7)), none)

/-! ## The machine, directly -/

/-- `k` applied to the configuration that runs `f` on `args`, or `d` if it does not start. -/
def withStart {β : Type} (f : String) (args : Array Int)
    (k : {m : LModule ExSem.model.at} → {B : Ty} → WF m →
      (s : State ExSem.model.at) → StateOK m B s → β) (d : β) : β :=
  match mod (needs f) >>= link ExSem.model with
  | .error _ => d
  | .ok lm => match hw : checkModule lm with
    | .error _ => d
    | .ok () => match lm.funcIndex (nm f) with
      | none => d
      | some i => match start hw i (args.map (ExSem.model.arg · Run)).toList with
        | .error _ => d
        | .ok ⟨_, s, h⟩ => k hw s h

/-- A run's end, as its result. -/
def endResult {m : LModule ExSem.model.at} {B : Ty} :
    RunEnd m B → Option (Result (ExSem.model.interp Run))
  | .done r _ _ _ => some r
  | .timeout .. => none

-- A timeout resumes: `runFused` on 30 steps, then on more, ends as one run does.
#guard withStart "sum" #[10] (fun hw s h => match runFused hw (fun _ => 0) 30 s h with
  | .timeout s₁ h₁ => (endResult (runFused hw (fun _ => 0) 1000 s₁ h₁)).bind intOf
  | .done .. => none) none = some 45

-- An event counter: it counts every step but the last, which ends the run.
#guard withStart "chain" #[5] (fun hw s h =>
  let (e, n) := runHooked hw (fun _ => 0) (fun (n : Nat) _ _ => .continue (n + 1)) 1000 0 s h
  ((e.toRunEnd.bind endResult).bind intOf, n)) (none, 0) = (some 106, 19)

/-- A breakpoint on entering `fib`: it stops at each call, and resuming ends as the run
does. -/
def fibBreak : {m : LModule ExSem.model.at} → {B : Ty} → Hook m B Nat :=
  fun n ev _ =>
  if ev = .enter (nm "fib") then .stop (n + 1) else .continue n

#guard (mod [fib] >>= fun m =>
    debugRun ExSem.model m (nm "fib") #[ExSem.model.arg (4 : Int)] 1000 fibBreak 0).toOption.map
  (fun r => (r.stops.size, r.st, r.result.bind excOf)) = some (8, 8, some (true, 3))

/-- Record the oracle's answers with a hook, then replay them from a tape. -/
def recorder : {m : LModule ExSem.model.at} → {B : Ty} → Hook m B (List Nat) :=
  fun l ev _ =>
  match ev with
  | .answer (.choose k) => .continue (l ++ [k])
  | _ => .continue l

#guard withStart "coins" #[] (fun hw s h =>
  (runHooked hw (fun i => 2 * i + 4) recorder 1000 [] s h).2) [] = [4, 6, 8]
#guard intOf (run "coins" #[] (oracle := tapeOracle [4, 6, 8])).result = some 468

end Strata.Dyn.ExecTest.RunTest
