/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Examples.While.Lower
public import StrataDyn.Exec.Run
-- Running a module needs the environment representation at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Running While programs

`run p f args` lowers `p`, then links, validates and runs its function `f` on integer
arguments against `WhileSem.model`.  `showOutcome` prints how a run ended: `ok v` for a value,
`raised e` for an `error e` that left the function, or the fault.
-/

namespace Strata.Dyn.While

open Strata.Dyn.Exec

@[expose] public section

/-- A value of the While model at the token `σ`. -/
abbrev Val (σ : Type) [Store σ] := Dyn (WhileSem.model.interp σ)

/-- Lower `p` and run its function `f` on `args` for at most `fuel` steps of `engine`, with
the oracle `oracle`. -/
def run (p : Ast.Program) (f : String) (args : Array Int) (fuel : Nat := 100000)
    (oracle : Nat → Nat := fun _ => 0) (engine : Engine := .fused) :
    Except String (Outcome WhileSem.model) := do
  let m ← lower p
  return runModule WhileSem.model m (nm f) (args.map (WhileSem.model.arg ·)) fuel oracle engine

def showList : While.IntList.Val → String
  | .nil => "nil"
  | .cons h t => s!"{h} :: {showList t}"

section
variable {σ : Type} [Store σ]

/-- `d` as an `α`, if it is one. -/
def Val.read? (d : Val σ) (α : Type) [@TagOf σ _ (WhileSem.model.decode σ) α] : Option α :=
  WhileSem.model.read? (.ok d) α

/-- A value of one of While's types, other than a cell. -/
def showPlain (d : Val σ) : Option String :=
  match d.read? Int, d.read? Bool, d.read? Unit, d.read? While.IntList.Val with
  | some n, _, _, _ => some (toString n)
  | _, some b, _, _ => some (toString b)
  | _, _, some (), _ => some "unit"
  | _, _, _, some l => some (showList l)
  | _, _, _, _ => none

/-- `d` as an `Except Int α`, shown with `shw`: `ok v`, or `raised e`. -/
def showExcept (d : Val σ) (α : Type) [@TagOf σ _ (WhileSem.model.decode σ) α]
    (shw : α → String) : Option String :=
  (d.read? (Except Int α)).map fun
    | .ok v => s!"ok {shw v}"
    | .error e => s!"raised {e}"

/-- A function's result: `ok v`, or `raised e` from a function that may raise. -/
def showResult (d : Val σ) : String :=
  match (showPlain d).map (s!"ok {·}") with
  | some s => s
  | none => ((showExcept d Int toString) <|> (showExcept d Bool toString) <|>
      (showExcept d Unit fun () => "unit") <|> (showExcept d While.IntList.Val showList)).getD
      "ok <cell>"

end

def showFault : Fault → String
  | .gap msg => s!"gap: {msg}"
  | .failure msg => s!"failure: {msg}"
  | .blocked msg => s!"blocked: {msg}"
  | .badCall f => s!"bad call of {nameStr f}"
  | .badCell l => s!"bad cell at {l}"
  | .outOfFuel => "out of fuel"
  | .missingRules ops => s!"no rules for {ops.toList.map nameStr}"
  | .invalid msg => s!"invalid: {msg}"
  | .noFunction f => s!"no function {nameStr f}"

/-- How a run ended. -/
def showOutcome (o : Outcome WhileSem.model) : String :=
  match o.result with
  | .ok d => showResult d
  | .fault f => s!"fault {showFault f}"

end

end Strata.Dyn.While
