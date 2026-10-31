/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Table
public import StrataDyn.DDMRead
public import StrataDyn.Exec.Run
import StrataDyn.DSL
import StrataDyn.Env.WF

/-! # The cost of Python's rules

`lake exe semPerf [N]` runs a function of `N` instructions `py.is` (default 20000), whose rule
runs the generic `Proto.isOp` in `PyM`, and the same function with `pt.isDirect`, the same rule
written directly in `Sem`, and `pt.isGet`, which also reads the store as `runTotal` does, and
prints the time per instruction of each run, after linking and checking.  Not run in CI. -/

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn StrataPython.Dyn.Sem

namespace SemPerf

/-- Python's environment, with `is` written directly. -/
public environment PyPerf extends Py where
  namespace pt
  open py
  insn isDirect (lhs rhs : Value) : Value
  insn isGet (lhs rhs : Value) : Value
  end pt

#dyn_types PyPerf

section
variable {ε : Eff} {E : Type}

/-- `is`, written directly in `Sem` over `Value`. -/
@[dyn_sem PyPerf.isDirect, expose] public def isDirect (a b : Value) : Sem ε E Value :=
  match a.identical b with
  | .yes => pure (.bool true)
  | .no => pure (.bool false)
  | .unknown => semanticGap "is on two equal immediates depends on CPython's caching"

/-- `is`, directly in `Sem`, after reading the store as `runTotal` does. -/
@[dyn_sem PyPerf.isGet, expose] public def isGet {σ : Type} [Store σ] [Decode σ] [PyLang σ ε]
    (a b : Value) : Sem ε E Value := do
  let _ ← getThe (ObjStore σ)
  match a.identical b with
  | .yes => pure (.bool true)
  | .no => pure (.bool false)
  | .unknown => semanticGap "is on two equal immediates depends on CPython's caching"
end

public section
#dyn_sem_table PerfSem for PyPerf (world := Sem.World)
end

/-- A module whose `main` runs `op` on `None` and `1` `n` times. -/
def program (op : String) (n : Nat) : String := Id.run do
  let mut lines := #["module m {", "  func @m.main() -> py.Value {", "    entry.0():",
    "      %a.0 : py.Value = py.noneLit", "      %b.0 : py.Value = py.intLit(1)"]
  for i in [0:n] do
    lines := lines.push s!"      %v.{i} : py.Value = {op}(%a.0, %b.0)"
  lines := lines ++ #[s!"      ret(%v.{n - 1})", "  }", "}"]
  return "\n".intercalate lines.toList

/-- The nanoseconds per instruction of `op`, best of `runs` runs. -/
def measure (op : String) (n runs : Nat) : IO Float := do
  let .ok m ← Module.read PyPerf.env (program op n) "perf.dyn" | throw (IO.userError "read")
  let .ok ⟨_, hw, i⟩ := prepare PerfSem.model m (.str (.str .base "m") "main")
    | throw (IO.userError "prepare")
  let mut best : Nat := 0
  for k in [0:runs] do
    let t0 ← IO.monoNanosNow
    let o := runPrepared hw i #[] (n + 10) (fun _ => 0)
    match o.result with
    | .ok _ => pure ()
    | .fault f => throw (IO.userError s!"fault {repr f}")
    let t1 ← IO.monoNanosNow
    if k == 0 || t1 - t0 < best then best := t1 - t0
  return best.toFloat / n.toFloat

end SemPerf

public def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 20000
  let generic ← SemPerf.measure "py.is" n 5
  let direct ← SemPerf.measure "pt.isDirect" n 5
  let withGet ← SemPerf.measure "pt.isGet" n 5
  IO.println s!"{n} instructions: generic {generic} ns each, direct {direct} ns each, \
    direct with a store read {withGet} ns each"
