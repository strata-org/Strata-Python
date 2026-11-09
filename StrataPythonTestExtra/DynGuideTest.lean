/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! # The Dyn guide stays true to the package

The guide in `docs/dyn/` is a Lake project of its own, built by hand, so nothing else checks it
against the package's sources. This test runs its two checks:

* `docs/dyn/scripts/export-data.py --check`: every listing and panel copy equals its source,
  and every excerpt that the guide quotes from the package is still in the package;
* each file of `docs/dyn/checks/`: it compiles against the package and prints nothing, since its
  `#guard_msgs` pins match and the texts of `docs/dyn/data/` that it checks are what the package
  gives.

The script runs with `PYTHON`, as the build exports it, or with `python3`. -/

namespace StrataPython.DynGuideTest

/-- The guide's directory, from the package root. -/
private meta def guideDir : System.FilePath := "docs" / "dyn"

/-- The files of `docs/dyn/checks/`, in order: a check that is deleted or added must be listed
here, so that the test cannot pass by running none. -/
private meta def expectedChecks : Array String :=
  #["Exec.lean", "Lowering.lean", "RefToReg.lean", "TypedMean.lean"]

/-- Run `cmd args`, and return its exit code and its output, stdout then stderr. -/
private meta def run (cmd : String) (args : Array String) : IO (UInt32 × String) := do
  let out ← IO.Process.output { cmd, args }
  return (out.exitCode, out.stdout ++ out.stderr)

#eval show IO Unit from do
  let python := (← IO.getEnv "PYTHON").getD "python3"
  let mut failures := #[]
  let (code, out) ← run python #["-I", (guideDir / "scripts" / "export-data.py").toString, "--check"]
  if code != 0 then failures := failures.push s!"export-data.py --check failed:\n{out}"
  let checks := (← (guideDir / "checks").readDir).filter (·.fileName.endsWith ".lean")
  let checks := checks.qsort (·.fileName < ·.fileName)
  let names := checks.map (·.fileName)
  unless names == expectedChecks do
    failures := failures.push s!"docs/dyn/checks/ holds {names}, expected {expectedChecks}"
  for c in checks do
    let (code, out) ← run "lean" #[c.path.toString]
    if code != 0 || !out.isEmpty then failures := failures.push s!"{c.path} failed:\n{out}"
  IO.println s!"DynGuideTest: sync check and {checks.size} Lean checks, {failures.size} failure(s)"
  if !failures.isEmpty then
    for f in failures do IO.println f
    throw <| IO.userError s!"DynGuideTest: {failures.size} failure(s)"

end StrataPython.DynGuideTest
