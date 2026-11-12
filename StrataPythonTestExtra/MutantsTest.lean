/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python -- shake: keep

/-! ## The mutants still apply, and are recorded as caught

`StrataPythonTest/Dyn/differential/mutants.py` lists textual changes to the rules, each of which a
test program must catch; its manual `--run` records which one does. This test runs its `--check`,
which fails if a mutant's old text no longer occurs exactly once in its file, so that the mutants
can't rot silently when the rules change, or if `mutants_results.txt` doesn't record each mutant
as caught with the blobs of its files. It prints the results whose mutated file or catching
program changed since they were measured, as `--check` reports them. -/

namespace StrataPython.MutantsTest

meta section

def script : System.FilePath := "StrataPythonTest/Dyn/differential/mutants.py"

def main : IO Unit := do
  withPython fun pythonCmd => do
    let out ← IO.Process.output { cmd := pythonCmd.toString, args := #[script.toString, "--check"] }
    if out.exitCode != 0 then
      throw <| .userError s!"{script} --check failed:\n{out.stderr}"
    unless out.stdout.isEmpty do IO.print out.stdout

end

end StrataPython.MutantsTest

#eval StrataPython.MutantsTest.main
