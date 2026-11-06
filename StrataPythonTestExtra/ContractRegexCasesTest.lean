/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python -- shake: keep

/-! ## The regular-expression cases of `py.reSearch` are CPython 3.12's

`StrataPythonTest/Dyn/Sem/Contracts/RegexTest.lean` checks the matcher against the cases of
`RegexCases.lean` with no Python.  This test runs their generator, `regex_cases.py`, again with
CPython 3.12, and fails if its output differs from the checked-in file, so the cases can't go
stale.  It skips when the Python it finds is not 3.12. -/

open StrataPython (withPython getPython3Version)

namespace StrataPython.ContractRegexCasesTest

meta section

def generator : System.FilePath := "StrataPythonTest" / "Dyn" / "contract_rules" / "regex_cases.py"
def casesFile : System.FilePath := "StrataPythonTest" / "Dyn" / "Sem" / "Contracts" / "RegexCases.lean"

def main : IO Unit := withPython fun python => do
  if (← getPython3Version python.toString) != some 12 then
    IO.println s!"skipped: {python} is not CPython 3.12"
    return
  let out ← IO.Process.output { cmd := python.toString, args := #["-I", generator.toString] }
  if out.exitCode != 0 then
    throw <| .userError s!"{generator} failed:\n{out.stderr}"
  if out.stdout != (← IO.FS.readFile casesFile) then
    throw <| .userError s!"{casesFile} differs from the output of {generator}"

end

end StrataPython.ContractRegexCasesTest

#eval StrataPython.ContractRegexCasesTest.main
