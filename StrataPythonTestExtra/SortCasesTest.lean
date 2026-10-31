/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python -- shake: keep

/-! ## The sort cases are CPython 3.12's

`StrataDynTest/Util/SortCases.lean` holds CPython 3.12's runs of `list.sort`, which
`StrataDynTest/Util/SortTest.lean` checks the sort port against. This test runs the
generator, `StrataDynTest/Util/gen_sort_cases.py`, again with CPython 3.12, and fails if
its output differs from the checked-in file. It skips when the Python it finds is not 3.12. -/

namespace StrataPython.SortCasesTest

meta section

def casesFile : System.FilePath := "StrataDynTest/Util/SortCases.lean"
def generator : System.FilePath := "StrataDynTest/Util/gen_sort_cases.py"

def main : IO Unit := do
  withPython fun pythonCmd => do
    if (← getPython3Version pythonCmd.toString) != some 12 then
      IO.println s!"skipped: {pythonCmd} is not CPython 3.12"
      return
    let out ← IO.Process.output { cmd := pythonCmd.toString, args := #[generator.toString] }
    if out.exitCode != 0 then
      throw <| .userError s!"{generator} failed:\n{out.stderr}"
    if out.stdout != (← IO.FS.readFile casesFile) then
      throw <| .userError
        s!"{casesFile} differs from the output of {generator}; regenerate it with CPython 3.12"

end

end StrataPython.SortCasesTest

#eval StrataPython.SortCasesTest.main
