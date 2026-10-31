/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python -- shake: keep

/-! ## The Unicode tables and the library's cases are CPython 3.12's

`StrataPython/Dyn/Sem/Generated/Unicode.lean` and `LibraryUnicode.lean` hold CPython 3.12's
Unicode tables, and the case files of `StrataPythonTest/Dyn/Sem/Library/` its results of the
library's methods. This test runs their generators again with CPython 3.12, and fails if an
output differs from the checked-in file. It skips when the Python it finds is not 3.12. -/

namespace StrataPython.LibraryCasesTest

meta section

def tablesGenerator : System.FilePath := "StrataPythonTest/Dyn/Sem/gen_unicode.py"
def generatedDir : System.FilePath := "StrataPython/Dyn/Sem/Generated"
/-- The generators that print a case file, with the file. -/
def caseFiles : List (System.FilePath × System.FilePath) :=
  let dir : System.FilePath := "StrataPythonTest/Dyn/Sem/Library"
  [(dir / "gen_str_cases.py", dir / "StrCases.lean"),
   (dir / "gen_strmethod_cases.py", dir / "StrMethodCases.lean"),
   (dir / "gen_number_cases.py", dir / "NumberCases.lean"),
   (dir / "gen_codec_cases.py", dir / "CodecCases.lean")]
def scratchDir : System.FilePath := ".lake/build/library-cases-check"

/-- Run `python script args`, failing on a non-zero exit; its standard output. -/
def run (python : System.FilePath) (script : System.FilePath) (args : Array String) :
    IO String := do
  let out ← IO.Process.output { cmd := python.toString, args := #[script.toString] ++ args }
  if out.exitCode != 0 then
    throw <| .userError s!"{script} failed:\n{out.stderr}"
  return out.stdout

/-- Fail unless `a` and `b` have the same contents. -/
def same (a b : System.FilePath) : IO Unit := do
  if (← IO.FS.readFile a) != (← IO.FS.readFile b) then
    throw <| .userError s!"{b} differs from its generator's output; regenerate it with CPython 3.12"

def main : IO Unit := do
  withPython fun python => do
    if (← getPython3Version python.toString) != some 12 then
      IO.println s!"skipped: {python} is not CPython 3.12"
      return
    IO.FS.createDirAll scratchDir
    discard <| run python tablesGenerator #[scratchDir.toString]
    same (scratchDir / "Unicode.lean") (generatedDir / "Unicode.lean")
    same (scratchDir / "LibraryUnicode.lean") (generatedDir / "LibraryUnicode.lean")
    for (generator, file) in caseFiles do
      if (← run python generator #[]) != (← IO.FS.readFile file) then
        throw <| .userError s!"{file} differs from the output of {generator}"

end

end StrataPython.LibraryCasesTest

#eval StrataPython.LibraryCasesTest.main
