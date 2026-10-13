/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPython.Mantle.Env
meta import StrataMantle.DDM
meta import StrataMantle.DDMRead
meta import StrataMantle.Env.WF
meta import StrataPythonTest.Mantle.TestUtil

/-! # Reading the translator goldens back

Reads every `NAME.expected.mantle` in `StrataPythonTest/Mantle/mantle_tests/` against `Py.env`,
the diagnostic lines before its module read as comments, and checks both printed forms:

* folded, as the goldens are, reprinting the module gives the golden's module text, byte for
  byte;
* in full, printing, reading and printing again gives the same text;
* no name read has a `.` inside a segment.

Nothing is excluded: the goldens' floats print as the shortest decimals that read back
exactly.  No Python is needed. -/

namespace StrataPython.MantleReadTest

open Strata.Mantle
open StrataPython.Mantle
open StrataPython.Mantle.TestUtil (firstDiff dottedNames)

/-- The directory holding the goldens. -/
private meta def testDir : System.FilePath := "StrataPythonTest" / "Mantle" / "mantle_tests"

/-- The suffix of a translator golden. -/
private meta def goldenSuffix : String := ".expected.mantle"

/-- The module part of a golden: from its `module` line on. -/
private meta def moduleText (golden : String) : String :=
  "\n".intercalate ((golden.splitOn "\n").dropWhile (!·.startsWith "module ")) |>.trimAsciiEnd
    |>.toString |>.push '\n'

/-- Check one golden, or say what is wrong with it. -/
private meta def check (path : System.FilePath) : IO (Option String) := do
  let golden ← IO.FS.readFile path
  let text := moduleText golden
  match ← Module.read Py.env golden path.toString with
  | .error e => return some s!"{path}: does not read back:\n{e}"
  | .ok m =>
    unless (dottedNames m.raw).isEmpty do
      return some s!"{path}: a name has a `.` inside a segment: {(dottedNames m.raw).map ToDDM.nameText}"
    if let some d := firstDiff (toString m) text then
      return some s!"{path}: reprints differently at {d}"
    let full := m.format .full
    match ← Module.read Py.env full s!"{path} (full)" with
    | .error e => return some s!"{path}: the full form does not read back:\n{e}"
    | .ok m' =>
      if let some d := firstDiff (m'.format .full) full then
        return some s!"{path}: the full form reprints differently at {d}"
      return none

#eval show IO Unit from do
  let goldens := (← testDir.readDir).filter (·.fileName.endsWith goldenSuffix)
  let goldens := goldens.qsort (·.fileName < ·.fileName)
  let mut failures := #[]
  for g in goldens do
    if let some msg ← check g.path then failures := failures.push msg
  IO.println s!"MantleReadTest: {goldens.size - failures.size}/{goldens.size} read back"
  if !failures.isEmpty then
    for f in failures do IO.println f
    throw <| IO.userError s!"MantleReadTest: {failures.size} failure(s)"

end StrataPython.MantleReadTest
