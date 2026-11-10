/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- `withPython` (the interpreter locator that honours `SKIP_PYTHON_TESTS`) is
-- re-exported to the generated children: each child `#eval`s `runInterpretCase`,
-- whose body calls it, so the symbol must reach them transitively.
public meta import StrataPythonTest.Util.Python
-- The compile+run pipeline (`compileAndRun`) and the failure-to-pattern helpers are
-- shared with `Scripts.pyInterpretUpdate` so the read and write sides cannot drift.
-- They are used by `runOnePass` at meta time and re-exported to the generated
-- children (which run `runInterpretCase`), hence both import forms.
public meta import StrataPythonTest.InterpretGolden.Matching
public import StrataPythonTest.InterpretGolden.Matching
import Strata.Util.Tests

open StrataPython.GoldenText

/-! ## Golden interpret tests for both front ends (dynamically generated)

Runs the compiled `pyInterpret` binary (Python → Core → concrete execution, no
verification) on every `StrataPythonTest/tests/test_*.py` and compares the result
against each front end's expectations. This file is the *generator*: it declares
one `#eval runInterpretCase "<stem>"` per corpus file and writes one child
module per entry under `StrataPythonTestExtra/InterpretGolden/Gen/`, which
`testMain` runs as its own `lean` process. The children run concurrently, so the
corpus is spread across cores.

`#test_for_each_file` reads the corpus directory at build time so the set of
children tracks `tests/`, and `#run_tests_as_modules` checks the committed children
against what this file would emit; on drift it regenerates them and fails the build
until they are committed. Re-baselining the `.expected` files
and reporting the V1/V2 divergence are not test-time concerns; the
`pyInterpretUpdate` executable does those.

Each corpus file runs under both front ends: the default V1 pipeline (Python →
Laurel → Core), whose expectations live in `StrataPythonTest/expected_interpret_v1/`,
and the V2 pipeline (Resolution → Translation → Elaboration → Core), whose
expectations live in `StrataPythonTest/expected_interpret/`. See
`expected_interpret/README.md` for why the sets sit at those paths. The imported
regression corpus is V2-only, marked by a `.desired` sidecar in
`expected_interpret/`; a case with that marker skips its V1 run.

For one front end, the presence of `<expected_dir>/<stem>.expected` says the case
is expected to fail (non-zero exit) with output matching the regex that file holds;
its absence says the case is expected to pass (exit 0); a `<stem>.skip` sidecar
skips the case. A parse failure (the Python front end cannot lower the file to Ion)
is a silent skip rather than a failure.

Requires Python with `strata_python.gen` (the build exports `PYTHON`) and the
`pyInterpret` binary, which `StrataPythonFrontEndTestMain` lists in its `needs` so
`lake test` builds it once. Unlike the analyze goldens this needs no SMT solver —
nothing here is verified. Generation itself (the two commands at the foot of this
file) runs at build time and needs neither Python nor the binary; only the children
`testMain` later spawns do. -/

namespace StrataPython.InterpretGolden

meta section

/-- Run one front end (`v2` selects V2 over V1) on one corpus case and throw on any
    failure, so the child `lean` process exits non-zero and `testMain` reports it.
    A `.skip` sidecar or a parse failure returns quietly (the case passes). -/
private def runOnePass (pythonCmd root : System.FilePath) (stem : String) (v2 : Bool)
    : IO Unit := do
  let feName := if v2 then "V2" else "V1"
  let expectedDir := root / "StrataPythonTest" /
    (if v2 then "expected_interpret" else "expected_interpret_v1")
  -- `.skip` → skip (the file's contents are the human-facing reason).
  if ← (expectedDir / (stem ++ ".skip")).pathExists then
    return
  let some (exitCode, output) ← compileAndRun pythonCmd.toString root stem v2
    | return  -- the Python front end could not lower the file to Ion: a silent skip
  let expectedFile := expectedDir / (stem ++ ".expected")
  if ← expectedFile.pathExists then
    let pattern := rstripNewlines (← IO.FS.readFile expectedFile)
    if pattern.isEmpty then
      throw <| .userError s!"{stem} [{feName}]: empty .expected file — must contain a pattern"
    if exitCode == 0 then
      throw <| .userError
        s!"{stem} [{feName}]: expected a failure matching /{pattern}/ but the case passed"
    else if ← matchesPattern pattern output then
      return
    else
      throw <| .userError <|
        s!"{stem} [{feName}]: output does not match expected pattern /{pattern}/\n"
        ++ s!"  actual: {failureReason output}\n"
        ++ s!"  full output:\n{output}"
  else
    if exitCode == 0 then
      return
    else
      throw <| .userError
        s!"{stem} [{feName}]: expected the case to pass but it failed — \
           {failureReason output}\n{output}"

/-- Run one corpus case under both front ends (V1 skipped for an imported V2-only
    case). `withPython` supplies the interpreter and honours `SKIP_PYTHON_TESTS`, so
    the whole case is skipped where the toolchain is absent. -/
public def runInterpretCase (stem : String) : IO Unit :=
  withPython fun pythonCmd => do
    let root ← IO.currentDir
    -- Run both front ends before reporting, so a V1 failure does not hide the V2
    -- result (or vice versa); collect each pass's error and throw once at the end.
    let mut errs : Array String := #[]
    unless ← (root / "StrataPythonTest" / "expected_interpret" / (stem ++ ".desired")).pathExists do
      try runOnePass pythonCmd root stem (v2 := false)
      catch e => errs := errs.push e.toString
    try runOnePass pythonCmd root stem (v2 := true)
    catch e => errs := errs.push e.toString
    unless errs.isEmpty do
      throw <| .userError (String.intercalate "\n" errs.toList)

end -- meta section

end StrataPython.InterpretGolden

open StrataPython.InterpretGolden

-- Declare one `#eval runInterpretCase "<stem>"` per `tests/test_*.py`, then
-- check (and on drift regenerate) the child modules. The directory is read at
-- build time, so the generated set tracks the corpus.
#test_for_each_file "StrataPythonTest/tests" "test_" ".py" runInterpretCase
#run_tests_as_modules "StrataPythonTestExtra/InterpretGolden/Gen"
