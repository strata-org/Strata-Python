/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.PythonDialect -- shake: keep

/-! ## Golden interpret tests for both front ends

Runs `StrataPythonTest/run_py_interpret.sh`, which compiles each
`StrataPythonTest/tests/test_*.py` to Ion, runs the compiled `pyInterpret` binary
on it (Python → Core → concrete execution, no verification), and compares the
result against that front end's expectations.

This used to reimplement the interpret pipeline in-process inside `#eval` in
`StrataPythonTest/CI/InterpretTests.lean`, which ran in the Lean interpreter for
every test file — 244s for 309 cases at elaboration time, so a hard build error
rather than a test failure. Delegating to the shell script builds the native
binary once and runs it as a subprocess per file, which is ~4x faster per case
and makes room for running the corpus twice.

The whole corpus runs twice, once per front end: the default V1 pipeline (Python →
Laurel → Core), whose expectations are in `StrataPythonTest/expected_interpret_v1/`,
and then the V2 pipeline (Resolution → Translation → Elaboration → Core), whose
expectations are in `StrataPythonTest/expected_interpret/`. See
`StrataPythonTest/expected_interpret/README.md` for why the sets sit at those paths
and an inventory of what currently differs between them.

The two runs are sequential rather than separate concurrent test files because they
share scratch state: both regenerate `tests/*.python.st.ion`.

Requires Python with `strata_python.gen` (the build exports `PYTHON`). Unlike the
analyze goldens this needs no SMT solver — nothing here is verified. Run from the
package root via `lake test`. -/

meta section

/-- Run `run_py_interpret.sh` with `extraArgs` and return its exit code. -/
private def runInterpretGoldens (extraArgs : Array String) : IO UInt32 := do
  -- The script resolves paths relative to its own directory, but `lake build` inside
  -- it wants the package root, so run it from `StrataPythonTest/` as the analyze
  -- goldens do. Use .inherit for stdout/stderr so output streams to the terminal in
  -- real time rather than being buffered until the process exits.
  let child ← IO.Process.spawn {
    cmd := "bash"
    args := #["run_py_interpret.sh"] ++ extraArgs
    cwd := some "StrataPythonTest"
    -- Inherit PYTHON / PYTHONPATH exported by the build so the script's
    -- `strata_python.gen` uses the right interpreter.
    inheritEnv := true
    stdout := .inherit
    stderr := .inherit
  }
  child.wait

#eval show IO Unit from do
  let script : System.FilePath := "StrataPythonTest/run_py_interpret.sh"
  unless ← script.pathExists do
    throw <| IO.userError s!"interpret golden test script not found: {script} \
                            (run from the package root, e.g. via `lake test`)"
  -- Run both front ends before reporting, so one failing front end does not hide
  -- the other's results.
  let v1Exit ← runInterpretGoldens #[]
  let v2Exit ← runInterpretGoldens #["--v2"]
  let failures :=
    (if v1Exit != 0 then ["V1 (Python → Laurel → Core)"] else [])
    ++ (if v2Exit != 0 then ["V2 (Resolution → Translation → Elaboration → Core)"] else [])
  unless failures.isEmpty do
    throw <| IO.userError s!"run_py_interpret.sh failed for \
                            {String.intercalate " and " failures}; see output above"

end -- meta section
