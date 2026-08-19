/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.PythonDialect -- shake: keep

/-! ## Golden analyze tests for `pyAnalyzeLaurel` and `pyAnalyzeV2`

Runs `StrataPythonTest/run_py_analyze.sh`, which compiles each
`StrataPythonTest/tests/test_*.py` to Ion, runs the compiled analyzer binary on
it, normalizes unstable assertion-label IDs (see
`StrataPythonTest/normalize_labels.py`), and diffs the result against that
front-end's golden `.expected` files.

This used to reimplement the analyze pipeline in-process inside `#eval`, which
ran in the Lean interpreter (slow) for every test file. Delegating to the shell
script builds the native binary once and runs it as a subprocess per file,
which is dramatically faster while exercising the same code path the CLI uses.

The whole corpus runs twice, once per front-end: the default V1 pipeline
(`pyAnalyzeLaurel`), whose goldens are in `StrataPythonTest/expected_laurel_v1/`,
and then the V2 pipeline (`pyAnalyzeV2`, i.e. Resolution → Translation →
Elaboration → Core), whose goldens are in `StrataPythonTest/expected_laurel/`.
See `StrataPythonTest/expected_laurel/README.md` for why the sets sit at those
paths and an inventory of what currently differs between them.

The two runs are sequential rather than separate concurrent test files because
they share scratch state: both regenerate `tests/*.python.st.ion`, and the
analyzer writes `user_errors.txt` into its working directory (`Cli.lean`), so
running them at the same time would have them clobber each other's files.

Requires Python with `strata_python.gen` (the build exports `PYTHON`) and the
SMT solvers cvc5 and z3 on PATH. Run from `StrataPythonTestExtra/` via
`lake test`. -/

meta section

/-- Run `run_py_analyze.sh` with `extraArgs` and return its exit code. -/
private def runAnalyzeGoldens (extraArgs : Array String) : IO UInt32 := do
  -- The script resolves paths relative to `StrataPythonTest/`, so run it there.
  -- Use .inherit for stdout/stderr so output streams to the terminal in real
  -- time rather than being buffered until the process exits.
  let child ← IO.Process.spawn {
    cmd := "bash"
    args := #["run_py_analyze.sh"] ++ extraArgs
    cwd := some "StrataPythonTest"
    -- Inherit PYTHON / PYTHONPATH exported by the build so the script's
    -- `strata_python.gen` and normalizer use the right interpreter.
    inheritEnv := true
    stdout := .inherit
    stderr := .inherit
  }
  child.wait

#eval show IO Unit from do
  let script : System.FilePath := "StrataPythonTest/run_py_analyze.sh"
  unless ← script.pathExists do
    throw <| IO.userError s!"analyze golden test script not found: {script} \
                            (run from the package root, e.g. via `lake test`)"
  -- Run both front-ends before reporting, so one failing front-end does not
  -- hide the other's results.
  let v1Exit ← runAnalyzeGoldens #[]
  let v2Exit ← runAnalyzeGoldens #["--v2"]
  let failures :=
    (if v1Exit != 0 then ["V1 (pyAnalyzeLaurel)"] else [])
    ++ (if v2Exit != 0 then ["V2 (pyAnalyzeV2)"] else [])
  unless failures.isEmpty do
    throw <| IO.userError s!"run_py_analyze.sh failed for \
                            {String.intercalate " and " failures}; see output above"

end -- meta section
