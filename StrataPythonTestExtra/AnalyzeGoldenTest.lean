/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.PythonDialect -- shake: keep

/-! ## Golden analyze tests for `pyAnalyzeLaurel`

Runs `StrataPythonTest/run_py_analyze.sh`, which compiles each
`StrataPythonTest/tests/test_*.py` to Ion, runs the compiled `pyAnalyzeLaurel`
binary on it, normalizes unstable assertion-label IDs (see
`StrataPythonTest/normalize_labels.py`), and diffs the result against the
golden `StrataPythonTest/expected_laurel/*.expected` files.

This used to reimplement the analyze pipeline in-process inside `#eval`, which
ran in the Lean interpreter (slow) for every test file. Delegating to the shell
script builds the native binary once and runs it as a subprocess per file,
which is dramatically faster while exercising the same code path the CLI uses.

Requires Python with `strata_python.gen` (the build exports `PYTHON`) and the
SMT solvers cvc5 and z3 on PATH. Run from `StrataPythonTestExtra/` via
`lake test`. -/

meta section

#eval show IO Unit from do
  let script : System.FilePath := "StrataPythonTest/run_py_analyze.sh"
  unless ← script.pathExists do
    throw <| IO.userError s!"analyze golden test script not found: {script} \
                            (run from the package root, e.g. via `lake test`)"
  -- The script resolves paths relative to `StrataPythonTest/`, so run it there.
  let child ← IO.Process.spawn {
    cmd := "bash"
    args := #["run_py_analyze.sh"]
    cwd := some "StrataPythonTest"
    -- Inherit PYTHON / PYTHONPATH exported by the build so the script's
    -- `strata_python.gen` and normalizer use the right interpreter.
    inheritEnv := true
    stdout := .piped
    stderr := .piped
  }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let out := (← IO.ofExcept stdout.get)
  -- Surface the script's output so failures are diagnosable in test logs.
  IO.print out
  unless stderr.isEmpty do IO.eprint stderr
  if exitCode != 0 then
    throw <| IO.userError s!"run_py_analyze.sh failed (exit {exitCode}); see output above"

end -- meta section
