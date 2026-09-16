/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.PythonDialect -- shake: keep

/-! ## CPython-as-oracle test

Runs `StrataPythonTest/cpython_oracle/run_cpython_oracle.sh`, which rewrites eligible
test methods from CPython's own regression suite into self-contained programs, runs
each under `pyInterpret` AND under CPython, and compares the outcomes.

Unlike the golden suites, this test has no `.expected` files: CPython is the
expectation. Nothing it finds fails the run -- a construct Strata cannot handle yet is
the point of the suite, so failing on one would leave the build permanently red. It
fails only if a stage itself breaks.

The verifier is deliberately not used: its verdicts are conditional ("always true/false
if reached, reachability unknown"), so pairing them with an oracle needs a reachability
fact and a per-obligation location join. The interpreter answers the question directly.

The corpus comes from the `CPython312Runtime` build-tool dependency, whose
`pkg.src` carries the upstream release tarball; the suite reads `Lib/test/*.py`
straight out of it. Nothing is downloaded and nothing needs provisioning, so this
runs alongside the other suites by default. It needs `brazil-path` to resolve that
dependency, which holds during a build but not in every bare `lake test`, so a
corpus it cannot locate is reported as a skip rather than a failure.

- `CPYTHON_ORACLE=0` — skip the suite.
- `CPYTHON_ORACLE_WORKERS` — parallelism, default 4. Deliberately small: testMain
  launches ~21 test files at once and a development build was killed for low memory
  at that concurrency, so this suite bounds its own fan-out.
- `CPYTHON_ORACLE_ARGS` — extra flags, space separated (e.g. `--filter test_dict`).

Runtime is about 130 seconds for the whole language-level corpus (66 files, ~1,330
methods) at 4 workers.

This suite regenerates `cpython_oracle/build/`, which no other test touches, so it
does not need the corpus lock that the analyze and interpret suites share.
-/

meta section

namespace StrataPython.CpythonOracleTest

private def scriptPath : System.FilePath :=
  "StrataPythonTest/cpython_oracle/run_cpython_oracle.sh"

/-- Run the suite, returning its exit code. -/
private def runSuite (extraArgs : Array String) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "bash"
    args := #["run_cpython_oracle.sh"] ++ extraArgs
    cwd := some "StrataPythonTest/cpython_oracle"
    -- Inherit PYTHON / PYTHONPATH exported by the build so `strata_python.gen`
    -- and the oracle use the interpreter the corpus was pinned against.
    inheritEnv := true
    stdout := .inherit
    stderr := .inherit
  }
  child.wait

def main : IO Unit := do
  if (← IO.getEnv "CPYTHON_ORACLE") == some "0" then
    IO.println "CPYTHON_ORACLE=0; skipping CPython oracle test."
    return
  unless ← scriptPath.pathExists do
    throw <| IO.userError s!"CPython oracle script not found: {scriptPath} \
                            (run from the package root, e.g. via `lake test`)"
  let extra ← match ← IO.getEnv "CPYTHON_ORACLE_ARGS" with
    | some s => pure (s.splitOn " " |>.map (·.trimAscii.toString)
                        |>.filter (!·.isEmpty) |>.toArray)
    | none => pure #[]
  let code ← runSuite extra
  -- Exit 3 is the script's "corpus unavailable" signal: `brazil-path` could not
  -- resolve CPython312Runtime, which happens outside a Brazil build. That is a skip,
  -- not a failure -- the suite has nothing to run, and failing here would make a
  -- bare `lake test` red for a reason unrelated to the code under test.
  if code == 3 then
    IO.println "CPython corpus unavailable; skipping CPython oracle test."
  else unless code == 0 do
    throw <| IO.userError s!"run_cpython_oracle.sh failed (exit {code}); \
                            see output above"

end StrataPython.CpythonOracleTest

end -- meta section

#eval StrataPython.CpythonOracleTest.main
