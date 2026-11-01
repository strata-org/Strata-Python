/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.TraceSource
meta import StrataPythonTest.Util.Python

/-! # Generated programs against CPython

Runs 500 random programs that call the built-in library with the Python semantics, and compares
each trace with CPython 3.12's. The programs come from the generator
`StrataPythonTest/Dyn/differential/gen_programs.py` with the seed 1. CPython's traces are kept in
`StrataPythonTest/Dyn/differential/generated.cpython.traces`, and the verdicts are pinned in
`StrataPythonTest/Dyn/differential/generated_expected.txt`. Set `SEM_UPDATE=1` to rewrite both
files (that needs CPython 3.12).

A larger run is a manual command: with `GEN_SEED=S` and `GEN_COUNT=N`, the test runs the `N`
programs of the seed `S` against CPython's traces computed live (with CPython 3.12), pins no
verdict and writes no file, and fails only on a program whose run disagrees with CPython, e.g.
`GEN_SEED=2 GEN_COUNT=20000 lake env lean StrataPythonTestExtra/GeneratedDiffTest.lean`.
-/

namespace StrataPython.GeneratedDiffTest

private meta def here : System.FilePath := "StrataPythonTest" / "Dyn" / "differential"

#eval withPython fun pythonCmd => do
  let script := here / "gen_programs.py"
  match (← IO.getEnv "GEN_SEED"), (← IO.getEnv "GEN_COUNT") with
  | some seed, some count =>
    let dir : System.FilePath := ".lake" / "build" / "differential" / s!"generated-{seed}"
    let ids ← TraceSource.programsOf pythonCmd script
      #[dir.toString, "--seed", seed, "--count", count]
    let programs ← TraceSource.mapBounded 8 ids fun id => do
      let file := dir / s!"{id}.py"
      return (id, file, ← SemDiff.cpythonTrace pythonCmd file)
    let (now, failures) ← TraceSource.judgeAll 8 #[] programs
    TraceSource.report s!"GeneratedDiffTest (seed {seed})" now ids.size failures
  | _, _ =>
    let dir : System.FilePath := ".lake" / "build" / "differential" / "generated"
    let ids ← TraceSource.programsOf pythonCmd script
      #[dir.toString, "--seed", "1", "--count", "500"]
    TraceSource.runSource "GeneratedDiffTest" pythonCmd dir (here / "generated.cpython.traces")
      (here / "generated_expected.txt") ids (← IO.getEnv "SEM_UPDATE").isSome

end StrataPython.GeneratedDiffTest
