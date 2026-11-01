/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.TraceSource
meta import StrataPythonTest.Util.Python

/-! # PyLate programs against CPython

Runs PyLate's scenarios as programs with the Python semantics, and compares each trace with
CPython 3.12's. The programs come from `StrataPythonTest/Dyn/differential/pylate_programs.py`:
the callable-rule scenarios (`Pylate/harness/data/callable_rule_scenarios.json` and
`callable_rule_fuzz.json`), the rule-validity cases (`rule_validity_cases.json`) and the
dispatch-order scenarios of `Pylate/harness/probes/cpython_binop_probe.py`. CPython's traces are
kept in `StrataPythonTest/Dyn/differential/pylate.cpython.traces`, and the verdicts are pinned in
`StrataPythonTest/Dyn/differential/pylate_expected.txt`. Set `SEM_UPDATE=1` to rewrite both
files (that needs CPython 3.12).
-/

namespace StrataPython.PylateDiffTest

private meta def here : System.FilePath := "StrataPythonTest" / "Dyn" / "differential"

#eval withPython fun pythonCmd => do
  let dir : System.FilePath := ".lake" / "build" / "differential" / "pylate"
  let ids ← TraceSource.programsOf pythonCmd (here / "pylate_programs.py") #[dir.toString]
  TraceSource.runSource "PylateDiffTest" pythonCmd dir (here / "pylate.cpython.traces")
    (here / "pylate_expected.txt") ids (← IO.getEnv "SEM_UPDATE").isSome

end StrataPython.PylateDiffTest
