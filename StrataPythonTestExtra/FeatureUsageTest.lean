/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPython
meta import StrataPython.FeatureUsage
meta import StrataPython.ReadPython
meta import StrataDDM.Util.IO
meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Mantle.TestUtil

/-! # Tests for the unresolved names `pymantle features` reports

Parses `feature_usage/names.py` through CPython, runs `analyzeFeatures`, and checks that its
unresolved names are exactly the program's unbound reads, each with its number of reads.
-/

namespace StrataPython.FeatureUsageTest

open StrataPython (withPython)
open StrataPython.Mantle.TestUtil (compilePython)

private meta def pyFile : System.FilePath := "StrataPythonTestExtra/feature_usage/names.py"

/-- The names `names.py` reads unbound, with their read counts. -/
private meta def expected : List (String × Nat) := [
  ("UndefinedBase", 1),
  ("UndefinedMeta", 1),
  ("attr", 2),
  ("undefined_decorator", 1),
  ("undefined_decorator_arg", 1),
  ("undefined_default", 1),
  ("undefined_in_lambda", 1),
  ("undefined_kw_default", 1),
  ("undefined_name", 1)
]

#eval withPython fun pythonCmd => IO.FS.withTempDir fun tmpDir => do
  let ionPath ← compilePython pythonCmd pyFile tmpDir
  let bytes ← StrataDDM.Util.readBinInputSource ionPath.toString
  let stmts ← match StrataPython.readPythonStrataBytes ionPath.toString bytes with
    | .ok stmts => pure stmts
    | .error msg => throw <| .userError s!"Failed to read Ion: {msg}"
  let st := StrataPython.FeatureUsage.analyzeFeatures stmts
  let actual := st.unresolvedNames.toList.mergeSort (·.1 < ·.1)
  if actual != expected then
    throw <| .userError s!"FeatureUsageTest: unresolved names\n  expected: {expected}\n  \
      actual:   {actual}"

end StrataPython.FeatureUsageTest
