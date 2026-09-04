/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import StrataPython.PySpecPipeline
meta import Strata.Languages.Laurel.Resolution
meta import Strata.Transform.ProcedureInlining
meta import StrataPython.PyFactory
meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Util.V2Pipeline
meta import StrataPython.Resolution
meta import StrataPython

namespace StrataPython.AnalyzeV2PySpecClassTest

open StrataPython.V2TestUtil

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Storage"]
    let results ← runAndVerify pythonCmd tmpDir "test_pyspec_method_ok.py" #["servicelib.Storage"]
    let bucket ← vcBySummary results "Bucket must not be empty"
    let key ← vcBySummary results "Key must not be empty"
    unless bucket.isSuccess && key.isSuccess do
      throw <| IO.userError "Expected both method preconditions to pass"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Storage"]
    let results ← runAndVerify pythonCmd tmpDir "test_pyspec_method_violation.py" #["servicelib.Storage"]
    let bucket ← vcBySummary results "Bucket must not be empty"
    let key ← vcBySummary results "Key must not be empty"
    if bucket.isSuccess || !key.isSuccess then
      throw <| IO.userError "Keyword method preconditions had unexpected outcomes"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_pyspec_method_dotted.py"
      #["servicelib.Storage"] "check_delete"
    unless caller.contains "servicelib_Storage_Storage@delete_item(" do
      throw <| IO.userError "Dotted class annotation did not bind the modeled method"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Messaging"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_pyspec_method_positional.py"
      #["servicelib.Messaging"] "check_receive"
    unless caller.contains "servicelib_Messaging_Messaging@receive(" do
      throw <| IO.userError "Positional method call did not bind"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Messaging"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_pyspec_method_kwargs.py"
      #["servicelib.Messaging"] "check_send"
    unless caller.contains "servicelib_Messaging_Messaging@send(" do
      throw <| IO.userError "Kwargs method call did not bind"

#guard checkExternalSigSplit [] [] [] [] == none
#guard checkExternalSigSplit [("a", none), ("b", none)] ["a", "b"] [] [] == none
#guard checkExternalSigSplit [("a", someDefaultArg)] [] [] ["a"]
  (kwonlyCount := 1) == none
#guard checkExternalSigSplit [("a", none), ("b", none)] [] [] ["a", "b"]
  (kwonlyCount := 5) == none
#guard checkExternalSigSplit [("a", none), ("b", someDefaultArg), ("c", none)]
  ["a"] ["b"] ["c"] (kwonlyCount := 1) == none
-- A non-constant default must keep its parameter in the optional bucket, not drop it.
#guard checkExternalSigSplit [("a", none), ("b", nonConstDefaultArg)] ["a"] ["b"] [] == none
#guard checkExternalKwargs == none

-- A modeled class with NO methods still binds: a parameter annotated with it
-- resolves to the modeled Composite, so its field access is a real read (no havoc).
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Bare"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_methodless_class.py"
      #["servicelib.Bare"] "use_it"
    unless caller.contains "m: Marker" && caller.contains "m#kind" do
      throw <| IO.userError s!"Methodless modeled class did not bind:\n{caller}"

end StrataPython.AnalyzeV2PySpecClassTest
