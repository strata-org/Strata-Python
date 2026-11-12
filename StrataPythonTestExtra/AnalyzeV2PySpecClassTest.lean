/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import StrataPython.PySpecPipeline
meta import StrataLaurel.Implementation.Resolution
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
    expectNoCore pythonCmd tmpDir "test_pyspec_method_ok.py" #["servicelib.Storage"]

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Storage"]
    expectNoCore pythonCmd tmpDir "test_pyspec_method_violation.py" #["servicelib.Storage"]

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Storage"]
    expectNoCore pythonCmd tmpDir "test_pyspec_method_dotted.py" #["servicelib.Storage"]

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Messaging"]
    expectNoCore pythonCmd tmpDir "test_pyspec_method_positional.py" #["servicelib.Messaging"]

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Messaging"]
    expectNoCore pythonCmd tmpDir "test_pyspec_method_kwargs.py" #["servicelib.Messaging"]

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

-- A modeled class with NO methods cannot be lowered by V2 while `Any` is not gradual.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Bare"]
    expectNoCore pythonCmd tmpDir "test_methodless_class.py" #["servicelib.Bare"]

-- A model constructor called before a method cannot be lowered by V2 while `Any` is not gradual.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Ctor"]
    expectNoCore pythonCmd tmpDir "test_ctor_contract_method.py" #["servicelib.Ctor"]

-- The `@overload` stubs of `__init__` get no procedure, so the model loads, and a
-- program that does not construct the class verifies.
/-- info: obligations: 0 -/
#guard_msgs in
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Overloaded"]
    let results ← runAndVerify pythonCmd tmpDir "test_overloaded_init.py"
      #["servicelib.Overloaded"]
    IO.println s!"obligations: {results.size}"

-- A call of an overloaded method cannot be lowered by V2 while `Any` is not gradual.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Overloaded"]
    expectNoCore pythonCmd tmpDir "test_overloaded_method_call.py" #["servicelib.Overloaded"]

end StrataPython.AnalyzeV2PySpecClassTest
