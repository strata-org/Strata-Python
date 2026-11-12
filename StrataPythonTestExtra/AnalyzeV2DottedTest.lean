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
meta import StrataPython

namespace StrataPython.AnalyzeV2DottedTest

open StrataPython.V2TestUtil

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_dotted_modalias.py" #["servicelib.Contract"]

end StrataPython.AnalyzeV2DottedTest
