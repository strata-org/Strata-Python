/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.PySpecPipeline
meta import all StrataPython.PythonRuntimeLaurelPart

meta section

namespace StrataPython.BodilessPreludeFilterTest

open StrataPython (bodilessTypeNamesFor pythonRuntimeLaurelPart)

private def candidates : List String :=
  ["Error", "Composite", "Any", "ListAny", "OperationModel", "OptionInt", "DictStrAny"]

/-! The prelude type names (`Error`, `Any`, `ListAny`, `OptionInt`, `DictStrAny`) are dropped;
    the non-prelude names (`Composite`, `OperationModel`) survive in their original order.
    Importing `Error` etc. therefore no longer emits a bodiless alias that would duplicate the
    prelude's `datatype Error` and abort the resolver. The surviving list being exactly these two
    (rather than empty) also guards against a degenerate exclusion set that would drop everything. -/
#guard bodilessTypeNamesFor candidates pythonRuntimeLaurelPart == ["Composite", "OperationModel"]

end StrataPython.BodilessPreludeFilterTest
end
