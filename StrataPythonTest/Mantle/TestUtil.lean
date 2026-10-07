/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import StrataPython.PythonDialect
public meta import StrataDDM.Ion

/-! # Helpers for the Python-on-Mantle golden runners

`MantleTranslateTest` and `PyScopeTest` in `StrataPythonTestExtra` share these:

* `compilePython`: parse a `.py` file to a Strata Ion file through CPython;
* `firstDiff`: the first line where an output and its golden differ.
-/

namespace StrataPython.Mantle.TestUtil

public meta section

/-- Parse `pyFile` to a Strata Ion file in `outDir`. -/
def compilePython (pythonCmd pyFile outDir : System.FilePath) : IO System.FilePath := do
  let some stem := pyFile.fileStem | throw <| .userError s!"No stem for {pyFile}"
  let ionPath := outDir / s!"{stem}.python.st.ion"
  let dialectFile := outDir / s!"{stem}.dialect.st.ion"
  IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
  let out ← IO.Process.output {
    cmd := toString pythonCmd
    args := #["-m", "strata_python.gen", "py_to_strata", "--dialect", dialectFile.toString,
              pyFile.toString, ionPath.toString] }
  if out.exitCode ≠ 0 then
    throw <| .userError s!"py_to_strata failed for {pyFile} (exit {out.exitCode}): {out.stderr}"
  return ionPath

/-- The first line where `actual` and `expected` differ, or `none` if they agree. -/
def firstDiff (actual expected : String) : Option String := Id.run do
  let a := actual.trimAscii.toString.splitOn "\n"
  let e := expected.trimAscii.toString.splitOn "\n"
  for i in [:max a.length e.length] do
    let al := a[i]?.getD "<EOF>"
    let el := e[i]?.getD "<EOF>"
    if al != el then
      return some s!"line {i + 1}:\n    expected: {el}\n    actual:   {al}"
  return none

end

end StrataPython.Mantle.TestUtil
