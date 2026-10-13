/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import StrataPython.PythonDialect
public meta import StrataDDM.Ion
public meta import StrataMantle.WF
meta import StrataMantle.Env.WF

/-! # Helpers for the Python-on-Mantle golden runners

`MantleTranslateTest` and `PyScopeTest` in `StrataPythonTestExtra` share these:

* `compilePython`: parse a `.py` file to a Strata Ion file through CPython;
* `firstDiff`: the first line where an output and its golden differ;
* `dottedNames`: the names of a module with a `.` inside a string segment, which no name may
  have.  A stopgap until segments are a subtype that rules it out.
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

open Strata.Mantle

/-- Whether a string segment of `n` contains `.`. -/
def hasDottedSegment : Name → Bool
  | .base => false
  | .num p _ => hasDottedSegment p
  | .str p s => s.contains '.' || hasDottedSegment p

/-- The names of `m`, of functions, labels and values, with a `.` inside a string segment. -/
def dottedNames {env : Env Unit} [base ⊑ env] {α : Type} (m : Module env α) : Array Name :=
  m.funcs.flatMap fun f =>
    (#[f.name] ++ (f.allBlocks.map (·.label.name)).toArray ++ f.names).filter hasDottedSegment

end

end StrataPython.Mantle.TestUtil
