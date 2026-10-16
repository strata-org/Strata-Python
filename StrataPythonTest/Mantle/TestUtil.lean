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
  have;
* `deadBlocks`: the blocks of a function that control cannot reach.
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
def dottedNames {env : Env Unit} [base ⊑ env] {α : Type} (m : Module.Raw env α) : Array Name :=
  m.funcs.flatMap fun f =>
    (#[f.name] ++ (f.allBlocks.map (·.label.name)).toArray ++ f.names).filter hasDottedSegment

/-- The labels a block may transfer to: its instructions' successors and its terminator's. -/
def blockTargets {env : Env Unit} {α : Type} (b : Block env α) : Array Label :=
  let succs := b.instrs.flatMap fun
    | .apply _ _ _ _ _ ks _ => ks
    | .const .. => #[]
  let .apply _ _ _ _ ks _ := b.term
  (succs ++ ks).map (·.target)

/-- The labels of the blocks of `f`, outside regions, that control cannot reach: neither from
the entry nor from a handler that no operation names, which is a block taking just one value
of type `value` (§10 of `docs/PythonToMantle.md`).  A dead block of that shape that is not a
handler counts as a root too, so it is not reported. -/
def deadBlocks {env : Env Unit} {α : Type} (value : TypeExpr env) (f : Func env α) :
    Array Label := Id.run do
  let named := f.blocks.flatMap blockTargets
  let roots := f.blocks.toList.zipIdx.filterMap fun (b, i) =>
    if i == 0 || (!named.contains b.label && (b.params.map (·.type)) == #[value]) then
      some b.label else none
  let mut seen : Std.HashSet Label := {}
  let mut todo := roots
  while true do
    match todo with
    | [] => break
    | l :: rest =>
      todo := rest
      if seen.contains l then continue
      seen := seen.insert l
      if let some b := f.blocks.find? (·.label == l) then todo := (blockTargets b).toList ++ todo
  return (f.blocks.filter (!seen.contains ·.label)).map (·.label)

end

end StrataPython.Mantle.TestUtil
