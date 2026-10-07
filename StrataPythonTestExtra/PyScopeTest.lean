/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPython
meta import StrataPython.Mantle.Scope
meta import StrataPython.ReadPython
meta import StrataDDM.Util.IO
meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Mantle.TestUtil

/-! # Tests for the Python scope pass

For each `NAME.py` in `StrataPythonTest/Mantle/mantle_tests/`, parses it through CPython, runs
`PyScope.analyze`, and checks two files beside it:

* `NAME.expected.scope`: `Table.format`, a golden.  Set `PYSCOPE_UPDATE=1` to rewrite it.
* `NAME.symtable`: what CPython's `symtable` module records, written by
  `StrataPythonTest/Mantle/scope_symtable.py`.  `Table.symtableFormat` must match it exactly.
  A file containing `skip` is a program with `type` statements or type parameters.

Every program must have both files, and each of them must belong to a program.
-/

namespace StrataPython.PyScopeTest

open StrataPython.Mantle.PyScope (analyze)
open StrataPython (withPython)
open StrataPython.Mantle.TestUtil (compilePython firstDiff)

private meta def testDir : System.FilePath := "StrataPythonTest/Mantle/mantle_tests"

/-- The suffixes of the files `runCase` checks beside `NAME.py`. -/
private meta def suffixes : List String := [".expected.scope", ".symtable"]

/-- `dir/NAME.py`'s companion `dir/NAME{suffix}`. -/
private meta def companion (pyFile : System.FilePath) (suffix : String) : System.FilePath :=
  pyFile.withFileName s!"{pyFile.fileStem.getD ""}{suffix}"

/-- Run one case; return its failures. -/
private meta def runCase (pythonCmd tmpDir pyFile : System.FilePath) (update : Bool) :
    IO (Array String) := do
  let ionPath ← compilePython pythonCmd pyFile tmpDir
  let bytes ← StrataDDM.Util.readBinInputSource ionPath.toString
  let stmts ← match StrataPython.readPythonStrataBytes ionPath.toString bytes with
    | .ok stmts => pure stmts
    | .error msg => throw <| .userError s!"Failed to read Ion: {msg}"
  let fileMap := Lean.FileMap.ofString (← IO.FS.readFile pyFile)
  let table := analyze stmts
  let mut failures := #[]
  let dump := table.format fileMap
  let expectedFile := companion pyFile ".expected.scope"
  if update then
    IO.FS.writeFile expectedFile dump
  else if !(← expectedFile.pathExists) then
    failures := failures.push s!"{pyFile}: missing {expectedFile}"
  else if let some d := firstDiff dump (← IO.FS.readFile expectedFile) then
    failures := failures.push s!"{pyFile}: Table.format differs from {expectedFile} at {d}"
  let symtableFile := companion pyFile ".symtable"
  if !(← symtableFile.pathExists) then
    failures := failures.push s!"{pyFile}: missing {symtableFile}"
  else
    let cpython ← IO.FS.readFile symtableFile
    if cpython.trimAscii.toString != "skip" then
      if let some d := firstDiff (table.symtableFormat fileMap) cpython then
        failures := failures.push s!"{pyFile}: differs from CPython's symtable at {d}"
  return failures

#eval withPython fun pythonCmd => do
  let update := (← IO.getEnv "PYSCOPE_UPDATE").isSome
  let entries ← testDir.readDir
  let files := entries.filter (·.path.extension == some "py")
    |>.map (·.path) |>.qsort (·.toString < ·.toString)
  if files.isEmpty then throw <| IO.userError "PyScopeTest: no tests found"
  -- Every golden and symbol table belongs to a program.
  let stems := files.filterMap (·.fileStem)
  let mut failures : Array String := #[]
  for f in entries do
    if let some sfx := suffixes.find? (f.fileName.endsWith ·) then
      unless stems.contains (f.fileName.dropEnd sfx.length).toString do
        failures := failures.push s!"{f.path}: belongs to no program"
  IO.FS.withTempDir fun tmpDir => do
    let tasks ← files.mapM fun f => IO.asTask (runCase pythonCmd tmpDir f update)
    let mut failures := failures
    for t in tasks do
      match ← IO.wait t with
      | .ok fs => failures := failures ++ fs
      | .error e => failures := failures.push s!"task error: {e}"
    IO.println s!"PyScopeTest: {files.size} programs"
    if !failures.isEmpty then
      for f in failures do IO.println f
      throw <| IO.userError s!"PyScopeTest: {failures.size} failure(s) in {files.size} cases"

end StrataPython.PyScopeTest
