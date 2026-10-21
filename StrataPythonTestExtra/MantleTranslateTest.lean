/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPython
meta import StrataPython.Mantle.Translate
meta import StrataMantle.DDM
meta import StrataMantle.DDMRead
meta import StrataPython.Mantle.Env
meta import StrataMantle.Env.WF
meta import StrataPython.ReadPython
meta import StrataDDM.Util.IO
meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Mantle.TestUtil
meta import StrataMantleTest.DomRef

/-! # Python-to-Mantle translator tests

Runs `PyTranslate.translate` over every test listed in `StrataPythonTest/Mantle/mantle_tests.txt`
and checks each against whether it is supported.

The list has one line per test:

```
t03_if_else | yes |
n05_lambda | yes | lambda
```

The columns are the `.py` path under `StrataPythonTest/Mantle/mantle_tests/` without its
extension, its status (`yes` if supported, `no` if not yet), and the diagnostics it is expected
to give: a rejected construct's name, the message without " is not supported", or a scope
error's message.

A test *translates* when its diagnostics are exactly the expected ones.  Every module must be
well formed (`Module.Raw.WF`), have no name with a `.` inside a segment, and read back from its
full printed form with the same values, defined in the same order with the same names.  A
supported test must translate, and its diagnostics and printed module must equal
`NAME.expected.mantle` beside `NAME.py`.  A test not yet supported must not translate; one that
does fails, and must be marked `yes`.

The tree the check computes for every body must give every block the parent an independent
computation gives: the iterative set-intersection algorithm (`DomRef.expectedIdoms`, in
`StrataMantleTest/DomRef.lean`), where the check uses Cooper, Harvey and Kennedy's
(`Body.domTree?`).  The builder drops every block the entry does not reach, so a block that
remains unreached fails the test.

Every `.py` file in `mantle_tests/` must be listed, and every `.expected.mantle` file there must
belong to a supported test.  Set `MANTLE_UPDATE=1` to rewrite the goldens.
-/

namespace StrataPython.MantleTranslateTest

open StrataPython.Mantle.PyTranslate (translate formatDiagnostic)
open StrataPython (withPython)
open StrataPython.Mantle.TestUtil (compilePython firstDiff dottedNames)

private meta def root : System.FilePath := "StrataPythonTest"

private meta def listFile : System.FilePath := root / "Mantle" / "mantle_tests.txt"

/-- The directory holding the tests and their goldens. -/
private meta def testDir : System.FilePath := root / "Mantle" / "mantle_tests"

/-- The suffix of a translator golden. -/
private meta def goldenSuffix : String := ".expected.mantle"

/-- One line of the list. -/
private structure Entry where
  path : String
  supported : Bool
  rejects : List String

/-- The test's name: the file stem. -/
private meta def Entry.name (e : Entry) : String :=
  (System.FilePath.mk e.path).fileName.getD e.path

/-- Parse the list. -/
private meta def readList : IO (Array Entry) := do
  let mut entries := #[]
  for line in (← IO.FS.readFile listFile).splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    let cols := (line.splitOn "|").map (·.trimAscii.toString)
    let [path, status, rejects] := cols
      | throw <| IO.userError s!"{listFile}: malformed line: {line}"
    let supported ← match status with
      | "yes" => pure true
      | "no" => pure false
      | _ => throw <| IO.userError s!"{listFile}: bad status: {line}"
    let rejects := (rejects.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
    entries := entries.push { path, supported, rejects }
  return entries

/-- What happened to one test. -/
private inductive Outcome where
  | supported
  | rejected
  | failed (msg : String)

/-- Run one test. -/
private meta def runCase (pythonCmd tmpDir : System.FilePath) (update : Bool)
    (e : Entry) : IO Outcome := do
  let pyFile := testDir / s!"{e.path}.py"
  let ionPath ← compilePython pythonCmd pyFile tmpDir
  let bytes ← StrataDDM.Util.readBinInputSource ionPath.toString
  let stmts ← match StrataPython.readPythonStrataBytes ionPath.toString bytes with
    | .ok stmts => pure stmts
    | .error msg => throw <| .userError s!"Failed to read Ion: {msg}"
  let fileMap := Lean.FileMap.ofString (← IO.FS.readFile pyFile)
  let r := translate e.name stmts
  let m := r.module
  -- An internal error, such as a function that is not well formed, fails any case.
  let internal := r.diagnostics.filter (·.kind == .internal)
  unless internal.isEmpty do
    return .failed s!"{e.path}: internal errors: \
      {"; ".intercalate (internal.map (·.message)).toList}"
  for f in m.raw.funcs do
    let bad := Strata.Mantle.DomRef.idomMismatches f.blocks
    unless bad.isEmpty do
      return .failed s!"{e.path}: {Strata.Mantle.ToDDM.nameText f.name}: computed dominators \
        differ: {bad}"
  let rejected := r.diagnostics.toList.map fun d =>
    ((d.message.dropSuffix? " is not supported").map (·.toString)).getD d.message
  let expected := e.rejects
  let translates := rejected.all expected.contains && expected.all rejected.contains
  if !e.supported then
    if translates then
      return .failed s!"{e.path}: translates, but is marked `no`; mark it `yes` and run \
        with MANTLE_UPDATE=1"
    return .rejected
  if !translates then
    return .failed s!"{e.path}: rejects [{", ".intercalate rejected}], expected \
      [{", ".intercalate expected}]"
  let dump := String.join (r.diagnostics.toList.map (formatDiagnostic (some fileMap) · ++ "\n"))
    ++ toString m ++ "\n"
  unless (dottedNames m.raw).isEmpty do
    return .failed s!"{e.path}: a name has a `.` inside a segment: \
      {(dottedNames m.raw).map Strata.Mantle.ToDDM.nameText}"
  -- Reading the full form back gives the same functions: the same values, defined in the same
  -- order with the same names.  The ids may differ: the builder drops the blocks the entry does
  -- not reach, which leaves their values' ids unused, and the reader numbers what it reads.
  let full := m.format .full
  match ← Strata.Mantle.Module.read StrataPython.Mantle.Py.env full e.path with
  | .error err => return .failed s!"{e.path}: the full form does not read back:\n{err}"
  | .ok m₁ =>
    let same := m₁.raw.funcs.size == m.raw.funcs.size && (m₁.raw.funcs.zip m.raw.funcs).all
      fun (f, g) => f.defs.map (f.names[·.id.id]?) == g.defs.map (g.names[·.id.id]?)
    unless same && m₁.format .full == full do
      return .failed s!"{e.path}: the full form reads back with other values or names"
  let golden := testDir / s!"{e.path}{goldenSuffix}"
  if update then
    IO.FS.writeFile golden dump
  else if !(← golden.pathExists) then
    return .failed s!"{e.path}: missing {golden}"
  else if let some d := firstDiff dump (← IO.FS.readFile golden) then
    return .failed s!"{e.path}: differs from {golden} at {d}"
  return .supported

#eval withPython fun pythonCmd => do
  let update := (← IO.getEnv "MANTLE_UPDATE").isSome
  let entries ← readList
  let mut failures : Array String := #[]
  -- Every test file is listed, and every golden belongs to a supported test.
  let listed := entries.map (·.path)
  let supported := (entries.filter (·.supported)).map (·.path)
  for f in ← testDir.readDir do
    if f.path.extension == some "py" then
      unless listed.contains (f.path.fileStem.getD "") do
        failures := failures.push s!"{f.path}: not listed"
    else if f.fileName.endsWith goldenSuffix then
      unless supported.contains (f.fileName.dropEnd goldenSuffix.length).toString do
        if update then IO.FS.removeFile f.path
        else failures := failures.push s!"{f.path}: golden for no supported test"
  let results ← IO.FS.withTempDir fun tmpDir => do
    let tasks ← entries.mapM fun e =>
      IO.asTask (runCase pythonCmd tmpDir update e)
    let mut results : Array (Entry × Outcome) := #[]
    for (e, t) in entries.zip tasks do
      match ← IO.wait t with
      | .ok o => results := results.push (e, o)
      | .error err => results := results.push (e, .failed s!"{e.path}: {err}")
    return results
  for (_, o) in results do
    if let .failed m := o then failures := failures.push m
  let isSupported : Outcome → Bool := fun | .supported => true | _ => false
  let count := (results.filter (isSupported ·.2)).size
  IO.println s!"MantleTranslateTest: {count}/{results.size} supported"
  if !failures.isEmpty then
    for f in failures do IO.println f
    throw <| IO.userError s!"MantleTranslateTest: {failures.size} failure(s)"

end StrataPython.MantleTranslateTest
