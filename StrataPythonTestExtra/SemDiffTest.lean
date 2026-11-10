/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDyn.Exec.Diff
meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Util.SemDiff

/-! # The Python semantics against CPython

Runs every program of two suites with the Python semantics and compares its trace with CPython
3.12's (`StrataPythonTest.Util.SemDiff`): the corpus `StrataPythonTest/Dyn/dyn_tests/`, whose
verdicts are pinned in `StrataPythonTest/Dyn/sem_expected.txt`, and the test programs
`StrataPythonTest/tests/`, whose verdicts are pinned in `StrataPythonTest/Dyn/sem_tests_expected.txt`
(`Strata.Dyn.Exec.Diff`).  The test fails on any change of verdict:

* `agree`: the two traces are equal;
* `gap`: the run stops with a gap, after agreeing with CPython up to it, or the translator does
  not support the program (`the translator does not support <constructs>`);
* `known`: a documented difference; the reason stays as pinned, and the run's own trace stays as
  its golden `NAME.known.trace` pins it;
* `syntax`: the translator reports a syntax error, and CPython does not compile the program.

A difference that is none of these fails, and so does a run out of fuel, except for a program
whose CPython run doesn't end within `SemDiff.cpythonSeconds`: its run must not end with a result
(`SemDiff.judge`).  CPython's traces are
goldens, `NAME.cpython.trace` beside the corpus's `NAME.py` and in
`StrataPythonTest/Dyn/test_traces/` for the test programs, so the check runs no CPython program;
it still needs Python with `strata_python`, which parses the programs.  Set `SEM_UPDATE=1` to
rewrite the goldens and the verdict files.
-/

namespace StrataPython.SemDiffTest

open Strata.Dyn.Exec
open Strata.Dyn.Exec.Diff (Entry Verdict)
open StrataPython (withPython)

/-- A set of programs: where they are, where their goldens are, their verdict file, and whether
the golden of a program that the translator rejects keeps CPython's trace (`false`: a fixed
line, `rejectedTrace`, since the trace is never compared and may hold the machine's paths). -/
private structure Suite where
  name : String
  programs : System.FilePath
  goldens : System.FilePath
  verdicts : System.FilePath
  keepRejected : Bool

/-- The corpus, with its goldens beside its programs, and the test programs. -/
private meta def suites : List Suite := [
  ⟨"corpus", "StrataPythonTest" / "Dyn" / "dyn_tests", "StrataPythonTest" / "Dyn" / "dyn_tests",
    "StrataPythonTest" / "Dyn" / "sem_expected.txt", true⟩,
  ⟨"tests", "StrataPythonTest" / "tests", "StrataPythonTest" / "Dyn" / "test_traces",
    "StrataPythonTest" / "Dyn" / "sem_tests_expected.txt", false⟩]

/-- The golden of a program that the translator rejects, in a suite that doesn't keep its trace. -/
private meta def rejectedTrace : String := "--- not kept: the translator rejects the program\n"

/-- The suffix of a CPython golden. -/
private meta def goldenSuffix : String := ".cpython.trace"

/-- The suffix of the golden of the run's own trace, for a program with a documented difference. -/
private meta def knownSuffix : String := ".known.trace"

/-- The verdict of one program, or the reason the test fails on it. -/
private meta def runCase (suite : Suite) (pythonCmd : System.FilePath) (update : Bool)
    (pinned : Array Entry) (name : String) : IO (Except String Entry) := do
  let pyFile := suite.programs / s!"{name}.py"
  let golden := suite.goldens / s!"{name}{goldenSuffix}"
  let theirs ← if update then SemDiff.cpythonTrace pythonCmd pyFile
    else if ← golden.pathExists then IO.FS.readFile golden
    else return .error s!"{name}: missing {golden}; run with SEM_UPDATE=1"
  let reason := pinned.findSome? fun e =>
    if e.path == name then match e.verdict with | .known r => some r | _ => none else none
  -- A documented difference holds only for the run's own trace, which its golden pins.
  let pin := suite.goldens / s!"{name}{knownSuffix}"
  let known ← match reason with
    | none => pure none
    | some r =>
      if update then pure (some ⟨r, none⟩)
      else if ← pin.pathExists then pure (some ⟨r, some (← IO.FS.readFile pin)⟩)
      else return .error s!"{name}: missing {pin}; run with SEM_UPDATE=1"
  let ours ← SemDiff.runOurs pyFile
    (fuel := if theirs == SemDiff.endlessTrace then some SemDiff.endlessFuel else none)
  if update then
    let kept := suite.keepRejected || !(ours matches .unsupported _) || theirs == SemDiff.syntaxTrace
    IO.FS.writeFile golden (if kept then theirs else rejectedTrace)
  match SemDiff.judge name ours theirs known, ours with
  | .error e, _ => return .error e
  | .ok v@(.known _), .trace t =>
    if update then IO.FS.writeFile pin t
    return .ok ⟨name, v⟩
  | .ok v, _ => return .ok ⟨name, v⟩

/-- Runs the suite `suite`, and gives its failures. -/
private meta def runSuite (pythonCmd : System.FilePath) (update : Bool) (suite : Suite) :
    IO (Array String) := do
  let verdictFile := suite.verdicts
  let pinned ← if ← verdictFile.pathExists then
      match Diff.parse (← IO.FS.readFile verdictFile) with
      | .ok es => pure es
      | .error e => throw <| .userError s!"{verdictFile}: {e}"
    else pure #[]
  let mut names : Array String := #[]
  let mut failures : Array String := #[]
  for f in ← suite.programs.readDir do
    if f.path.extension == some "py" then names := names.push (f.path.fileStem.getD "")
  names := names.qsort (· < ·)
  IO.FS.createDirAll suite.goldens
  -- Every golden belongs to a program, and every pinned trace to a program with a documented
  -- difference.
  let knownNames := pinned.filterMap fun e =>
    match e.verdict with | .known _ => some e.path | _ => none
  for f in ← suite.goldens.readDir do
    if f.fileName.endsWith goldenSuffix then
      unless names.contains (f.fileName.dropEnd goldenSuffix.length).toString do
        if update then IO.FS.removeFile f.path
        else failures := failures.push s!"{f.path}: golden for no program"
    if f.fileName.endsWith knownSuffix && !update then
      unless knownNames.contains (f.fileName.dropEnd knownSuffix.length).toString do
        failures := failures.push s!"{f.path}: pinned trace for no documented difference"
  let tasks ← names.mapM fun n => IO.asTask (runCase suite pythonCmd update pinned n)
  let mut now : Array Entry := #[]
  for (n, t) in names.zip tasks do
    match ← IO.wait t with
    | .ok (.ok e) => now := now.push e
    | .ok (.error msg) => failures := failures.push msg
    | .error err => failures := failures.push s!"{n}: {err}"
  -- An update keeps the pinned traces of the programs whose difference is still documented.
  if update then
    for f in ← suite.goldens.readDir do
      if f.fileName.endsWith knownSuffix then
        let n := (f.fileName.dropEnd knownSuffix.length).toString
        unless now.any fun e => e.path == n && e.verdict matches .known _ do IO.FS.removeFile f.path
  if failures.isEmpty then
    for c in ← Diff.checkOrUpdate verdictFile now update do
      failures := failures.push c.render
  let count v := (now.filter fun e => v e.verdict).size
  IO.println s!"SemDiffTest ({suite.name}): {count (· == .agree)} agree, \
    {count (fun | .gap _ => true | _ => false)} gap, {count (fun | .known _ => true | _ => false)} \
    known, {count (· == .syntax)} syntax, of {names.size}"
  return failures

#eval withPython fun pythonCmd => do
  let update := (← IO.getEnv "SEM_UPDATE").isSome
  unless ← SemDiff.pydynPath.pathExists do
    throw <| .userError s!"{SemDiff.pydynPath} is missing: build it with `lake build pydyn`"
  let mut failures : Array String := #[]
  for suite in suites do
    failures := failures ++ (← runSuite pythonCmd update suite)
  if !failures.isEmpty then
    for f in failures do IO.println f
    throw <| .userError s!"SemDiffTest: {failures.size} failure(s)"

end StrataPython.SemDiffTest
