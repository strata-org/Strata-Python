/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.AxisSource

/-! # The axis grid against CPython

Runs every program of the axis grid (`StrataPythonTest/Dyn/axes/grid.py`: one operation with one
kind of input on one axis, e.g. `len` of an instance of a `list` subclass that overrides
`__iter__`) with CPython 3.12 and with the Python semantics, and judges each pair with
`SemDiff.judge`. The verdicts are pinned in `StrataPythonTest/Dyn/axes/grid_expected.txt`, and our
run of each `known` case in `grid_known/`. The test fails:

* on a generator bug (`AxisSource.generatorBug?`): a case whose CPython run doesn't run its
  operation, or doesn't end the way the case expects, tests nothing; in update mode also a case
  whose CPython trace doesn't change when its operation is replaced by `r = None`
  (`AxisSource.observes`);
* on any difference that is not a gap after agreeing with CPython, and on any change of verdict;
* on a change of `grid_digest.txt`. The digest stands for this property: CPython's traces under
  the hash seeds 0 to 7 were compared on exactly these programs, and were equal. The build runs
  CPython under seed 0 only. The digest check makes sure that no program changes without an
  update, and the update compares the eight traces again. An update that fails writes nothing.

`grid_summary.txt` shows the verdicts by group and axis; it is compared like the verdicts, so that
it stays current. The test needs CPython 3.12, which it finds or fails without (`SKIP_PYTHON_TESTS`
skips it, as it does every Python test). Set `SEM_UPDATE=1` to compare the eight traces of every
program and rewrite the verdicts, the known runs, the summary and the digest.
-/

namespace StrataPython.AxisGridTest

open Strata.Dyn.Exec
open Strata.Dyn.Exec.Diff (Entry Verdict)
open StrataPython.AxisSource

private meta def here : System.FilePath := "StrataPythonTest" / "Dyn" / "axes"
private meta def outDir : System.FilePath := ".lake" / "build" / "differential" / "axes"
private meta def knownDir : System.FilePath := here / "grid_known"
private meta def knownSuffix : String := ".known.trace"

/-- The verdict of the case `c` and, for a `known` case in update mode, our run to pin; or why the
test fails on it. `reasons` maps each case pinned as `known` to its reason. -/
private meta def runCase (pythonCmd : System.FilePath) (update : Bool)
    (reasons : Std.HashMap String String) (c : Case) :
    IO (Except String (Entry × Option String)) := do
  let file := outDir / s!"{c.id}.py"
  let traces ← if update then seeds.toArray.mapM (cpythonTraceSeed pythonCmd file)
    else pure #[← cpythonTraceSeed pythonCmd file 0]
  unless seedsAgree traces do
    return .error s!"{c.id}: generator bug: CPython's trace depends on the hash seed or the machine"
  let theirs := traces[0]!
  if update then
    let null ← cpythonTraceSeed pythonCmd (outDir / s!"{c.id}.null.py") 0
    unless observes c theirs null do
      return .error s!"{c.id}: generator bug: CPython's trace is the same without the operation"
  let ours ← SemDiff.runOurs file
  if let some bug := generatorBug? c theirs ours then return .error bug
  let reason := reasons.get? c.id
  let pin := knownDir / s!"{c.id}{knownSuffix}"
  let known ← match reason with
    | none => pure none
    | some r =>
      if update then pure (some ⟨r, none⟩)
      else if ← pin.pathExists then pure (some ⟨r, some (← IO.FS.readFile pin)⟩)
      else return .error s!"{c.id}: missing {pin}; run with SEM_UPDATE=1"
  match SemDiff.judge c.id ours theirs known, ours with
  | .error e, _ => return .error e
  | .ok v@(.known _), .trace t => return .ok (⟨c.id, v⟩, if update then some t else none)
  | .ok v, _ => return .ok (⟨c.id, v⟩, none)

/-- Compare `text` with the file `path`, or write it in update mode. -/
private meta def checkFile (path : System.FilePath) (text : String) (update : Bool) :
    IO (Option String) := do
  if update then
    IO.FS.writeFile path text
    return none
  let old ← if ← path.pathExists then IO.FS.readFile path else pure ""
  return if old == text then none else
    some s!"{path} differs from this run; run with SEM_UPDATE=1 after checking the change"

#eval show IO Unit from do
  if let some skip ← IO.getEnv "SKIP_PYTHON_TESTS" then
    if !skip.isEmpty then return
  unless ← SemDiff.pydynPath.pathExists do
    throw <| .userError s!"{SemDiff.pydynPath} is missing: build it with `lake build pydyn`"
  let start ← IO.monoMsNow
  let pythonCmd ← StrataPython.findPython3 (minVersion := 12) (maxVersion := 12)
  let update := (← IO.getEnv "SEM_UPDATE").isSome
  let script := here / "grid.py"
  let lines ← TraceSource.programsOf pythonCmd script #[outDir.toString]
  let cases ← IO.ofExcept (parseCases ("\n".intercalate lines.toList))
  let pinned ← TraceSource.readPinned (here / "grid_expected.txt")
  let reasons : Std.HashMap String String := pinned.foldl (init := {}) fun m e =>
    match e.verdict with | .known r => m.insert e.path r | _ => m
  let mut failures : Array String := #[]
  let digest := String.intercalate "" (← TraceSource.programsOf pythonCmd script
    #["--digest", outDir.toString]).toList ++ "\n"
  IO.FS.createDirAll knownDir
  let results ← TraceSource.mapBounded 8 cases (runCase pythonCmd update reasons)
  let mut now : Array Entry := #[]
  let mut pins : Array (String × String) := #[]
  for r in results do
    match r with
    | .ok (e, pin) =>
      now := now.push e
      if let some t := pin then pins := pins.push (e.path, t)
    | .error msg => failures := failures.push msg
  unless update do
    for f in ← knownDir.readDir do
      let n := (f.fileName.dropEnd knownSuffix.length).toString
      unless reasons.contains n do
        failures := failures.push s!"{f.path}: pinned run for no known case"
  -- An update writes its files only when every case passed, so that the digest's property holds.
  if failures.isEmpty then
    if let some f ← checkFile (here / "grid_digest.txt") digest update then
      failures := failures.push f
    for ch in ← Diff.checkOrUpdate (here / "grid_expected.txt") now update do
      failures := failures.push ch.render
    if let some f ← checkFile (here / "grid_summary.txt") (summary cases now) update then
      failures := failures.push f
    if update then
      for f in ← knownDir.readDir do IO.FS.removeFile f.path
      for (id, t) in pins do IO.FS.writeFile (knownDir / s!"{id}{knownSuffix}") t
  -- The wall time, so that a build log shows what the grid costs.
  let secs := ((← IO.monoMsNow) - start) / 1000
  TraceSource.report s!"AxisGridTest ({secs} s)" now cases.size failures

end StrataPython.AxisGridTest
