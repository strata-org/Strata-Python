/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Lean.Data.Json
meta import StrataPythonTest.Util.TraceSource

/-! # The CPython regression-suite oracle against the Python semantics

The second backend of the oracle (`StrataPythonTest/cpython_oracle/`, whose first backend is
`pyInterpret`, `CpythonOracleTest.lean`). `runner_dyn.py` selects and generates the methods as
the first backend does, into its own build directory, `cpython_oracle/build_dyn/`, and gives
CPython 3.12's trace of each generated program. This test runs the Python semantics
(`pydyn run`) on each program and pins its verdict in `cpython_oracle/verdicts_dyn.txt`
(`Strata.Dyn.Exec.Diff`).

A method that depends on the machine is excluded, with the first backend's two buckets:
`oracleNotClean` (the method doesn't run cleanly under CPython) and `loweringBroken` (the
generated program fails under CPython where the method doesn't). `cpython_oracle/excluded_dyn.txt`
keeps the methods excluded when the verdicts were written, one `<stem> <bucket>` per line. When
the test checks, it leaves out a method that the list or this machine excludes, and ignores its
pinned verdict, so a method that is machine-dependent here doesn't look new on a machine where it
runs. An update writes this machine's exclusions to the list.

The test needs CPython 3.12 (`PYTHON`) and its sources (the `CPython312Runtime` build tool), and
reports a skip without them, as the first backend does.

- `CPYTHON_ORACLE=0` or `CPYTHON_ORACLE_DYN=0`: skip it.
- `CPYTHON_ORACLE_WORKERS`: the number of programs that run at once, default 4.
- `SEM_UPDATE=1`: rewrite the verdicts and the excluded list. Record with the CPython that the
  build uses (`PYTHON` as `build-tools/bin/custom-build` sets it): the exclusions depend on the
  CPython build, e.g. on whether it has `_testcapi`.
-/

namespace StrataPython.CpythonOracleDynTest

open Lean (Json)
open Strata.Dyn.Exec
open Strata.Dyn.Exec.Diff (Entry)

private meta def here : System.FilePath := "StrataPythonTest" / "cpython_oracle"

private meta def verdictFile : System.FilePath := here / "verdicts_dyn.txt"

private meta def excludedFile : System.FilePath := here / "excluded_dyn.txt"

/-- The stems and buckets of an excluded list. -/
private meta def parseExcluded (text : String) : Array (String × String) :=
  ((text.splitOn "\n").filterMap fun l =>
    match l.splitOn " " with
    | [stem, bucket] => some (stem, bucket)
    | _ => none).toArray

/-- One method's result in `dyn.json`. -/
private inductive Method where
  | traced (stem program trace : String)
  | excluded (stem bucket : String)
  | error (stem msg : String)

private meta def readMethods (text : String) : Except String (Array Method) := do
  let j ← Json.parse text
  let rs ← (← j.getObjVal? "results").getArr?
  rs.mapM fun r => do
    let stem ← (← r.getObjVal? "stem").getStr?
    if let .ok b := r.getObjValAs? String "excluded" then return .excluded stem b
    if let .ok m := r.getObjValAs? String "error" then return .error stem m
    let traces ← r.getObjValAs? (Array String) "traces"
    let (some t0, some t1) := (traces[0]?, traces[1]?)
      | throw s!"{stem}: dyn.json must give two traces"
    return .traced stem (← r.getObjValAs? String "program") (SemDiff.joinRuns t0 t1)

#eval show IO Unit from do
  if (← IO.getEnv "CPYTHON_ORACLE") == some "0" || (← IO.getEnv "CPYTHON_ORACLE_DYN") == some "0"
  then
    IO.println "CpythonOracleDynTest: skipped (CPYTHON_ORACLE=0)"
    return
  unless ← SemDiff.pydynPath.pathExists do
    throw <| .userError s!"{SemDiff.pydynPath} is missing: build it with `lake build pydyn`"
  let update := (← IO.getEnv "SEM_UPDATE").isSome
  let workers := ((← IO.getEnv "CPYTHON_ORACLE_WORKERS").bind String.toNat?).getD 4
  let build := here / "build_dyn"
  let python := (← IO.getEnv "PYTHON").getD "python3"
  let r ← IO.Process.output {
    cmd := python, args := #[(here / "runner_dyn.py").toString, "--build", build.toString,
      "--workers", toString workers] }
  if r.exitCode == 3 then
    IO.println s!"CpythonOracleDynTest: skipped ({r.stderr.trimAscii})"
    return
  unless r.exitCode == 0 do
    throw <| .userError s!"runner_dyn.py failed:\n{r.stdout}{r.stderr}"
  let methods ← IO.ofExcept <| readMethods (← IO.FS.readFile (build / "dyn.json"))
  let listed ← if ← excludedFile.pathExists then
      pure (parseExcluded (← IO.FS.readFile excludedFile))
    else pure #[]
  let excludedHere := methods.filterMap fun | .excluded s b => some (s, b) | _ => none
  let skip (stem : String) := listed.any (·.1 == stem) ||
    excludedHere.any (·.1 == stem)
  let mut failures : Array String := #[]
  for m in methods do
    if let .error s msg := m then failures := failures.push s!"{s}: {msg}"
  let pinned ← TraceSource.readPinned verdictFile
  let traced := methods.filterMap fun
    | .traced s p t => if update || !skip s then some (s, (p : System.FilePath), t) else none
    | _ => none
  let (now, judged) ← TraceSource.judgeAll workers pinned traced
  failures := failures ++ judged
  if update then
    if failures.isEmpty then
      IO.FS.writeFile verdictFile (Diff.render now)
      IO.FS.writeFile excludedFile
        (String.join (excludedHere.toList.map fun (s, b) => s!"{s} {b}\n"))
  else
    let pinnedHere := pinned.filter (!skip ·.path)
    for c in Diff.changes pinnedHere now do
      failures := failures.push c.render
  TraceSource.report "CpythonOracleDynTest" now methods.size failures
    s!" ({excludedHere.size} excluded here)"

end StrataPython.CpythonOracleDynTest
