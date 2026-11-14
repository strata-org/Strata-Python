/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.AxisSource

/-! # Fuzz programs against CPython

Runs the random programs of `StrataPythonTest/Dyn/axes/fuzz.py` (classes with special methods of
each behaviour and descriptor kind, values, and operations on them, each step in its own `try`)
with CPython 3.12 and with the Python semantics, and judges each pair.

* **Build seed** (the default): the 200 programs of seed 1, against the verdicts pinned in
  `StrataPythonTest/Dyn/axes/fuzz_expected.txt`, our runs of the `known` programs and the programs
  themselves in `fuzz_known/` (a pin holds for one program, not for its id), and `fuzz_digest.txt` (the digest stands for this property: CPython's traces under the hash
  seeds 0 to 7 were compared on exactly these programs). CPython runs under seed 0, except for
  the programs of the seed bucket (§ below). It fails on a generator bug
  (`AxisSource.fuzzBug?`), on any difference, on a change of verdict, and if no run of the seed
  bucket reaches its seed step. `SEM_UPDATE=1` runs CPython under all eight seeds and rewrites the files; an update that
  fails writes nothing.
* **Live**: `FUZZ_SEED=S FUZZ_COUNT=N lake env lean StrataPythonTestExtra/AxisFuzzTest.lean` runs
  the `N` programs of seed `S` with CPython under all eight seeds, pins nothing, and fails on any
  difference or generator bug. It prints the counts and the time.

A program of the seed bucket prints, as its last step, the order of a set of strings, which
depends on the hash seed: its verdict is `AxisSource.judgeSeedDependent` (our run must gap, and
agree with every one of CPython's eight traces up to the gap). Any other program whose eight
traces differ is a generator bug. The test also checks that program `i` of a seed doesn't depend
on the count (the first 5 programs of 5 and of 200 are the same).
-/

namespace StrataPython.AxisFuzzTest

open Strata.Dyn.Exec
open Strata.Dyn.Exec.Diff (Entry Verdict)
open StrataPython.AxisSource

private meta def here : System.FilePath := "StrataPythonTest" / "Dyn" / "axes"
private meta def knownDir : System.FilePath := here / "fuzz_known"
private meta def knownSuffix : String := ".known.trace"

/-- The verdict of the fuzz program `p` in `dir`, with CPython under all eight seeds (`allSeeds`)
or seed 0 alone, and our run to pin for a `known` program in update mode; or why the test fails
on it. `reasons` maps each program pinned as `known` to its reason; `pins` is false in live mode,
where nothing is pinned. -/
private meta def runProgram (pythonCmd dir : System.FilePath) (allSeeds update pins : Bool)
    (reasons : Std.HashMap String String) (p : FuzzProgram) :
    IO (Except String (Entry × Option String × Bool)) := do
  let file := dir / s!"{p.id}.py"
  let eight := allSeeds || p.seedBucket
  let traces ← if eight then seeds.toArray.mapM (cpythonTraceSeed pythonCmd file)
    else pure #[← cpythonTraceSeed pythonCmd file 0]
  let ours ← SemDiff.runOurs file
  if let some bug := fuzzBug? p traces[0]! ours then return .error bug
  -- Whether our run reaches the seed-dependent step, so that the step is checked.
  let reaches := match ours with
    | .trace t => (SemDiff.splitOutput t).any fun (o, _) => (o.splitOn "\n").contains "@op seed"
    | _ => false
  if p.seedBucket && seedsAgree traces then
    return .error s!"{p.id}: generator bug: its seed-dependent step shows the same order under every seed"
  if !p.seedBucket && !seedsAgree traces then
    return .error s!"{p.id}: generator bug: CPython's trace depends on the hash seed or the machine"
  let known ← match (if pins then reasons.get? p.id else none) with
    | none => pure none
    | some r =>
      -- A pin holds for one program: its id names a draw, which a change of the generator gives
      -- to another program, so the program is pinned with it.
      let program := knownDir / s!"{p.id}.py"
      if ← program.pathExists then
        unless (← IO.FS.readFile program) == (← IO.FS.readFile file) do
          return .error s!"{p.id}: the program pinned as known has changed; check that its \
            reason still holds, then delete {program} and update"
      else if !update then
        return .error s!"{p.id}: missing {program}; run with SEM_UPDATE=1"
      let pin := knownDir / s!"{p.id}{knownSuffix}"
      if update then pure (some ⟨r, none⟩)
      else if ← pin.pathExists then pure (some ⟨r, some (← IO.FS.readFile pin)⟩)
      else return .error s!"{p.id}: missing {pin}; run with SEM_UPDATE=1"
  let ourPin := match ours with
    | .trace t => if update then some t else none
    | _ => none
  if let some k := known then
    -- A pinned run is no check of the seed rule, so it doesn't count as reaching its seed step.
    if let some v := knownGap? p.id p.seedBucket ours traces k then
      return v.map fun v => (⟨p.id, v⟩, ourPin, false)
  if p.seedBucket then
    return (judgeSeedDependent p.id ours traces).map fun v => (⟨p.id, v⟩, none, reaches)
  match SemDiff.judge p.id ours traces[0]! known, ours with
  | .error e, _ => return .error e
  | .ok v@(.known _), _ => return .ok (⟨p.id, v⟩, ourPin, false)
  | .ok v, _ => return .ok (⟨p.id, v⟩, none, false)

/-- The programs of `seed` and `count`, written into `dir`. -/
private meta def generate (pythonCmd dir : System.FilePath) (seed : String) (count : Nat) :
    IO (Array FuzzProgram) := do
  let lines ← TraceSource.programsOf pythonCmd (here / "fuzz.py")
    #[dir.toString, "--seed", seed, "--count", toString count]
  IO.ofExcept (parseFuzz ("\n".intercalate lines.toList))

#eval show IO Unit from do
  if let some skip ← IO.getEnv "SKIP_PYTHON_TESTS" then
    if !skip.isEmpty then return
  unless ← SemDiff.pydynPath.pathExists do
    throw <| .userError s!"{SemDiff.pydynPath} is missing: build it with `lake build pydyn`"
  let pythonCmd ← StrataPython.findPython3 (minVersion := 12) (maxVersion := 12)
  let live := (← IO.getEnv "FUZZ_SEED").isSome
  let seed := (← IO.getEnv "FUZZ_SEED").getD "1"
  let count := ((← IO.getEnv "FUZZ_COUNT").bind (·.toNat?)).getD 200
  let update := !live && (← IO.getEnv "SEM_UPDATE").isSome
  let dir : System.FilePath := ".lake" / "build" / "differential" / s!"fuzz-{seed}"
  let start ← IO.monoMsNow
  let programs ← generate pythonCmd dir seed count
  let mut failures : Array String := #[]
  -- Program `i` doesn't depend on the count.
  let small : System.FilePath := ".lake" / "build" / "differential" / s!"fuzz-{seed}-small"
  for p in (← generate pythonCmd small seed (min 5 count)) do
    unless (← IO.FS.readFile (small / s!"{p.id}.py")) == (← IO.FS.readFile (dir / s!"{p.id}.py")) do
      failures := failures.push s!"{p.id}: generator bug: the program depends on the count"
  let pinned ← if live then pure #[] else TraceSource.readPinned (here / "fuzz_expected.txt")
  let reasons : Std.HashMap String String := pinned.foldl (init := {}) fun m e =>
    match e.verdict with | .known r => m.insert e.path r | _ => m
  IO.FS.createDirAll knownDir
  let results ← TraceSource.mapBounded 8 programs
    (runProgram pythonCmd dir (live || update) update (!live) reasons)
  let mut now : Array Entry := #[]
  let mut pins : Array (String × String) := #[]
  let mut reached := 0
  for r in results do
    match r with
    | .ok (e, pin, reaches) =>
      now := now.push e
      if reaches then reached := reached + 1
      if let some t := pin then pins := pins.push (e.path, t)
    | .error msg => failures := failures.push msg
  let bucket := (programs.filter (·.seedBucket)).size
  -- The build seed must check the seed-dependent rule: some run must reach its seed step.
  if !live && reached == 0 then
    failures := failures.push "no run of the seed bucket reaches its seed-dependent step"
  if !live && failures.isEmpty then
    let digest := String.intercalate "" (← TraceSource.programsOf pythonCmd (here / "fuzz.py")
      #["--digest", dir.toString]).toList ++ "\n"
    if let some f ← checkFile (here / "fuzz_digest.txt") digest update then
      failures := failures.push f
    for ch in ← Diff.checkOrUpdate (here / "fuzz_expected.txt") now update do
      failures := failures.push ch.render
    if update then
      for f in ← knownDir.readDir do IO.FS.removeFile f.path
      for (id, t) in pins do
        IO.FS.writeFile (knownDir / s!"{id}{knownSuffix}") t
        IO.FS.writeFile (knownDir / s!"{id}.py") (← IO.FS.readFile (dir / s!"{id}.py"))
    else
      failures := failures ++ (← stalePins knownDir [knownSuffix, ".py"] reasons.contains "program")
  let secs := ((← IO.monoMsNow) - start) / 1000
  TraceSource.report s!"AxisFuzzTest (seed {seed}, {count} programs, {bucket} seed-dependent of \
    which {reached} reach their seed step, {secs} s)"
    now programs.size failures

end StrataPython.AxisFuzzTest
