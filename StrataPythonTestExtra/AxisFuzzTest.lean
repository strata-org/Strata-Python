/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.AxisSource
meta import StrataDynTest.Exec.Shrink

/-! # Fuzz programs against CPython

Runs the random programs of `StrataPythonTest/Dyn/axes/fuzz.py` (classes with special methods of
each behaviour and descriptor kind, values, and operations on them, each step in its own `try`)
with CPython 3.12 and with the Python semantics, and judges each pair.

* **Build seed** (the default): the 200 programs of seed 1, against the verdicts pinned in
  `StrataPythonTest/Dyn/axes/fuzz_expected.txt`, our runs of the `known` programs and the programs
  themselves in `fuzz_known/` (a pin holds for one program, not for its id), and `fuzz_digest.txt`
  (the digest stands for this property: CPython's traces under the hash seeds 0 to 7 were
  compared on exactly these programs). CPython runs under seed 0, except for
  the programs of the seed bucket (§ below). It fails on a generator bug
  (`AxisSource.fuzzBug?`), on any difference, on a change of verdict, if no run of the seed
  bucket reaches its seed step, and if a shrink candidate of the first 5 programs or of a known
  program tests nothing (`proposerBugs`). `SEM_UPDATE=1` runs CPython under all eight seeds and
  rewrites the files; an update that fails writes nothing.
* **Live**: `FUZZ_SEED=S FUZZ_COUNT=N lake env lean StrataPythonTestExtra/AxisFuzzTest.lean` runs
  the `N` programs of seed `S` with CPython under all eight seeds, pins nothing, and fails on any
  difference or generator bug. It prints the counts and the time. With `FUZZ_SHRINK=1`, it also
  shrinks each failing program (`shrinkOne`, at most 500 candidates judged, about 15 s each): it
  keeps a smaller program when it fails with the same failure kind (the same step and lines of
  the first difference), and if the last one kept still fails the same way when it runs again, it
  writes it to `.lake/build/differential/fuzz-<S>/` as `repro-<id>.py`, with ours and the CPython
  trace that shows the failure beside it.

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

/-- CPython's traces of the program `file`, under every seed of `seeds` (`eight`) or seed 0 alone,
and our run of it. -/
private meta def runRaw (pythonCmd file : System.FilePath) (eight : Bool) :
    IO (Array String × SemDiff.Ours) := do
  let traces ← if eight then seeds.toArray.mapM (cpythonTraceSeed pythonCmd file)
    else pure #[← cpythonTraceSeed pythonCmd file 0]
  return (traces, ← SemDiff.runOurs file)

/-- The verdict of the fuzz program `p` in `dir`, with CPython under all eight seeds (`allSeeds`)
or seed 0 alone, and our run to pin for a `known` program in update mode; or why the test fails
on it. `reasons` maps each program pinned as `known` to its reason; `pins` is false in live mode,
where nothing is pinned. -/
private meta def runProgram (pythonCmd dir : System.FilePath) (allSeeds update pins : Bool)
    (reasons : Std.HashMap String String) (p : FuzzProgram) :
    IO (Except String (Entry × Option String × Bool)) := do
  let file := dir / s!"{p.id}.py"
  let (traces, ours) ← runRaw pythonCmd file (allSeeds || p.seedBucket)
  -- Whether our run reaches the seed-dependent step, so that the step is checked.
  let reaches := match ours with
    | .trace t => (SemDiff.splitOutput t).any fun (o, _) => (o.splitOn "\n").contains "@op seed"
    | _ => false
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
  -- A pinned run is no check of the seed rule, so it doesn't count as reaching its seed step.
  match fuzzVerdict p traces ours known with
  | .error f => return .error f.msg
  | .ok v@(.known _) => return .ok (⟨p.id, v⟩, ourPin, false)
  | .ok v => return .ok (⟨p.id, v⟩, none, p.seedBucket && reaches)

/-- The programs of `seed` and `count`, written into `dir`. -/
private meta def generate (pythonCmd dir : System.FilePath) (seed : String) (count : Nat) :
    IO (Array FuzzProgram) := do
  let lines ← TraceSource.programsOf pythonCmd (here / "fuzz.py")
    #[dir.toString, "--seed", seed, "--count", toString count]
  IO.ofExcept (parseFuzz ("\n".intercalate lines.toList))

/-- The number of candidates that one shrink judges at most. -/
private meta def shrinkBudget : Nat := 500

/-- Shrink the failing fuzz program `p` in `dir`: `fuzz.py shrink` proposes the candidates, and
one is kept when it fails with the same failure kind (`fuzzFailure?`, CPython under all eight
seeds), so at the same step and lines. Writes the last kept program to `dir/repro-<id>.py`, with
ours and the CPython trace that shows the failure beside it, and gives a line that reports it;
`none` when `p` has no failure kind (a generator bug, or a failure against no single trace). A
candidate whose run throws is not kept, and its error is printed. The shrunk program runs once
more before the repro is written; if that run doesn't fail the same way, the line says so and no
repro is written (`reproSeed?`). -/
private meta def shrinkOne (pythonCmd dir : System.FilePath) (p : FuzzProgram) :
    IO (Option String) := do
  let (traces, ours) ← runRaw pythonCmd (dir / s!"{p.id}.py") true
  let some (kind, _) := fuzzFailure? p traces ours | return none
  let work := dir / s!"shrink-{p.id}"
  if ← work.pathExists then IO.FS.removeDirAll work
  let round ← IO.mkRef 0
  -- Each round's candidates go to their own directory, so a kept candidate's files stay.
  let propose (c : FuzzProgram × System.FilePath) : IO (List (FuzzProgram × System.FilePath)) := do
    let n ← round.modifyGet fun n => (n, n + 1)
    let out := work / s!"round-{n}"
    let lines ← TraceSource.programsOf pythonCmd (here / "fuzz.py")
      #["shrink", (c.2 / s!"{c.1.id}.json").toString, out.toString]
    return (← IO.ofExcept (parseFuzz ("\n".intercalate lines.toList))).toList.map (·, out)
  let judge (cs : List (FuzzProgram × System.FilePath)) : IO (List Bool) := do
    let kept ← TraceSource.mapBounded 8 cs.toArray fun (q, d) => do
      try
        let (ts, o) ← runRaw pythonCmd (d / s!"{q.id}.py") true
        return (fuzzFailure? q ts o).map (·.1) == some kind
      catch e =>
        -- A crash on a candidate is a bug of its own, which this shrink doesn't follow.
        IO.eprintln s!"{d / s!"{q.id}.py"}: the run of this shrink candidate failed: {e}"
        return false
    return kept.toList
  let r ← Shrink.shrink propose judge 8 shrinkBudget (p, dir)
  let (q, d) := r.best
  -- The repro is written only if the shrunk program still fails the same way when it runs again.
  let (ts, o) ← runRaw pythonCmd (d / s!"{q.id}.py") true
  let seed ← match reproSeed? kind (fuzzFailure? q ts o) with
    | .ok s => pure s
    | .error why => return some s!"{p.id}: {kind.render}; {why} ({d / s!"{q.id}.py"}), so no repro is written"
  let repro := dir / s!"repro-{p.id}"
  IO.FS.writeFile (repro.addExtension "py") (← IO.FS.readFile (d / s!"{q.id}.py"))
  IO.FS.writeFile (repro.addExtension "cpython.trace") ts[seed]!
  IO.FS.writeFile (repro.addExtension "ours.trace") (match o with
    | .trace t => t
    | _ => "the translator rejects the program\n")
  let ran := if r.calls ≥ shrinkBudget then " (the budget ran out, so it may shrink further)" else ""
  return some s!"{p.id}: {kind.render}; shrunk from {p.steps.length} to {q.steps.length} \
    steps after judging {r.calls} candidates{ran}: {repro}.py (CPython's trace under \
    PYTHONHASHSEED={seed} beside it)"

/-- The number of candidates of the program `p` in `dir` that the shrink proposer gives, and why
it is wrong on them: a candidate that tests nothing (`fuzzBug?` on CPython's run under seed 0), so
that no shrink could keep it. -/
private meta def proposerBugs (pythonCmd dir : System.FilePath) (p : FuzzProgram) :
    IO (Nat × Array String) := do
  let out := dir / s!"proposals-{p.id}"
  let lines ← TraceSource.programsOf pythonCmd (here / "fuzz.py")
    #["shrink", (dir / s!"{p.id}.json").toString, out.toString]
  let cs ← IO.ofExcept (parseFuzz ("\n".intercalate lines.toList))
  if cs.isEmpty then return (0, #[s!"{p.id}: the shrink proposer gives no candidate"])
  let bugs ← TraceSource.mapBounded 8 cs fun q => do
    let t ← cpythonTraceSeed pythonCmd (out / s!"{q.id}.py") 0
    return (fuzzBug? q t (.trace "")).map (s!"shrink proposer bug: " ++ ·)
  return (cs.size, bugs.filterMap id)

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
  let shrinking := live && (← IO.getEnv "FUZZ_SHRINK").isSome
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
  -- The proposer gives valid candidates of the build seed's first 5 programs and of its known
  -- programs, which are programs that a shrink starts from.
  if !live then
    let mut checked := 0
    for (p, i) in programs.zipIdx do
      if i < 5 || reasons.contains p.id then
        let (n, bugs) ← proposerBugs pythonCmd dir p
        checked := checked + n
        failures := failures ++ bugs
    if checked == 0 then failures := failures.push "the shrink proposer's check checked no candidate"
  if shrinking then
    -- Repros of an earlier run would read as this run's.
    for f in ← dir.readDir do
      if f.fileName.startsWith "repro-" then IO.FS.removeFile f.path
      else if f.fileName.startsWith "shrink-" then IO.FS.removeDirAll f.path
    for (p, r) in programs.zip results do
      if r matches .error _ then
        if let some line ← shrinkOne pythonCmd dir p then IO.println line
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
