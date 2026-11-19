/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Util.SemDiff

/-! # Each lowered loop invariant against CPython

For each loop-invariant program of the translator's corpus (the `li_*` rows of
`StrataPythonTest/Dyn/dyn_tests.txt` with no expected rejection), `invRun` runs the translated
program on the machine, where each compared invariant writes `--- invariant RANK True|False` at
each entry of its loop's head, and `StrataPythonTest/Dyn/invariant_trace.py` runs the program on
CPython, which calls the same invariants' lambdas at the same points, under both hash seeds. The
two traces are compared as the differential test compares them (`SemDiff.judge`): equal, or, when
the machine's run stops with a gap, equal up to the gap. An invariant is compared when the Python
semantics has a rule for each operation of its region, and its `OLD`s read only what has a value
at entry. For an invariant with `OLD`, `invRun` moves each old region to the start of its
function, and prints the parts read at entry that the translator's split gives; the tracer
computes the parts itself, by the rule of §6.11, and fails when they differ, then evaluates them
at the function's first statement. In `quantifierDifferences`, the programs that pin how a
quantifier differs from CPython's `all` and `any` (`docs/PythonToDyn.md` §6.11), the two sides are
not compared: each side's answers are pinned instead.

`StrataPythonTest/Dyn/invariant_runs.expected` pins each invariant's status: compared, with the
number of its evaluations and how many were `True` (on each side, for `quantifierDifferences`),
or skipped, with the reason. Set `INV_UPDATE=1` to rewrite it.
-/

namespace StrataPython.DynInvariantEvalTest

open StrataPython (withPython)

private meta def listFile : System.FilePath := "StrataPythonTest" / "Dyn" / "dyn_tests.txt"

private meta def testDir : System.FilePath := "StrataPythonTest" / "Dyn" / "dyn_tests"

private meta def tracer : System.FilePath := "StrataPythonTest" / "Dyn" / "invariant_trace.py"

private meta def invRun : System.FilePath := ".lake" / "build" / "bin" / "invRun"

private meta def statusFile : System.FilePath :=
  "StrataPythonTest" / "Dyn" / "invariant_runs.expected"

/-- The programs whose quantifier invariants differ from CPython's `all` and `any` by design: they
quantify over strings, ranges, iterators and containers that override their iteration, and a
quantifier whose element raises for some member raises. -/
private meta def quantifierDifferences : List String := ["li_q_kinds"]

/-- The loop-invariant programs that the translator accepts. -/
private meta def programs : IO (Array String) := do
  let mut names := #[]
  for line in (← IO.FS.readFile listFile).splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match (line.splitOn "|").map (·.trimAscii.toString) with
    | [path, "yes", ""] => if path.startsWith "li_" then names := names.push path
    | _ => pure ()
  return names

/-- The header lines of `invRun`'s output: those before its `--- stdout` line. -/
private meta def headerOf (out : String) : List String :=
  (out.splitOn "\n").takeWhile (!·.startsWith "--- stdout ")

/-- The text after `pfx` in the first line of `lines` that starts with it. -/
private meta def field (lines : List String) (pfx : String) : Option String :=
  (lines.find? (·.startsWith pfx)).map fun l => (l.drop pfx.length).toString

/-- `(n, t)`: how many `--- invariant RANK` lines `out` has for `rank`, and how many of them say
`True`. -/
private meta def counts (out : String) (rank : String) : Nat × Nat :=
  ((out.splitOn s!"--- invariant {rank} ").length - 1,
   (out.splitOn s!"--- invariant {rank} True").length - 1)

/-- The trace part of `invRun`'s output: from its first `--- stdout` line on. -/
private meta def traceOf (out : String) : String :=
  let ls := out.splitOn "\n"
  "\n".intercalate (ls.dropWhile (!·.startsWith "--- stdout "))

#eval withPython fun python => do
  let update := (← IO.getEnv "INV_UPDATE").isSome
  unless ← invRun.pathExists do
    throw <| .userError s!"{invRun} is missing: build it with `lake build invRun`"
  let mut failures : Array String := #[]
  let mut status : Array String := #[]
  let mut compared := 0
  for name in ← programs do
    let py := (testDir / s!"{name}.py").toString
    let m ← IO.Process.output { cmd := invRun.toString, args := #[py] }
    unless m.exitCode == 0 do
      failures := failures.push s!"{name}: invRun failed ({m.exitCode}): {m.stderr}"
      continue
    let header := headerOf m.stdout
    let ranks := (field header "--- compared ").getD ""
    let statuses := header.filter (·.startsWith "--- status ")
    -- The parts read at entry that the translator's split gives, as `RANK<TAB>PART` lines.
    let parts := (header.filter (·.startsWith "--- part ")).map fun l =>
      let rest := (l.drop "--- part ".length).toString
      match rest.splitOn " " with
      | rank :: _ => s!"{rank}\t{(rest.drop (rank.length + 1)).toString}"
      | [] => rest
    let trace := traceOf m.stdout
    let runs ← IO.FS.withTempDir fun dir => do
      let partsFile := dir / "parts.txt"
      IO.FS.writeFile partsFile (String.join (parts.map (· ++ "\n")))
      #["0", "1"].mapM fun seed => do
        let args := #[tracer.toString, py, ranks, partsFile.toString]
        let c ← IO.Process.output
          { cmd := python.toString, args, env := #[("PYTHONHASHSEED", some seed)] }
        unless c.exitCode == 0 do
          throw <| .userError s!"{name}: invariant_trace.py failed:\n{c.stderr}"
        pure (c.stdout, c.stderr.trimAscii.toString)
    let (out0, ranked) := runs[0]!
    -- Both sides rank the same invariants.
    unless runs.all (·.2 == s!"ranked {statuses.length}") do
      failures := failures.push
        s!"{name}: CPython ranks as {ranked}, but the machine has {statuses.length} invariants"
    let bySide := quantifierDifferences.contains name
    let theirs := SemDiff.joinRuns out0 runs[1]!.1
    unless bySide do
      if let .error e := SemDiff.judge name (.trace trace) theirs none then
        failures := failures.push e
    let out := ((SemDiff.splitOutput trace).map (·.1)).getD ""
    let gap := if (SemDiff.gapOf trace).isSome then ", up to a gap" else ""
    for l in statuses do
      let rest := (l.drop "--- status ".length).toString
      match rest.splitOn " " with
      | rank :: "compared" :: _ =>
        compared := compared + 1
        let (n, t) := counts out rank
        if bySide then
          let (cn, ct) := counts out0 rank
          status := status.push
            s!"{name} {rank} by side: machine {n} evaluations, {t} True; CPython {cn} evaluations, {ct} True{gap}"
        else status := status.push s!"{name} {rank} compared, {n} evaluations, {t} True{gap}"
      | _ => status := status.push s!"{name} {rest}"
  let text := "\n".intercalate status.toList ++ "\n"
  if update then IO.FS.writeFile statusFile text
  else if text != (← IO.FS.readFile statusFile) then
    failures := failures.push s!"the invariants' statuses differ from {statusFile}:\n{text}"
  IO.println s!"DynInvariantEvalTest: {compared} invariants compared, {status.size - compared} skipped"
  unless failures.isEmpty do
    for f in failures do IO.println f
    throw <| .userError s!"DynInvariantEvalTest: {failures.size} failure(s)"

end StrataPython.DynInvariantEvalTest
