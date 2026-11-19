/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import StrataPythonTest.Util.TraceSource
public meta import StrataPythonTest.Util.Python
public meta import Std.Data.HashMap
public meta import Std.Data.HashSet

/-! # Generated differential sources: the shared checks

The axis grid (`StrataPythonTest/Dyn/axes/grid.py`) writes one program per case, and says what
each case expects of CPython. Its test (`AxisGridTest`), in a full run, runs every program with
CPython 3.12 and with the Python semantics, and judges each pair with `SemDiff.judge`; the
fuzzer's test (`AxisFuzzTest`) does the same for the programs of `fuzz.py`. Every build runs only
the grid's quick check, which runs no program. This module holds what the two tests
need besides the judge:

* the *generator-bug checks*: a case whose CPython run doesn't run its operation, or doesn't end
  the way the case expects, tests nothing, so the test fails on it instead of pinning a verdict
  (`generatorBug?`);
* CPython's trace under one hash seed, and the check that the eight traces under the seeds 0 to
  7 are equal (`cpythonTraceSeed`, `seedsAgree`);
* the summary of the verdicts by group and axis (`summary`);
* the coverage check (`coverage`): every name of the model's tables is covered by a case that
  agrees with CPython, by observed evidence (a call in CPython's run, an instruction of the
  operation's translation) or by a declared entry of the catalog, or `not_covered.txt` lists it;
  it is the judgment (`judgeCoverage`) of the facts of the cases' runs (`coverageFacts`), which a
  full run writes as text (`printCoverageFacts`) and the quick check reads (`parseCoverageFacts`);
* the stamp of a test's sources (`sourcesStamp`, `gridSources`, `fuzzSources`, `checkStamp`), so
  that the quick check sees a change to a source without that test's update;
* the fuzzer's checks: its programs (`FuzzProgram`, `parseFuzz`), the generator-bug checks of a
  fuzz program (`fuzzBug?`, with `runBug?`), the verdict of a program whose output depends on the
  hash seed (`judgeSeedDependent`), and a pinned program that gaps (`knownGap?`);
* the files that both tests compare or write (`checkFile`, `stalePins`);
* the shrinker's checks: one verdict for a fuzz program (`fuzzVerdict`), how a run fails against
  CPython (`failureKind?`, `fuzzFailure?`), and whether a shrunk program still fails the same way
  when it runs again (`reproSeed?`).

A case prints `@op <id>` right before its operation and `@done <id>` after the `try` around it;
between them, a `= ...` line for a result or a `! <ExcType>: ...` line for an exception, an
`ev <name>` line for each user call, an `is ...` line for the identity of a result, and a
`self ...` line for the receiver of a method after the call.
-/

public meta section

namespace StrataPython.AxisSource

open Strata.Dyn.Exec
open Strata.Dyn.Exec.Diff (Entry Verdict)

/-- What a case expects of CPython. -/
inductive Expect where
  /-- The operation gives a result. -/
  | result
  /-- The operation raises an exception of this type. -/
  | raises (exc : String)
  /-- The translator rejects this construct on purpose; CPython's run is not checked further. -/
  | rejects (construct : String)
  /-- The operation gives a result or raises; the markers are still checked. -/
  | any
  deriving DecidableEq, Repr, Inhabited

/-- The expectation that `grid.py` prints: `result`, `raises:<ExcType>`, `rejects:<construct>` or
`any`. -/
def Expect.parse (s : String) : Except String Expect :=
  if s == "result" then .ok .result
  else if s == "any" then .ok .any
  else if let some e := s.dropPrefix? "raises:" then .ok (.raises e.toString)
  else if let some c := s.dropPrefix? "rejects:" then .ok (.rejects c.toString)
  else .error s!"unknown expectation: {s}"

/-- One case of a generated source: its id, its group and axis (for the summary), what it
expects of CPython, and for the coverage check: its operation's template, the built-in functions
and methods it calls by name, and the dunder entries its operation reaches without a call. -/
structure Case where
  id : String
  group : String
  axis : String
  expect : Expect
  template : String := ""
  calls : List String := []
  entries : List String := []
  deriving Repr, Inhabited

/-- A comma-separated list, `-` for the empty one. -/
private def parseList (s : String) : List String :=
  if s == "-" then [] else s.splitOn ","

/-- The cases that `grid.py` printed, one line per case:
`<id> | <group> | <axis> | <expectation> | <template> | <calls> | <entries>`. -/
def parseCases (text : String) : Except String (Array Case) := do
  let mut out := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn " | " with
    | [id, group, axis, e, t, calls, entries] =>
      out := out.push { id, group, axis, expect := ← Expect.parse e, template := t,
                        calls := parseList calls, entries := parseList entries }
    | _ => throw s!"malformed case line: {line}"
  return out

/-- How a case ended in CPython's output. -/
inductive Outcome where
  | result
  | raises (exc : String)
  deriving DecidableEq, Repr

/-- The outcome as a phrase: `a result`, or `raises <ExcType>`. -/
def Outcome.render : Outcome → String
  | .result => "a result"
  | .raises e => s!"raises {e}"

/-- The expectation as a phrase. -/
def Expect.render : Expect → String
  | .result => "a result"
  | .raises e => s!"raises {e}"
  | .rejects c => s!"a rejection of {c}"
  | .any => "a result or an exception"

/-- How the case `id` ended in the program's output `out`: the last line between its markers that
is not a user call (`ev `), an identity line (`is `) or a receiver line (`self `); or why the
output doesn't show it. -/
def caseOutcome (id out : String) : Except String Outcome := do
  let lines := out.splitOn "\n"
  let some i := lines.findIdx? (· == s!"@op {id}")
    | throw "the operation never ran (no @op line)"
  let some j := lines.findIdx? (· == s!"@done {id}")
    | throw "the case didn't finish (no @done line)"
  unless i < j do throw "the @done line comes before the @op line"
  let body := ((lines.drop (i + 1)).take (j - i - 1)).filter fun l =>
    !(l.startsWith "ev ") && !(l.startsWith "is ") && !(l.startsWith "self ")
  match body.getLast? with
  | some l =>
    if l.startsWith "= " then return .result
    else if let some rest := l.dropPrefix? "! " then
      return .raises ((rest.toString.splitOn ":").head!)
    else throw s!"the case's last line is neither a result nor an exception: {l}"
  | none => throw "the case printed no result and no exception"

/-- CPython's output of a generated program, from its trace `theirs`; or, as the error, why the
program can't test anything: CPython doesn't compile it, its run doesn't end, or the run doesn't end
with the outcome `ok`. -/
def runBug? (theirs : String) : Except String String :=
  if theirs == SemDiff.syntaxTrace then .error "CPython doesn't compile the program"
  else if theirs == SemDiff.endlessTrace then .error "CPython's run doesn't end in time"
  else match SemDiff.splitOutput theirs with
    | none => .error "CPython's trace has no output section"
    | some (out, rest) =>
      if !rest.startsWith "--- outcome\nok\n" then .error "CPython's run doesn't end with `ok`"
      else .ok out

/-- Why the case `c` tests nothing, from CPython's trace `theirs` and what `pydyn run` gave; `none`
when it tests its operation. -/
def generatorBug? (c : Case) (theirs : String) (ours : SemDiff.Ours) : Option String :=
  let bug (why : String) := some s!"{c.id}: generator bug: {why}"
  if theirs == SemDiff.syntaxTrace then bug "CPython doesn't compile the program"
  else if theirs == SemDiff.endlessTrace then bug "CPython's run doesn't end in time"
  else match ours, c.expect with
  | .syntax, _ => bug "the translator reports a syntax error"
  | .unsupported cs, .rejects construct =>
    if cs.contains construct then none
    else bug s!"the translator rejects {", ".intercalate cs}, not {construct}"
  | .unsupported cs, _ => bug s!"the translator rejects {", ".intercalate cs}"
  | .trace _, .rejects construct => bug s!"the translator doesn't reject {construct}"
  | .trace _, expect =>
    match runBug? theirs with
    | .error why => bug why
    | .ok out =>
      match caseOutcome c.id out, expect with
      | .error e, _ => bug e
      | .ok _, .any => none
      | .ok .result, .result => none
      | .ok (.raises e), .raises e' => if e == e' then none else
        bug s!"CPython raises {e}, the case expects {e'}"
      | .ok o, e => bug s!"CPython's case ends with {o.render}, the case expects {e.render}"

/-- Whether the case `c` observes its operation: CPython's trace of the program differs from its
trace of the same program with the operation replaced by `r = None` (`<id>.null.py`). A case
that the translator is meant to reject needs no such check. -/
def observes (c : Case) (theirs null : String) : Bool :=
  c.expect matches .rejects _ || theirs != null

/-- The hash seeds under which CPython runs a program before its trace is pinned. -/
def seeds : List Nat := List.range 8

/-- CPython's trace of `pyFile` under `PYTHONHASHSEED=seed`, with a fixed locale and output
encoding; `SemDiff.endlessTrace` if it doesn't end within `SemDiff.cpythonSeconds`. -/
def cpythonTraceSeed (pythonCmd pyFile : System.FilePath) (seed : Nat) : IO String := do
  let r ← IO.Process.output {
    cmd := "timeout"
    args := #[toString SemDiff.cpythonSeconds, pythonCmd.toString,
      SemDiff.traceScript.toString, pyFile.toString]
    env := #[("PYTHONHASHSEED", some (toString seed)), ("LC_ALL", some "C.UTF-8"),
      ("PYTHONIOENCODING", some "utf-8")] }
  if r.exitCode == 124 then return SemDiff.endlessTrace
  unless r.exitCode == 0 do
    throw <| .userError s!"{pyFile}: trace.py failed:\n{r.stderr}"
  return r.stdout

/-- Whether CPython's traces under the hash seeds of `seeds` are all equal. -/
def seedsAgree (traces : Array String) : Bool :=
  match traces[0]? with
  | some t0 => traces.all (· == t0)
  | none => true

/-- The summary of the verdicts `now` of the cases `cases`: per (group, axis), the counts of
agree, gap and known, sorted, and a total line. -/
def summary (cases : Array Case) (now : Array Entry) : String := Id.run do
  let byId : Std.HashMap String Case := cases.foldl (fun m c => m.insert c.id c) {}
  let mut rows : Std.HashMap (String × String) (Nat × Nat × Nat) := {}
  for e in now do
    let some c := byId.get? e.path | continue
    let (a, g, k) := rows.getD (c.group, c.axis) (0, 0, 0)
    rows := rows.insert (c.group, c.axis) <| match e.verdict with
      | .agree => (a + 1, g, k)
      | .gap _ => (a, g + 1, k)
      | .known _ => (a, g, k + 1)
      | .syntax => (a, g, k)
  let keys := rows.toArray.map (·.1) |>.qsort fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 < y.2)
  let mut out := ""
  let mut total := (0, 0, 0)
  for key in keys do
    let (a, g, k) := rows.getD key (0, 0, 0)
    total := (total.1 + a, total.2.1 + g, total.2.2 + k)
    out := out ++ s!"{key.1} | {key.2} | {a} agree | {g} gap | {k} known\n"
  out ++ s!"total | {now.size} cases | {total.1} agree | {total.2.1} gap | {total.2.2} known\n"

/-! ## The coverage check

Coverage comes from the cases that agree with CPython: from their runs and translations
(observed), or from the catalog alone (declared). A case counts only if its verdict is `agree`: a
`known` case is a wrong result, and a gap is no claim. What a counted case shows is kept apart by
where it comes from:
* *observed*: the built-in functions and methods that CPython called by name during its operation
  (`cpython_calls.py`), and the py.* and base instructions that its operation's translation has
  (its template translated with and without the operation; an instruction there may still not run,
  e.g. `base.unreachable`);
* *declared*: the dunder entries that the catalog says its operation reaches without a call (`len`
  of a `list` reaches `list.__len__`), and the attributes of `typing` and `dataclasses` that its
  code reads, which no run shows.
A case whose CPython run raises in its operation (a binding error, a wrong argument) covers only
its (name, axis) cells, never a name: it doesn't show what the name computes. Every name of the
model's tables must be covered, and every (name, axis) cell that the catalog declares for such a
name, unless `not_covered.txt` names it with a reason; an entry there must name a name of the
tables (or a declared cell of one) that nothing covers. The names that only declared entries
cover are reported apart (`Coverage.byEntriesOnly`). -/

/-- The instruction names of a printed module (`pydyn dyn`): each `py.<name>` or `base.<name>`
right after `= ` (an instruction whose result is bound) or at the start of a statement, and the
block terminators, which print without their namespace: `jump`, `branch(…)` and `unreachable`.
A line that ends with `:` is a block's label. -/
def insnNames (module : String) : List String := Id.run do
  let mut out : List String := []
  for line in module.splitOn "\n" do
    let stmt := line.trimAscii.toString
    if stmt.endsWith ":" then continue
    let rhs := match line.splitOn " = " with
      | [_, r] => r
      | _ => stmt
    let word := String.ofList (rhs.toList.takeWhile fun (c : Char) =>
      c.isAlphanum || c == '.' || c == '_')
    let name :=
      if rhs.startsWith "py." || rhs.startsWith "base." then some word
      else if word == "jump" || word == "branch" || word == "unreachable" then some s!"base.{word}"
      else none
    if let some n := name then
      unless out.contains n do out := out ++ [n]
  return out

/-- The instructions that a run which agrees with CPython can never execute, though a translation
has them: `base.unreachable` stops the run with a failure. They never count as covered. -/
def neverRuns : List String := ["base.unreachable"]

/-- Whether a case with this verdict counts for coverage: only `agree`. -/
def counts : Option Verdict → Bool
  | some .agree => true
  | _ => false

/-- What one case shows for the coverage check: whether it counts, whether its CPython run gave a
result (not an exception) in its operation, the names CPython called in it, and the instructions
of its operation's translation. `cells` is false for the program around every operation, whose
instructions count for the names only. -/
structure Evidence where
  case : Case
  counted : Bool
  result : Bool
  called : List String
  insns : List String
  cells : Bool := true
  deriving Inhabited

/-- An entry of `not_covered.txt`: a name, or a (name, axis) cell, and the reason. -/
structure NotCovered where
  name : String
  axis : Option String
  reason : String
  deriving Repr, Inhabited

/-- The entries of `not_covered.txt`: `<name> | <reason>` or `<name> @ <axis> | <reason>`, one per
line; `#` starts a comment line. -/
def parseNotCovered (text : String) : Except String (Array NotCovered) := do
  let mut out := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " | " with
    | [key, reason] =>
      match key.splitOn " @ " with
      | [n] => out := out.push ⟨n, none, reason⟩
      | [n, a] => out := out.push ⟨n, some a, reason⟩
      | _ => throw s!"malformed not-covered entry: {line}"
    | _ => throw s!"malformed not-covered entry: {line}"
  return out

/-- The result of the coverage check: its failures, and the names that only declared entries
cover, each with the cases that declare it, in the order of the cases. -/
structure Coverage where
  failures : Array String
  byEntriesOnly : Array (String × Array String)
  deriving Repr, BEq

/-- The cases `ids` that declare a name, in a message: the first one, and how many more. -/
def declaredBy (ids : Array String) : String :=
  match ids.toList with
  | [] => "no case"
  | [i] => i
  | i :: rest => s!"{i} and {rest.length} more"

/-- What the cases' runs show for the coverage check, without the model's names: the names that a
run observed, the names that the catalog's entries declare (with the cases that declare them), the
same for cells (a name with an axis), every declared cell, and the entries of the counted cases.
`observed` and `byEntries` take only the cases that count (they agree with CPython) and give a
result; the cells and `caseEntries` take every case that counts; `declared` takes every case. Every
array but `caseEntries` is sorted, and `caseEntries` and each list of cases are in the cases' order,
so that the facts print the same way on every run. A full run of the grid writes them
(`printCoverageFacts`), and the quick check judges them again without running a program. -/
structure CoverageFacts where
  observed : Array String
  byEntries : Array (String × Array String)
  /-- The observed cells that are also declared: the judgment asks only about those. -/
  observedCells : Array (String × String)
  entryCells : Array ((String × String) × Array String)
  declared : Array (String × String)
  /-- The (case, name) pairs of the entries of the cases that count, in the cases' order. -/
  caseEntries : Array (String × String)
  deriving Repr, BEq, Inhabited

/-- Pairs of strings, ordered by their first string, then by their second. -/
private instance : Ord (String × String) := lexOrd

/-- The pairs of `m`, sorted by key. -/
private def sortedPairs {α : Type} [BEq α] [Hashable α] [Ord α] {β : Type}
    (m : Std.HashMap α β) : Array (α × β) :=
  m.toArray.qsort fun a b => compare a.1 b.1 == .lt

/-- The elements of `s`, sorted. -/
private def sortedSet {α : Type} [BEq α] [Hashable α] [Ord α] (s : Std.HashSet α) : Array α :=
  s.toArray.qsort fun a b => compare a b == .lt

/-- The coverage facts of the cases' evidence `evs`, and the failures that only the runs show: a
case that names a call that CPython's run doesn't show. -/
def coverageFacts (evs : Array Evidence) : CoverageFacts × Array String := Id.run do
  let mut fails : Array String := #[]
  let mut observed : Std.HashSet String := {}
  let mut byEntries : Std.HashMap String (Array String) := {}
  let mut observedCells : Std.HashSet (String × String) := {}
  let mut entryCells : Std.HashMap (String × String) (Array String) := {}
  let mut declared : Std.HashSet (String × String) := {}
  let mut caseEntries : Array (String × String) := #[]
  for ev in evs do
    let c := ev.case
    for n in c.calls ++ c.entries do declared := declared.insert (n, c.axis)
    unless ev.counted do continue
    if ev.result then
      for n in c.calls do
        unless ev.called.contains n do
          fails := fails.push s!"{c.id}: the case calls {n} by name, but CPython's run doesn't show it"
    for n in c.entries do caseEntries := caseEntries.push (c.id, n)
    let insns := ev.insns.filter (!neverRuns.contains ·)
    if ev.result then
      for n in ev.called ++ insns do observed := observed.insert n
      for n in c.entries do byEntries := byEntries.insert n ((byEntries.getD n #[]).push c.id)
    if ev.cells then
      for n in ev.called ++ insns do observedCells := observedCells.insert (n, c.axis)
      for n in c.entries do
        entryCells := entryCells.insert (n, c.axis) ((entryCells.getD (n, c.axis) #[]).push c.id)
  let cells := (sortedSet observedCells).filter declared.contains
  return (⟨sortedSet observed, sortedPairs byEntries, cells, sortedPairs entryCells,
    sortedSet declared, caseEntries⟩, fails)

/-- The judgment of the coverage check, for the model's names `required` (its tables), the facts
`f` and the entries `nc` of `not_covered.txt`. -/
def judgeCoverage (required : Array String) (f : CoverageFacts) (nc : Array NotCovered) :
    Coverage := Id.run do
  let mut fails : Array String := #[]
  let req : Std.HashSet String := required.foldl (·.insert ·) {}
  let observed : Std.HashSet String := f.observed.foldl (·.insert ·) {}
  let byEntries : Std.HashMap String (Array String) :=
    f.byEntries.foldl (fun m (k, v) => m.insert k v) {}
  let observedCells : Std.HashSet (String × String) := f.observedCells.foldl (·.insert ·) {}
  let entryCells : Std.HashMap (String × String) (Array String) :=
    f.entryCells.foldl (fun m (k, v) => m.insert k v) {}
  let declared : Std.HashSet (String × String) := f.declared.foldl (·.insert ·) {}
  for (id, n) in f.caseEntries do
    unless req.contains n do
      fails := fails.push s!"{id}: the catalog says the case reaches {n}, which no table of \
        the model has"
  let covered (n : String) := observed.contains n || byEntries.contains n
  let cellCovered (k : String × String) := observedCells.contains k || entryCells.contains k
  -- How an entry of `not_covered.txt` is covered, for its message: by a run, or only by cases
  -- that declare it.
  let how (run : Bool) (decl : Option (Array String)) : String :=
    if run then "is covered"
    else s!"is covered only by the declared entries of {declaredBy (decl.getD #[])}"
  let byName : Std.HashSet String := nc.foldl (fun s e => if e.axis.isNone then s.insert e.name else s) {}
  let byCell : Std.HashSet (String × String) :=
    nc.foldl (fun s e => match e.axis with | some a => s.insert (e.name, a) | none => s) {}
  for n in required do
    unless covered n || byName.contains n do
      fails := fails.push s!"{n}: no case that agrees with CPython reaches it, and not_covered.txt \
        doesn't list it"
  -- A cell counts only for a name of the tables: a name that the model doesn't implement gaps by
  -- design.
  for (n, a) in f.declared do
    unless !req.contains n || cellCovered (n, a) || byCell.contains (n, a) || byName.contains n do
      fails := fails.push s!"{n} @ {a}: no case of the axis that agrees with CPython reaches it, \
        and not_covered.txt doesn't list the cell"
  for e in nc do
    match e.axis with
    | none =>
      if !req.contains e.name then
        fails := fails.push s!"not_covered.txt: {e.name} is no name of the model's tables"
      else if covered e.name then
        fails := fails.push s!"not_covered.txt: {e.name} {how (observed.contains e.name)
          (byEntries.get? e.name)}; remove its entry"
    | some a =>
      if !req.contains e.name || !declared.contains (e.name, a) then
        fails := fails.push s!"not_covered.txt: no case declares {e.name} @ {a} for a name of the \
          model's tables"
      else if cellCovered (e.name, a) then
        fails := fails.push s!"not_covered.txt: {e.name} @ {a} {how (observedCells.contains (e.name, a))
          (entryCells.get? (e.name, a))}; remove its entry"
  let entryOnly := (required.filter fun n => byEntries.contains n && !observed.contains n).map
    fun n => (n, byEntries.getD n #[])
  return ⟨fails, entryOnly⟩

/-- The coverage facts as text, one fact per line: `observed | <name>`, `entries | <name> |
<cases>`, `cell | <name> @ <axis>`, `entry-cell | <name> @ <axis> | <cases>`, `declared | <name> @
<axis>` and `case-entry | <case> | <name>`, where `<cases>` is a space-separated list. -/
def printCoverageFacts (f : CoverageFacts) : String :=
  let cell (k : String × String) := s!"{k.1} @ {k.2}"
  let ids (a : Array String) := " ".intercalate a.toList
  String.join <|
    (f.observed.map (s!"observed | {·}\n")).toList ++
    (f.byEntries.map fun (n, is) => s!"entries | {n} | {ids is}\n").toList ++
    (f.observedCells.map (s!"cell | {cell ·}\n")).toList ++
    (f.entryCells.map fun (k, is) => s!"entry-cell | {cell k} | {ids is}\n").toList ++
    (f.declared.map (s!"declared | {cell ·}\n")).toList ++
    (f.caseEntries.map fun (i, n) => s!"case-entry | {i} | {n}\n").toList

/-- The coverage facts that `printCoverageFacts` printed. -/
def parseCoverageFacts (text : String) : Except String CoverageFacts := do
  let cell (line s : String) : Except String (String × String) :=
    match s.splitOn " @ " with
    | [n, a] => pure (n, a)
    | _ => throw s!"malformed cell in the coverage facts: {line}"
  let ids (s : String) : Array String := ((s.splitOn " ").filter (!·.isEmpty)).toArray
  let mut f : CoverageFacts := {
    observed := #[], byEntries := #[], observedCells := #[], entryCells := #[], declared := #[],
    caseEntries := #[] }
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn " | " with
    | ["observed", n] => f := { f with observed := f.observed.push n }
    | ["entries", n, is] => f := { f with byEntries := f.byEntries.push (n, ids is) }
    | ["cell", c] => f := { f with observedCells := f.observedCells.push (← cell line c) }
    | ["entry-cell", c, is] =>
      f := { f with entryCells := f.entryCells.push (← cell line c, ids is) }
    | ["declared", c] => f := { f with declared := f.declared.push (← cell line c) }
    | ["case-entry", i, n] => f := { f with caseEntries := f.caseEntries.push (i, n) }
    | _ => throw s!"malformed line in the coverage facts: {line}"
  return f

/-- The coverage check, for the model's names `required` (its tables), the cases' evidence `evs`
and the entries `nc` of `not_covered.txt`, and the facts' text, which a full run of the grid writes.
The check judges the facts as they read back from their text, as the quick check judges them, and
fails if they don't read back as they were written. The failures that only the runs show come
first. -/
def coverageText (required : Array String) (evs : Array Evidence) (nc : Array NotCovered) :
    Coverage × String :=
  let (f, fails) := coverageFacts evs
  let text := printCoverageFacts f
  match parseCoverageFacts text with
  | .ok g =>
    if g == f then
      let c := judgeCoverage required g nc
      ({ c with failures := fails ++ c.failures }, text)
    else (⟨fails.push "the coverage facts don't read back as written", #[]⟩, text)
  | .error e => (⟨fails.push e, #[]⟩, text)

/-- The coverage check, for the model's names `required` (its tables), the cases' evidence `evs`
and the entries `nc` of `not_covered.txt`: `coverageText` without the text. -/
def coverage (required : Array String) (evs : Array Evidence) (nc : Array NotCovered) :
    Coverage :=
  (coverageText required evs nc).1

/-- The stamp of the sources `files` of a test's programs: a hash of each file's path and bytes, in
the order of `files`, as `sources <hex>`. A test's update writes it; the quick check compares it, so
that a change to a source without that test's update fails. It detects edits; it isn't a security
hash. It uses Lean's native hash, so that the quick check stays fast; a Lean upgrade that changes
that hash fails the quick check until the next update. -/
def sourcesStamp (files : Array System.FilePath) : IO String := do
  let mut h : UInt64 := 7
  for f in files do
    h := mixHash h (hash f.toString)
    h := mixHash h (hash (← IO.FS.readBinFile f))
  return s!"sources {String.ofList (Nat.toDigits 16 h.toNat)}"

/-- The directory of the generated tests' sources. -/
def axesDir : System.FilePath := ("StrataPythonTest" : System.FilePath) / "Dyn" / "axes"

/-- The sources of the fuzzer's programs: `fuzz.py` uses the grid's prelude, and the tracer. -/
def fuzzSources : Array System.FilePath :=
  #[axesDir / "catalog.py", axesDir / "fuzz.py", axesDir / "grid.py",
    ("StrataPythonTest" : System.FilePath) / "Dyn" / "trace.py"]

/-- The sources of the grid's programs and of its coverage facts, then the facts, which a full run
of the grid writes: the catalog, the generator, the call tracer, the typing programs
(`typing/*.py`), the tracer, the Lean code that computes the facts (this module and
`AxisGridTest.lean`), and `grid_coverage.txt`. -/
def gridSources : IO (Array System.FilePath) := do
  let typing := ((← (axesDir / "typing").readDir).filter (·.fileName.endsWith ".py")).map (·.path)
  let typing := typing.qsort fun a b => a.toString < b.toString
  return #[axesDir / "catalog.py", axesDir / "cpython_calls.py", axesDir / "grid.py"] ++ typing ++
    #[("StrataPythonTest" : System.FilePath) / "Dyn" / "trace.py",
      ("StrataPythonTest" : System.FilePath) / "Util" / "AxisSource.lean",
      ("StrataPythonTestExtra" : System.FilePath) / "AxisGridTest.lean", axesDir / "grid_coverage.txt"]

/-- Whether the digest file's text `digest` holds the stamp `stamp`; or the failure, which names
the test (`test`) whose update writes the file. -/
def checkStamp (test : String) (file : System.FilePath) (digest stamp : String) : Option String :=
  if (digest.splitOn "\n").contains stamp then none
  else some s!"{file}: the sources changed since {test}'s last update; run {test} with SEM_UPDATE=1"

/-! ## Fuzz programs

A fuzz program (`StrataPythonTest/Dyn/axes/fuzz.py`) is a list of steps, each between its own
`@op <step>` and `@done <step>` lines; a step that uses a class or value whose definition raised
prints `skip <step>` between them. A program of the `seed` bucket prints, as its last step, the
iteration order of a set of strings, which depends on the hash seed. -/

/-- One fuzz program: its id, its steps, and the steps that define a class whose creation is meant
to raise. -/
structure FuzzProgram where
  id : String
  steps : List String
  failing : List String := []
  deriving Repr, Inhabited

/-- Whether the program is in the seed-dependent bucket: its last step is `seed`. -/
def FuzzProgram.seedBucket (p : FuzzProgram) : Bool := p.steps.getLast? == some "seed"

/-- The programs that `fuzz.py` printed, one `<id> | <plain or seed> | <steps> | <failing>` per
line. -/
def parseFuzz (text : String) : Except String (Array FuzzProgram) := do
  let mut out := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn " | " with
    | [id, bucket, steps, failing] =>
      unless bucket == "plain" || bucket == "seed" do throw s!"unknown bucket: {line}"
      let p : FuzzProgram := ⟨id, steps.splitOn ",", if failing == "-" then [] else failing.splitOn ","⟩
      unless p.seedBucket == (bucket == "seed") do
        throw s!"the bucket disagrees with the last step: {line}"
      out := out.push p
    | _ => throw s!"malformed fuzz line: {line}"
  return out

/-- Why the fuzz program `p` tests nothing, from CPython's trace `theirs` and what `pydyn run` gave;
`none` when each of its steps ran. -/
def fuzzBug? (p : FuzzProgram) (theirs : String) (ours : SemDiff.Ours) : Option String :=
  let bug (why : String) := some s!"{p.id}: generator bug: {why}"
  match ours, runBug? theirs with
  | _, .error why => bug why
  | .syntax, _ => bug "the translator reports a syntax error"
  | .unsupported cs, _ => bug s!"the translator rejects {", ".intercalate cs}"
  | .trace _, .ok out =>
    let lines := out.splitOn "\n"
    -- A step that names a value whose definition didn't run must skip, not fail.
    if lines.any (·.startsWith "! NameError") then bug "a step uses a name that no step defined"
    else match p.steps.find? fun s => !(lines.contains s!"@op {s}" && lines.contains s!"@done {s}") with
    | some s => bug s!"step {s} didn't run (no @op or @done line)"
    | none =>
      -- A class step that runs raises exactly when the tree says that its creation is meant to
      -- raise (a class whose base failed skips).
      let raises (s : String) := caseOutcome s out matches .ok (.raises _)
      match p.steps.find? fun s =>
          s.startsWith "c:" && !lines.contains s!"skip {s}" && raises s != p.failing.contains s with
      | some s => bug s!"the creation of {s} raises, or doesn't, against the program's tree"
      | none => none

/-- The verdict of a fuzz program pinned as `known` (`k`) whose run stops with a gap after its
documented difference, which the judge rejects as a run that differs before its gap; `none` for any
other run, which the judge decides. The judge's other checks still hold first: the gap is no model
invariant, the run has no fault and isn't out of fuel, and each of CPython's `traces` is a plain
run. The run must be its pinned trace, as in `Diff.classify`. A program of the seed bucket
(`seedBucket`) must also stop before it prints anything of its seed step, so that the pin never
covers output that depends on the hash seed. -/
def knownGap? (name : String) (seedBucket : Bool) (ours : SemDiff.Ours) (traces : Array String)
    (k : Diff.Known) : Option (Except String Verdict) := do
  let .trace t := ours | none
  let (out, before, msg) ← SemDiff.splitGap t
  if seedBucket then
    let lines := out.splitOn "\n"
    if let some i := lines.idxOf? "@op seed" then
      if (lines.drop (i + 1)).any (· != "") then
        return .error s!"{name}: the run prints its seed-dependent step before its gap"
  let outOfFuel := ((SemDiff.splitOutput t).map (·.2.splitOn "\n")).any (·.contains "--- out of fuel")
  guard (!StrataPython.Dyn.Sem.isModelInvariant msg && (SemDiff.faultOf t).isNone && !outOfFuel)
  guard (traces.all fun th => th != SemDiff.syntaxTrace && th != SemDiff.endlessTrace &&
    !th.startsWith SemDiff.twoRunsHeader)
  guard (traces.any fun th => !SemDiff.agreesBeforeTrace out before th)
  pure <| match k with
    | ⟨r, none⟩ => .ok (.known r)
    | ⟨r, some pin⟩ =>
      if pin == t then .ok (.known r) else .error s!"{name}: the run's trace differs from its pinned trace"

/-- The verdict of a program of the seed bucket from what `pydyn run` gave and CPython's traces under
the hash seeds of `seeds`: they must differ, else the program shows nothing seed-dependent (a
generator bug); our run must stop with a gap that agrees with *every* trace up to it, so that it
claims nothing where CPython's runs differ; and the judge against the first trace must accept it,
so that its other checks (a model invariant, a fault, fuel) still apply. -/
def judgeSeedDependent (name : String) (ours : SemDiff.Ours) (traces : Array String) :
    Except String Verdict := do
  if seedsAgree traces then
    throw s!"{name}: generator bug: its seed-dependent step shows the same order under every seed"
  let .trace t := ours
    | throw s!"{name}: the translator rejects the program"
  let some (out, before, msg) := SemDiff.splitGap t
    | throw s!"{name}: the run gives a result where CPython's runs depend on the hash seed\n\
        --- ours\n{t}"
  for h : i in [:traces.size] do
    unless SemDiff.agreesBeforeTrace out before traces[i] do
      throw s!"{name}: the run differs before its gap from CPython's run under PYTHONHASHSEED={i}\n\
        --- ours\n{t}--- CPython\n{traces[i]}"
  match SemDiff.judge name ours traces[0]! none with
  | .ok (.gap _) => return .gap msg
  | .ok _ => throw s!"{name}: the judge doesn't see the gap"
  | .error e => throw e

/-- Compare `text` with the file `path`, or write it in update mode; the message of a
difference, or `none`. -/
def checkFile (path : System.FilePath) (text : String) (update : Bool) : IO (Option String) := do
  if update then
    IO.FS.writeFile path text
    return none
  let old ← if ← path.pathExists then IO.FS.readFile path else pure ""
  return if old == text then none else
    some s!"{path} differs from this run; run with SEM_UPDATE=1 after checking the change"

/-- The files of the pin directory `dir` that pin nothing. A file pins something only when its name
is `<id><suffix>` for one of `suffixes` and `known id` holds; any other file is stale. One message
per stale file, naming what a pin is for (`what`, e.g. "case"). -/
def stalePins (dir : System.FilePath) (suffixes : List String) (known : String → Bool)
    (what : String) : IO (Array String) := do
  let mut out := #[]
  for f in ← dir.readDir do
    let id? := (suffixes.find? (f.fileName.endsWith ·)).map fun sfx =>
      (f.fileName.dropEnd sfx.length).toString
    unless id?.any known do out := out.push s!"{f.path}: pinned for no known {what}"
  return out

/-- The pin files that the verdicts of `verdictFile` need, in `dir`: each `known` id has a file
`<id><suffix>` for each of `suffixes`, and no other file is there. The messages name what a pin is
for (`what`) and the test (`test`) whose update writes the pins. -/
def pinFailures (test what : String) (verdictFile dir : System.FilePath) (suffixes : List String) :
    IO (Array String) := do
  let known := (← TraceSource.readPinned verdictFile).filterMap fun e =>
    match e.verdict with | .known _ => some e.path | _ => none
  let mut out := #[]
  for id in known do
    for sfx in suffixes do
      unless ← (dir / s!"{id}{sfx}").pathExists do
        out := out.push s!"{id}: missing {dir / s!"{id}{sfx}"}; run {test} with SEM_UPDATE=1"
  if ← dir.pathExists then out := out ++ (← stalePins dir suffixes known.contains what)
  return out

/-- The kind of a trace line where two runs first differ: a user call (`ev`), a step's marker
(`@op`, `@done`), another output line (a value, an exception, a skip), or a line after the output
(the outcome and the globals). -/
inductive LineKind where
  | event
  | marker
  | value
  | outcome
  deriving DecidableEq, Repr

/-- The kind of the output line `l`. -/
def lineKind (l : String) : LineKind :=
  if l.startsWith "ev " then .event else if l.startsWith "@" then .marker else .value

/-- Where two runs first differ: the step it is in (the last `@op <step>` line before it; `""`
before any step and after the output), the kind of line, and the two lines there: CPython's and
ours, each `none` past the end of its run's part. -/
structure FirstDiff where
  step : String
  kind : LineKind
  theirs : Option String
  ours : Option String
  deriving DecidableEq, Repr

/-- The lines of `s`, without the empty line after a final newline. -/
private def linesOf (s : String) : List String :=
  if s.isEmpty then [] else ((if s.endsWith "\n" then (s.dropEnd 1).toString else s).splitOn "\n")

/-- The step of the output lines `ls`: the last `@op <step>` among them, or `""`. -/
def stepOf (ls : List String) : String :=
  match ls.reverse.find? (·.startsWith "@op ") with
  | some l => (l.drop 4).toString
  | none => ""

/-- The index of the first line where `a` and `b` differ, and their lines there. -/
private def firstApart (a b : List String) : Nat × Option String × Option String :=
  let n := ((a.zip b).takeWhile fun (x, y) => x == y).length
  (n, a[n]?, b[n]?)

/-- Where our run first differs from CPython's: in the outputs `ours` and `theirs`, or, when they
are equal, in the sections after them, `oursRest` and `theirsRest`, compared line by line (with
an empty step and the kind `outcome`). The line kind is that of CPython's line, or of ours past the
end of CPython's output. -/
def firstDiff (ours theirs : String) (oursRest theirsRest : String := "") : FirstDiff :=
  let a := linesOf ours
  let b := linesOf theirs
  match firstApart a b with
  | (_, none, none) =>
    let (_, x, y) := firstApart (linesOf oursRest) (linesOf theirsRest)
    ⟨"", .outcome, y, x⟩
  | (n, x, y) => ⟨stepOf (b.take n), lineKind ((y <|> x).getD ""), y, x⟩

/-- How a run fails against CPython's trace: the gap is a model invariant; the run has a fault; it
is out of fuel; it differs before its gap; it differs and ends without a gap; or its trace has no
output section. Each kind says where it is: the step our run stopped in for the first three, the
place of the first difference (`FirstDiff`) for the differences. So two bugs in different steps,
or with different lines, have different kinds. -/
inductive FailureKind where
  | invariant (step msg : String)
  | fault (step line : String)
  | fuel (step : String)
  | beforeGap (place : FirstDiff)
  | differs (place : FirstDiff)
  | noOutput
  deriving DecidableEq, Repr

/-- The line kind in words. -/
def LineKind.render : LineKind → String
  | .event => "a user call"
  | .marker => "a step's marker"
  | .value => "a value or an exception"
  | .outcome => "the outcome or the globals"

/-- " in step <step>", or nothing for no step. -/
private def inStep (step : String) : String := if step.isEmpty then "" else s!" in step {step}"

/-- The place of a difference in words. -/
def FirstDiff.render (d : FirstDiff) : String := s!"first at {d.kind.render}{inStep d.step}"

/-- The failure kind in words. -/
def FailureKind.render : FailureKind → String
  | .invariant st m => s!"the model invariant \"{m}\"{inStep st}"
  | .fault st l => s!"the fault \"{l}\"{inStep st}"
  | .fuel st => s!"out of fuel{inStep st}"
  | .beforeGap d => s!"a difference before the gap, {d.render}"
  | .differs d => s!"a difference, {d.render}"
  | .noOutput => "a trace without its output section"

/-- How our run `ours` fails against CPython's trace `theirs`, computed from the traces and not
from the judge's message. `none` when the run agrees, when it gaps after agreeing, when CPython's
trace is no plain run (its run doesn't end, it doesn't compile, or it is two runs) unless our run
breaks a model invariant or has a fault, and when the program is rejected. A failure against a trace that is no plain run is the judge's to report; the
fuzz test reports such traces as generator bugs anyway. -/
def failureKind? (ours : SemDiff.Ours) (theirs : String) : Option FailureKind := do
  let .trace t := ours | none
  let some (o, r) := SemDiff.splitOutput t | some .noOutput
  let step := stepOf (linesOf o)
  if let some m := (SemDiff.gapOf t).filter StrataPython.Dyn.Sem.isModelInvariant then
    return .invariant step m
  if let some l := SemDiff.faultOf t then return .fault step l
  if theirs == SemDiff.endlessTrace || theirs == SemDiff.syntaxTrace ||
    theirs.startsWith SemDiff.twoRunsHeader then none
  if ((r.splitOn "\n").contains "--- out of fuel") then return .fuel step
  let (o', rest') ← SemDiff.splitOutput theirs
  match SemDiff.splitGap t with
  | some (out, before, _) =>
    if SemDiff.agreesBeforeTrace out before theirs then none
    else return .beforeGap (firstDiff out o' before rest')
  | none =>
    -- As in `SemDiff.judge`: against a cut trace, only the first `n` characters of the outputs.
    match SemDiff.splitTeardown theirs with
    | some (n, theirs') =>
      let (o'', rest'') ← SemDiff.splitOutput theirs'
      if o.take n == o''.take n && r == rest'' then none
      else return .differs (firstDiff (o.take n).toString (o''.take n).toString r rest'')
    | none =>
      if t == theirs then none
      else return .differs (firstDiff o o' r rest')

/-- Why a fuzz program fails the test: it tests nothing (a generator bug), or its run is wrong. -/
inductive FuzzFail where
  | bug (msg : String)
  | wrong (msg : String)
  deriving DecidableEq, Repr

/-- The message of a failure. -/
def FuzzFail.msg : FuzzFail → String
  | .bug m => m
  | .wrong m => m

/-- The verdict of the fuzz program `p` from CPython's `traces` (one per seed of `seeds` for the
seed bucket, else at least seed 0's) and our run, with `known` its pinned difference; or why it
fails. A generator bug comes first (`fuzzBug?`; traces whose agreement doesn't fit the bucket);
then a pinned run that gaps after its difference (`knownGap?`); then `judgeSeedDependent` for the
seed bucket and the judge for the others. -/
def fuzzVerdict (p : FuzzProgram) (traces : Array String) (ours : SemDiff.Ours)
    (known : Option Diff.Known) : Except FuzzFail Verdict := do
  let some t0 := traces[0]? | throw (.bug s!"{p.id}: no CPython trace")
  if let some b := fuzzBug? p t0 ours then throw (.bug b)
  if p.seedBucket && seedsAgree traces then
    throw (.bug s!"{p.id}: generator bug: its seed-dependent step shows the same order under every seed")
  if !p.seedBucket && !seedsAgree traces then
    throw (.bug s!"{p.id}: generator bug: CPython's trace depends on the hash seed or the machine")
  if let some k := known then
    if let some v := knownGap? p.id p.seedBucket ours traces k then
      return ← v.mapError .wrong
  let v := if p.seedBucket then judgeSeedDependent p.id ours traces else SemDiff.judge p.id ours t0 known
  v.mapError .wrong

/-- How the fuzz program `p` fails, with the index in `traces` of the first CPython trace against
which our run has a failure kind. `none` when `fuzzVerdict` accepts the run or finds a generator
bug, so that a shrink never keeps a program that tests nothing; also when the run fails, but
against no single trace. -/
def fuzzFailure? (p : FuzzProgram) (traces : Array String) (ours : SemDiff.Ours) :
    Option (FailureKind × Nat) :=
  match fuzzVerdict p traces ours none with
  | .ok _ | .error (.bug _) => none
  | .error (.wrong _) =>
    ((List.range traces.size).filterMap fun i => (failureKind? ours traces[i]!).map (·, i)).head?

/-- Whether a shrunk program still shows the original failure `kind` when it runs again, from its
failure on that run (`rerun`, as `fuzzFailure?` gives it): the index of the CPython trace that
shows it, or why no repro may be written. A flaky failure, or one that changed its kind, has no
repro. -/
def reproSeed? (kind : FailureKind) (rerun : Option (FailureKind × Nat)) : Except String Nat :=
  match rerun with
  | some (k, seed) =>
    if k == kind then .ok seed
    else .error s!"the shrunk program fails differently when it runs again: {k.render}"
  | none => .error "the shrunk program no longer fails when it runs again"

end StrataPython.AxisSource
