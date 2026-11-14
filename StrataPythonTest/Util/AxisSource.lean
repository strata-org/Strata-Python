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
each case expects of CPython. Its build test runs every program with CPython 3.12 and with the
Python semantics, and judges each pair with `SemDiff.judge`. This module holds what the test
needs besides the judge:

* the *generator-bug checks*: a case whose CPython run doesn't run its operation, or doesn't end
  the way the case expects, tests nothing, so the test fails on it instead of pinning a verdict
  (`generatorBug?`);
* CPython's trace under one hash seed, and the check that the eight traces under the seeds 0 to
  7 are equal (`cpythonTraceSeed`, `seedsAgree`);
* the summary of the verdicts by group and axis (`summary`);
* the coverage check (`coverage`): every name of the model's tables is covered by a case that
  agrees with CPython, by observed evidence (a call in CPython's run, an instruction of the
  operation's translation) or by a declared entry of the catalog, or `not_covered.txt` lists it.

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
    match SemDiff.splitOutput theirs with
    | none => bug "CPython's trace has no output section"
    | some (out, rest) =>
      if !rest.startsWith "--- outcome\nok\n" then bug "CPython's run doesn't end with `ok`"
      else match caseOutcome c.id out, expect with
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

/-- The coverage check, for the model's names `required` (its tables), the cases' evidence `evs`
and the entries `nc` of `not_covered.txt`. -/
def coverage (required : Array String) (evs : Array Evidence) (nc : Array NotCovered) :
    Coverage := Id.run do
  let mut fails : Array String := #[]
  let req : Std.HashSet String := required.foldl (·.insert ·) {}
  let mut observed : Std.HashSet String := {}
  -- For each name and each cell that a declared entry covers: the cases that declare it.
  let mut byEntries : Std.HashMap String (Array String) := {}
  let mut observedCells : Std.HashSet (String × String) := {}
  let mut entryCells : Std.HashMap (String × String) (Array String) := {}
  let mut declared : Std.HashSet (String × String) := {}
  let mut declaredList : Array (String × String) := #[]
  for ev in evs do
    let c := ev.case
    for n in c.calls ++ c.entries do
      unless declared.contains (n, c.axis) do
        declared := declared.insert (n, c.axis)
        declaredList := declaredList.push (n, c.axis)
    unless ev.counted do continue
    if ev.result then
      for n in c.calls do
        unless ev.called.contains n do
          fails := fails.push s!"{c.id}: the case calls {n} by name, but CPython's run doesn't show it"
    for n in c.entries do
      unless req.contains n do
        fails := fails.push s!"{c.id}: the catalog says the case reaches {n}, which no table of \
          the model has"
    let insns := ev.insns.filter (!neverRuns.contains ·)
    if ev.result then
      for n in ev.called ++ insns do observed := observed.insert n
      for n in c.entries do byEntries := byEntries.insert n ((byEntries.getD n #[]).push c.id)
    if ev.cells then
      for n in ev.called ++ insns do observedCells := observedCells.insert (n, c.axis)
      for n in c.entries do
        entryCells := entryCells.insert (n, c.axis) ((entryCells.getD (n, c.axis) #[]).push c.id)
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
  for (n, a) in declaredList do
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

end StrataPython.AxisSource
