/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import StrataPythonTest.Util.TraceSource
public meta import StrataPythonTest.Util.Python
public meta import Std.Data.HashMap

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
* the summary of the verdicts by group and axis (`summary`).

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

/-- One case of a generated source: its id, its group and axis (for the summary), and what it
expects of CPython. -/
structure Case where
  id : String
  group : String
  axis : String
  expect : Expect
  deriving Repr, Inhabited

/-- The cases that `grid.py` printed, one `<id> | <group> | <axis> | <expectation>` per line. -/
def parseCases (text : String) : Except String (Array Case) := do
  let mut out := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn " | " with
    | [id, group, axis, e] => out := out.push ⟨id, group, axis, ← Expect.parse e⟩
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

end StrataPython.AxisSource
