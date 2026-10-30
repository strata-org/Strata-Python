/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# Differential runs: the pinned verdicts

A front end runs each program of its corpus with its semantics and with the source language's own
implementation, and compares the two traces as text.  The result for each program is a *verdict*:
the traces agree, the semantics stopped with a gap, the difference is known and documented, or the
translator rejected the program with a syntax error.  The verdicts are pinned in a file, one line
per program, sorted by path:

```
<path> | agree
<path> | gap | <the gap's message>
<path> | known | <reason>
<path> | syntax
```

A test compares the verdicts of a run with the pinned ones and fails on any change; in update mode
it writes the new verdicts instead (`checkOrUpdate`).  This file is language neutral: it reads,
writes and compares verdicts.  Running programs is each front end's.  A `known` verdict holds only
for the semantics' own trace that the front end pins with it (`Known`), so that a change of that
run's output fails the test (`classify`).
-/

namespace Strata.Dyn.Exec.Diff

@[expose] public section

/-- What a differential run found for one program. -/
inductive Verdict where
  /-- The two traces are equal. -/
  | agree
  /-- The semantics stopped with a gap, with this message. -/
  | gap (msg : String)
  /-- A documented difference, with the reason. -/
  | known (reason : String)
  /-- The translator rejects the program with a syntax error, as the source implementation does. -/
  | syntax
  deriving DecidableEq, Repr, Inhabited

/-- One line of a verdict file: a program's path and its verdict. -/
structure Entry where
  path : String
  verdict : Verdict
  deriving DecidableEq, Repr, Inhabited

/-- A message on one line: a backslash becomes `\\` and a newline `\n`. -/
def escape (msg : String) : String :=
  msg.foldl (fun acc ch => match ch with
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | ch => acc.push ch) ""

/-- The message that `escape` wrote. -/
def unescape (msg : String) : String :=
  let rec go : List Char → String → String
    | '\\' :: 'n' :: rest, acc => go rest (acc.push '\n')
    | '\\' :: '\\' :: rest, acc => go rest (acc.push '\\')
    | ch :: rest, acc => go rest (acc.push ch)
    | [], acc => acc
  go msg.toList ""

/-- The text of an entry, as one line of a verdict file. -/
def Entry.render (e : Entry) : String :=
  match e.verdict with
  | .agree => s!"{e.path} | agree"
  | .gap msg => s!"{e.path} | gap | {escape msg}"
  | .known reason => s!"{e.path} | known | {escape reason}"
  | .syntax => s!"{e.path} | syntax"

/-- The entry of a line of a verdict file, or why the line is malformed.  The message or reason is
the rest of the line after the second separator, so it may itself contain ` | `; `unescape` gives
back its newlines. -/
def Entry.parse (line : String) : Except String Entry :=
  match line.splitOn " | " with
  | [path, "agree"] => .ok ⟨path, .agree⟩
  | [path, "syntax"] => .ok ⟨path, .syntax⟩
  | path :: "gap" :: msg@(_ :: _) => .ok ⟨path, .gap (unescape (" | ".intercalate msg))⟩
  | path :: "known" :: reason@(_ :: _) => .ok ⟨path, .known (unescape (" | ".intercalate reason))⟩
  | _ => .error s!"malformed verdict line: {line}"

/-- The text of a verdict file: one line per entry, sorted by path, each ending in a newline. -/
def render (es : Array Entry) : String :=
  String.join ((es.qsort (fun a b => a.path < b.path)).toList.map (·.render ++ "\n"))

/-- The entries of a verdict file, or the first problem: a malformed line, two entries for one
path, or lines out of order.  Empty lines are ignored. -/
def parse (text : String) : Except String (Array Entry) := do
  let mut out : Array Entry := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let e ← Entry.parse line
    if let some prev := out.back? then
      if e.path == prev.path then throw s!"two verdicts for {e.path}"
      if !(prev.path < e.path) then throw s!"verdicts out of order at {e.path}"
    out := out.push e
  return out

/-- A change between the pinned verdicts and a run's: a program whose verdict changed, which is
new, or which the run no longer has. -/
inductive Change where
  | changed (path : String) (pinned now : Verdict)
  | added (e : Entry)
  | removed (e : Entry)
  deriving DecidableEq, Repr

/-- The text of a change, for a test's failure message. -/
def Change.render : Change → String
  | .changed p a b => s!"{p}: pinned {(Entry.mk p a).render}, now {(Entry.mk p b).render}"
  | .added e => s!"new: {e.render}"
  | .removed e => s!"gone: {e.render}"

/-- The changes from the pinned entries to a run's, by path. -/
def changes (pinned now : Array Entry) : Array Change :=
  let fromPinned := pinned.filterMap fun p =>
    match now.find? (·.path == p.path) with
    | some n => if n.verdict == p.verdict then none else some (.changed p.path p.verdict n.verdict)
    | none => some (.removed p)
  let added := now.filterMap fun n =>
    if pinned.any (·.path == n.path) then none else some (.added n)
  fromPinned ++ added

/-- Compares a run's verdicts with the ones pinned in the file `path` (none if it doesn't exist),
or, in update mode, writes the run's verdicts there.  Gives the changes (none in update mode), and
throws if the pinned file is malformed. -/
def checkOrUpdate (path : System.FilePath) (now : Array Entry) (update : Bool) :
    IO (Array Change) := do
  if update then
    IO.FS.writeFile path (render now)
    return #[]
  let text ← if ← path.pathExists then IO.FS.readFile path else pure ""
  match parse text with
  | .ok pinned => return changes pinned now
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- A documented difference of a program: its reason, and the semantics' own trace that is pinned
with it (`none` only while the pin is being written, to accept any trace). -/
structure Known where
  reason : String
  pinned : Option String
  deriving DecidableEq, Repr, Inhabited

/-- The verdict of a program from two traces that end without a gap: `agree` if they are equal,
and otherwise `known` if the difference is documented and the semantics' trace is the pinned one;
or why a test fails on it. -/
def classify (ours theirs : String) (known : Option Known) : Except String Verdict :=
  if ours == theirs then .ok .agree else
  match known with
  | some ⟨r, none⟩ => .ok (.known r)
  | some ⟨r, some pin⟩ =>
    if pin == ours then .ok (.known r) else .error "the run's trace differs from its pinned trace"
  | none => .error "the traces differ"

end

end Strata.Dyn.Exec.Diff
