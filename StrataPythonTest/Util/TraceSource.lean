/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import StrataPythonTest.Util.SemDiff

/-! # Differential sources of programs

Helpers for the differential sources, which compare the Python semantics with CPython on many
programs. Each source judges its programs with `SemDiff.verdict` and pins the verdicts of its
programs in one verdict file (`Strata.Dyn.Exec.Diff`). Two of them also keep CPython's text for each
program (`SemDiff.cpythonTrace`) in one checked-in traces file; `runSource` checks every program
against both files, or, in update mode, writes both files again.

A traces file starts with the text of `SemDiff.traceScript`, so that a change to the trace script
makes the checked-in traces fail instead of being compared with traces in an old format. Then it
holds, for each program in order, a line `=== <id> <p> <t>`, the program's text (`p` characters)
and CPython's text for it (`t` characters). The check compares the program's text too, so a
program that changed without a new trace fails. CPython's text names the interpreter's own
directories as `<python>`, so that a traces file doesn't depend on where CPython is installed.
-/

public meta section

namespace StrataPython.TraceSource

open Strata.Dyn.Exec
open Strata.Dyn.Exec.Diff (Entry Verdict)

/-- One record of a traces file: its id, the program's text and CPython's text for it. -/
structure Record where
  id : String
  program : String
  trace : String
  deriving Inhabited, BEq, Repr

/-- The id of the record that holds the trace script's text. -/
def scriptId : String := "#trace.py"

/-- The text of a traces file for the records `rs`. -/
def renderTraces (rs : Array Record) : String :=
  rs.foldl (fun acc r => acc ++ s!"=== {r.id} {r.program.length} {r.trace.length}\n" ++ r.program ++
    r.trace) ""

/-- The records of a traces file, or the first malformed header or truncated record. -/
def parseTraces (text : String) : Except String (Array Record) := do
  let mut out : Array Record := #[]
  let mut rest := text.toList
  while !rest.isEmpty do
    let line := rest.takeWhile (· != '\n')
    rest := rest.drop (line.length + 1)
    match (String.ofList line).splitOn " " with
    | ["===", id, p, t] =>
      let (some p, some t) := (p.toNat?, t.toNat?)
        | throw s!"malformed header: {String.ofList line}"
      let prog := rest.take p
      let tr := (rest.drop p).take t
      if prog.length + tr.length < p + t then throw s!"{id}: the file ends inside its record"
      out := out.push ⟨id, String.ofList prog, String.ofList tr⟩
      rest := rest.drop (p + t)
    | _ => throw s!"malformed header: {String.ofList line}"
  return out

/-- Run `f` on each item, with at most `workers` running at once, and keep the results in order.
Each worker takes the next item as soon as it is free. The workers are dedicated threads, since
they mostly wait on subprocesses. -/
def mapBounded {α β : Type} [Inhabited β] (workers : Nat) (xs : Array α) (f : α → IO β) :
    IO (Array β) := do
  let next ← IO.mkRef 0
  let out ← IO.mkRef (Array.replicate xs.size (default : β))
  let worker : IO Unit := do
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if h : i < xs.size then
        let y ← f xs[i]
        out.modify (·.setIfInBounds i y)
      else break
  let tasks ← (List.range (max workers 1)).mapM fun _ => IO.asTask worker (prio := .dedicated)
  for t in tasks do
    IO.ofExcept (← IO.wait t)
  out.get

/-- The directories of `pythonCmd`'s installation: its prefix and its base prefix, each as CPython
names it and with its links resolved. A directory shorter than two characters (such as `/`) would
mask unrelated paths, so it is an error. -/
def interpreterDirs (pythonCmd : System.FilePath) : IO (List String) := do
  let r ← IO.Process.output { cmd := pythonCmd.toString, args := #["-c",
    "import os, sys\nfor p in (sys.prefix, sys.base_prefix): print(p); print(os.path.realpath(p))"] }
  unless r.exitCode == 0 do
    throw <| .userError s!"{pythonCmd} failed:\n{r.stderr}"
  let dirs := (r.stdout.splitOn "\n").filter (!·.isEmpty)
  if dirs.isEmpty then throw <| .userError s!"{pythonCmd} names no installation directory"
  if let some d := dirs.find? (·.length < 2) then
    throw <| .userError s!"{pythonCmd}: its installation directory {d} is too short to mask"
  return dirs

/-- Whether `text` contains `part`. -/
private def mentions (text part : String) : Bool := (text.splitOn part).length > 1

/-- CPython's text `trace` with each directory of `dirs` written as `<python>` wherever a `/`
follows it, as at the start of a path (`<dir>/...`); an empty directory names nothing. The longer directories go first, since one directory's text may contain another's
(a link's target can end with the link's own path). A trace's header then gives its masked
output's length. These are errors, so that a recorded `<python>` always comes from the mask:
- a text that already holds `<python>`;
- a text that names a directory other than at the start of a path, which the mask leaves alone;
- the text of two runs that differ and name a directory, since the program can print the line
  that separates the runs, so the second run's header can't be found for sure. -/
def maskInterpreter (dirs : List String) (trace : String) : Except String String := do
  let dirs := (dirs.filter (!·.isEmpty)).mergeSort (·.length ≥ ·.length)
  if mentions trace "<python>" then throw "CPython's text already holds <python>"
  if !dirs.any (mentions trace) then return trace
  if trace.startsWith SemDiff.twoRunsHeader then
    throw "CPython's two runs differ and name the interpreter's directory"
  let mask (s : String) := dirs.foldl (fun t d => t.replace (d ++ "/") "<python>/") s
  let masked := match SemDiff.splitOutput trace with
    | some (out, rest) => SemDiff.traceOf (mask out) (mask rest)
    | none => mask trace
  if dirs.any (mentions masked) then
    throw "CPython's text names the interpreter's directory other than at the start of a path"
  return masked

/-- A recorded trace with `<python>` written as the directory `dir` again, for the comparison with
the semantics' run. The semantics can't know where CPython is installed, so a run that prints
`<python>` itself never agrees with a path that CPython printed. -/
def unmaskInterpreter (dir trace : String) : Except String String := do
  if !mentions trace "<python>" then return trace
  if trace.startsWith SemDiff.twoRunsHeader then
    throw "a recorded text of two runs holds <python>"
  return match SemDiff.splitOutput trace with
    | some (out, rest) => SemDiff.traceOf (out.replace "<python>" dir) (rest.replace "<python>" dir)
    | none => trace.replace "<python>" dir

/-- The user's home directory, as `HOME` names it and with its links resolved; none if `HOME` is
unset or shorter than two characters. -/
def homeDirs : IO (List String) := do
  let some home ← IO.getEnv "HOME" | return []
  if home.length < 2 then return []
  let real ← try pure (← IO.FS.realPath home).toString catch _ => pure home
  return [home, real]

/-- The ids that a script prints, one per line, after it wrote the programs into `dir`. -/
def programsOf (pythonCmd script : System.FilePath) (args : Array String) : IO (Array String) := do
  let r ← IO.Process.output { cmd := pythonCmd.toString, args := #[script.toString] ++ args }
  unless r.exitCode == 0 do
    throw <| .userError s!"{script} failed:\n{r.stderr}"
  return ((r.stdout.splitOn "\n").filter (!·.isEmpty)).toArray

/-- The verdicts pinned in `verdictFile`, or none if it doesn't exist. -/
def readPinned (verdictFile : System.FilePath) : IO (Array Entry) := do
  if ← verdictFile.pathExists then
    match Diff.parse (← IO.FS.readFile verdictFile) with
    | .ok es => return es
    | .error e => throw <| .userError s!"{verdictFile}: {e}"
  else return #[]

/-- The verdict of each program `(id, file, CPython's text)`, and the failure messages. A `known`
verdict holds only with a pinned trace of the semantics' run (`Diff.Known`), and these sources
keep none. So a program whose pinned verdict is `known` fails. -/
def judgeAll (workers : Nat) (pinned : Array Entry)
    (programs : Array (String × System.FilePath × String)) : IO (Array Entry × Array String) := do
  let results ← mapBounded workers programs fun (id, file, theirs) => do
    if pinned.any fun e => e.path == id && e.verdict matches .known _ then
      return (id, .error s!"{id}: a known verdict needs a pinned trace of the semantics' run, which \
        this source doesn't keep")
    return (id, ← SemDiff.verdict id file theirs none)
  let mut now : Array Entry := #[]
  let mut failures : Array String := #[]
  for (id, r) in results do
    match r with
    | .ok v => now := now.push ⟨id, v⟩
    | .error msg => failures := failures.push msg
  return (now, failures)

/-- Print the summary line of a source, headed by `title`, and its failures; throw if there are
any. `extra` is added to the summary line. -/
def report (title : String) (now : Array Entry) (total : Nat) (failures : Array String)
    (extra : String := "") : IO Unit := do
  let count (p : Verdict → Bool) := (now.filter (p ·.verdict)).size
  IO.println s!"{title}: {count (· == .agree)} agree, \
    {count (fun | .gap _ => true | _ => false)} gap, {count (fun | .known _ => true | _ => false)} \
    known, {count (· == .syntax)} syntax, of {total}{extra}"
  unless failures.isEmpty do
    for f in failures do IO.println f
    throw <| .userError s!"{title}: {failures.size} failure(s)"

/-- Check the programs `ids` in `dir` (`dir/<id>.py`) against the CPython texts of
`tracesFile` and the verdicts of `verdictFile`; in update mode, compute CPython's texts with
`pythonCmd`, masked by `maskInterpreter`, and write both files. CPython's texts are unmasked
by `unmaskInterpreter` before the comparison. It prints a summary line headed by `title`, and throws if a
program fails. -/
def runSource (title : String) (pythonCmd dir tracesFile verdictFile : System.FilePath)
    (ids : Array String) (update : Bool) (workers : Nat := 8) : IO Unit := do
  unless ← SemDiff.pydynPath.pathExists do
    throw <| .userError s!"{SemDiff.pydynPath} is missing: build it with `lake build pydyn`"
  let file (id : String) := dir / s!"{id}.py"
  let script ← IO.FS.readFile SemDiff.traceScript
  let dirs ← interpreterDirs pythonCmd
  let traces ← if update then do
      let home ← homeDirs
      let rs ← mapBounded workers ids fun id => do
        match maskInterpreter dirs (← SemDiff.cpythonTrace pythonCmd (file id)) with
        | .ok trace =>
          if let some h := home.find? (mentions trace) then
            throw <| .userError s!"{id}: CPython's text names the home directory {h}"
          return (⟨id, ← IO.FS.readFile (file id), trace⟩ : Record)
        | .error e => throw <| .userError s!"{id}: {e}"
      IO.FS.writeFile tracesFile (renderTraces (#[⟨scriptId, script, ""⟩] ++ rs))
      pure rs
    else match parseTraces (← IO.FS.readFile tracesFile) with
      | .ok rs =>
        unless rs[0]? == some ⟨scriptId, script, ""⟩ do
          throw <| .userError s!"{tracesFile}: {SemDiff.traceScript} changed since the traces \
            were written; run with SEM_UPDATE=1"
        pure (rs.extract 1)
      | .error e => throw <| .userError s!"{tracesFile}: {e}"
  if traces.map (·.id) != ids then
    throw <| .userError s!"{tracesFile}: its programs are not the source's programs; run with \
      SEM_UPDATE=1"
  for r in traces do
    unless (← IO.FS.readFile (file r.id)) == r.program do
      throw <| .userError s!"{tracesFile}: the program {r.id} changed since its CPython trace was \
        written; run with SEM_UPDATE=1"
  let real := dirs.headD ""
  let theirs ← traces.mapM fun r => match unmaskInterpreter real r.trace with
    | .ok trace => pure (r.id, file r.id, trace)
    | .error e => throw <| .userError s!"{tracesFile}: {r.id}: {e}"
  let pinned ← readPinned verdictFile
  let (now, failures) ← judgeAll workers pinned theirs
  let mut failures := failures
  if failures.isEmpty then
    for c in ← Diff.checkOrUpdate verdictFile now update do
      failures := failures.push c.render
  report title now ids.size failures

end StrataPython.TraceSource
