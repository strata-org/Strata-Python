/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import StrataDyn.Exec.Diff
public meta import StrataPython.Dyn.Sem.Invariant

/-! # One program against CPython

The verdict of one Python program: its trace under the Python semantics (`pydyn run`, the
compiled binary) against CPython 3.12's (`StrataPythonTest/Dyn/trace.py`).  Each differential
test keeps its own CPython traces and its own verdict file (`Strata.Dyn.Exec.Diff`), and calls
`verdict` for each program.

CPython runs each program twice, with `PYTHONHASHSEED` 0 and 1 (`cpythonTrace`).  If the two
traces differ, CPython's text holds both, each after a line `--- PYTHONHASHSEED=N`, with every
address `0x…` replaced by `0x?`, and the semantics must stop with a gap on the program.

A run that stops with a gap must agree with CPython up to the gap: its output is the beginning of
CPython's, and if the gap comes after the output, the output and the sections before the gap are
CPython's.  So a gap can't hide a wrong output or a wrong exception before it.  A trace's header
`--- stdout <n>` gives the length of the output, so a line that the program prints is never taken
for a section's header.
-/

public meta section

namespace StrataPython.SemDiff

open Strata.Dyn.Exec

/-- The script that prints CPython's trace. -/
def traceScript : System.FilePath := "StrataPythonTest" / "Dyn" / "trace.py"

/-- The compiled `pydyn`. -/
def pydynPath : System.FilePath := ".lake" / "build" / "bin" / "pydyn"

/-- The header of CPython's first trace when its two runs differ. -/
def twoRunsHeader : String := "--- PYTHONHASHSEED=0\n"

/-- CPython's trace says that CPython does not compile the program. -/
def syntaxTrace : String := "--- syntax error\n"

/-- `text` with each address `0x` followed by hex digits replaced by `0x?`. -/
def maskAddresses (text : String) : String := Id.run do
  let cs := text.toList.toArray
  let mut out := ""
  let mut i := 0
  while h : i < cs.size do
    if cs[i] == '0' && cs[i + 1]? == some 'x' &&
        (cs[i + 2]?.map Char.isHexDigit).getD false then
      out := out ++ "0x?"
      i := i + 2
      while j : i < cs.size do
        if cs[i].isHexDigit then i := i + 1 else break
    else
      out := out.push cs[i]
      i := i + 1
  return out

/-- A trace's output, which its header `--- stdout <n>` says is `n` characters long, and the
sections after it; `none` for a trace that doesn't start with that header. -/
def splitOutput (trace : String) : Option (String × String) := do
  let header := (trace.splitOn "\n").head!
  let n ← (header.dropPrefix? "--- stdout ").bind (·.toString.toNat?)
  let body := (trace.drop (header.length + 1)).toString
  -- The output, then the newline that ends the section.
  pure ((body.take n).toString, (body.drop (n + 1)).toString)

/-- A trace whose output is `out`, followed by the sections `rest`. -/
def traceOf (out rest : String) : String := s!"--- stdout {out.length}\n{out}\n{rest}"

/-- `trace` with its addresses masked, its header giving the masked output's length. -/
def maskTrace (trace : String) : String :=
  match splitOutput trace with
  | some (out, rest) => traceOf (maskAddresses out) (maskAddresses rest)
  | none => maskAddresses trace

/-- CPython's text from its runs with `PYTHONHASHSEED` 0 and 1: the trace if they agree, else both
masked, each after a line `--- PYTHONHASHSEED=N`. -/
def joinRuns (t0 t1 : String) : String :=
  if t0 == t1 then t0
  else s!"{twoRunsHeader}{maskTrace t0}--- PYTHONHASHSEED=1\n{maskTrace t1}"

/-- CPython's text for `pyFile`: its trace, or both traces if its runs with `PYTHONHASHSEED` 0
and 1 differ. -/
def cpythonTrace (pythonCmd pyFile : System.FilePath) : IO String := do
  let traceWith (seed : String) : IO String := do
    let r ← IO.Process.output {
      cmd := pythonCmd.toString, args := #[traceScript.toString, pyFile.toString]
      env := #[("PYTHONHASHSEED", some seed)] }
    unless r.exitCode == 0 do
      throw <| .userError s!"{pyFile}: trace.py failed:\n{r.stderr}"
    return r.stdout
  let t0 ← traceWith "0"
  let t1 ← traceWith "1"
  return joinRuns t0 t1

/-- The sections of a trace after its output, before its first gap line, and the gap's message.
The search skips the output, so a line that the program printed is never taken for a gap. -/
def splitGap (trace : String) : Option (String × String × String) := do
  let (out, rest) ← splitOutput trace
  let lines := rest.splitOn "\n"
  let i ← lines.findIdx? (·.startsWith "--- gap ")
  pure (out, "\n".intercalate (lines.take i), ((lines[i]!).drop 8).toString)

/-- The message of the first gap of a trace. -/
def gapOf (trace : String) : Option String := (splitGap trace).map (·.2.2)

/-- The first line of a trace, after its output, that reports a fault other than a gap. -/
def faultOf (trace : String) : Option String := do
  let (_, rest) ← splitOutput trace
  (rest.splitOn "\n").find? (·.startsWith "--- fault ")

/-- Whether a run that stops with a gap agrees with CPython's trace `theirs` up to the gap: a gap
right after the output needs only a prefix of CPython's output, and a later gap the whole output
and the sections before it.  A gap in the outcome after the line `raised <ExcType>` needs CPython's
outcome to raise that type. -/
def agreesBefore (out before theirs : String) : Bool :=
  match splitOutput theirs with
  | none => false
  | some (out', rest') =>
    if before.isEmpty then out'.startsWith out
    -- A gap in the outcome after `raised <ExcType>`: CPython's line goes on with `: <str>`.  Only
    -- the line right after the outcome's header is that line; a global may start with "raised ".
    else if (match (before.splitOn "\n").reverse with
        | l :: "--- outcome" :: _ => l.startsWith "raised "
        | _ => false) then
      out == out' && rest'.startsWith (before ++ ": ")
    else out == out' && rest'.startsWith (before ++ "\n")

/-- What `pydyn run` gave. -/
inductive Ours where
  /-- The run's trace. -/
  | trace (text : String)
  /-- The translator reported a syntax error. -/
  | syntax
  /-- The translator rejected these constructs. -/
  | unsupported (constructs : List String)

/-- What the diagnostics that `pydyn run` printed when it rejected a program say: a syntax error,
or the constructs that the translator doesn't support; or why they say neither, which fails the
test: an internal error of the translator, or a line that is no diagnostic of either kind. -/
def readRejection (stdout : String) : Except String Ours := do
  let lines := (stdout.splitOn "\n").filter (!·.isEmpty)
  if let some l := lines.find? (·.startsWith "-- internal error: ") then
    throw s!"the translator reports an internal error: {l}"
  if lines.any (·.startsWith "-- syntax error: ") then return .syntax
  if lines.isEmpty then throw "the translator rejects the program with no diagnostic"
  -- Each line is `-- unsupported: <construct> is not supported at <range>`.
  let constructs ← lines.mapM fun l => match l.dropPrefix? "-- unsupported: " with
    | some rest => pure (rest.toString.splitOn " is not supported").head!
    | none => throw s!"the translator prints a line that is no diagnostic: {l}"
  return .unsupported constructs.eraseDups

/-- Run `pydyn run` on `pyFile`. -/
def runOurs (pyFile : System.FilePath) (pydyn : System.FilePath := pydynPath) : IO Ours := do
  let r ← IO.Process.output { cmd := pydyn.toString, args := #["run", pyFile.toString] }
  if r.exitCode == 0 then return .trace r.stdout
  unless r.exitCode == 1 do
    throw <| .userError s!"{pyFile}: pydyn run failed ({r.exitCode}):\n{r.stdout}{r.stderr}"
  match readRejection r.stdout with
  | .ok o => return o
  | .error e => throw <| .userError s!"{pyFile}: {e}"

/-- The verdict of the program `name` from what `pydyn run` gave and CPython's text `theirs`
(`cpythonTrace`), with `known` its documented difference; or the reason the test fails on it.  A
documented difference holds only for the run's pinned trace. -/
def judge (name : String) (ours : Ours) (theirs : String) (known : Option Diff.Known) :
    Except String Diff.Verdict :=
  match ours with
  | .syntax =>
    if theirs == syntaxTrace then .ok .syntax
    else .error s!"{name}: the translator reports a syntax error, but CPython compiles it"
  | .unsupported cs =>
    if theirs == syntaxTrace then
      .error s!"{name}: CPython reports a syntax error, but the translator only rejects \
        {", ".intercalate cs}"
    else .ok (.gap s!"the translator does not support {", ".intercalate cs}")
  | .trace ours =>
    let twoRuns := theirs.startsWith twoRunsHeader
    if theirs == syntaxTrace then
      .error s!"{name}: CPython reports a syntax error, but the program runs"
    else if (splitOutput ours).isNone then
      .error s!"{name}: the run's trace has no output section"
    else if ((splitOutput ours).map (·.2.splitOn "\n")).any (·.contains "--- out of fuel") then
      .error s!"{name}: the run is out of fuel"
    else if let some msg := (gapOf ours).filter StrataPython.Dyn.Sem.isModelInvariant then
      -- A precondition of the model itself doesn't hold: a bug in the model, never an allowed gap.
      .error s!"{name}: the run breaks a model invariant: {msg}"
    else if let some line := faultOf ours then
      -- A fault other than a gap is a wrong ending, after which ref-to-reg keeps nothing: it is a
      -- bug, whatever the verdict file says.
      .error s!"{name}: the run ends with a fault: {line}"
    else if let some (out, before, msg) := splitGap ours then
      -- Up to the gap, our trace is CPython's.  With two different runs, it is either run's.
      let runs := if twoRuns then
          ((theirs.drop twoRunsHeader.length).toString.splitOn "--- PYTHONHASHSEED=1\n")
        else [theirs]
      if runs.any (agreesBefore out before) then .ok (.gap msg)
      else .error s!"{name}: the run differs from CPython's before its gap\n--- ours\n{ours}\
        --- CPython\n{theirs}"
    else if twoRuns then
      .error s!"{name}: CPython's two runs differ, but the run doesn't stop with a gap"
    else match Diff.classify ours theirs known with
      | .ok v => .ok v
      | .error e => .error s!"{name}: {e}\n--- ours\n{ours}--- CPython\n{theirs}"

/-- The verdict of the program `pyFile`, named `name`, against CPython's text `theirs`
(`cpythonTrace`), with `known` its documented difference (`judge`); or the reason the test fails
on it. -/
def verdict (name : String) (pyFile : System.FilePath) (theirs : String) (known : Option Diff.Known)
    (pydyn : System.FilePath := pydynPath) : IO (Except String Diff.Verdict) :=
  return judge name (← runOurs pyFile pydyn) theirs known

end StrataPython.SemDiff
