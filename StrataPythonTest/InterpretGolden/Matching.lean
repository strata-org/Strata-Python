/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPythonTest.Util.GoldenText

/-! # Shared failure-to-pattern helpers for the interpret goldens

The read side (`StrataPythonTest.InterpretGolden.Generate`, which each generated
child runs) and the write side (`Scripts.pyInterpretUpdate`, which regenerates the
`.expected` patterns) must agree on how an interpreter failure is reduced to its one
naming line and how a stored pattern is matched against output: the write side
derives and stores a pattern using these functions, and the read side re-checks the
committed pattern with them, so a divergence between two copies would let the update
tool emit a pattern the test then rejects. They must also agree on how a case is
compiled and run before matching — the dialect, the timeout and the `--v2` flag — so
that pipeline (`compileAndRun`) lives here too. These are the single definition both
sides import. -/

namespace StrataPython.InterpretGolden

-- `hasSub` and `rstripNewlines` are shared with the analyze goldens; opened here so
-- the suite and its write side keep referring to them unqualified.
open StrataPython.GoldenText

/-- Collapse every run of whitespace (newlines included) to a single space, so a
    diagnostic a host wrapped or indented differently matches a single-line pattern. -/
public def collapseWs (s : String) : String := Id.run do
  let mut out := ""
  let mut prevSpace := false
  for c in s.toList do
    if c.isWhitespace then
      unless prevSpace do out := out.push ' '
      prevSpace := true
    else
      out := out.push c
      prevSpace := false
  return out

/-- The one line of a failure that names it. Every shape the interpreter produces
    puts that line first and any elaboration (the indented `AST:` dump, the CLI's
    `Run strata --help` hint, blank lines, Lean runtime backtraces) after it, so
    this drops those and takes the head, then strips the leading `Exception: ` the
    CLI framework adds. Taking the tail instead would yield a leaf of the AST dump,
    which names nothing and moves with unrelated pretty-printer changes. -/
public def failureReason (output : String) : String :=
  let kept := (output.splitOn "\n").filter fun ln =>
    !(ln.isEmpty
      || hasSub ln "backtrace:"
      || ln.startsWith "trace:"
      || ln.endsWith "for additional help."
      || (!ln.isEmpty && ln.front.isWhitespace)
      || ln.startsWith "AST:")
  match kept.head? with
  | some first =>
    match first.dropPrefix? "Exception: " with
    | some ss => ss.toString
    | none => first
  | none => ""

/-- Does `text` match the extended-regex `pattern`? The pattern comes straight from
    an `.expected` file, so matching is delegated to `grep -qE` rather than
    reimplementing ERE. The text is handed over as a temp file instead of on stdin to
    keep large interpreter dumps off the pipe. -/
public def grepE (pattern text : String) : IO Bool := do
  IO.FS.withTempDir fun dir => do
    let f := dir / "grep-input"
    IO.FS.writeFile f text
    let o ← IO.Process.output {
      cmd := "grep", args := #["-qE", "-e", pattern, f.toString]
    }
    return o.exitCode == 0

/-- Match `output` against `pattern`, then (on a miss) retry against `collapseWs
    output`. The retry is additive: it can only turn a mismatch into a match. -/
public def matchesPattern (pattern output : String) : IO Bool := do
  if ← grepE pattern output then return true
  grepE pattern (collapseWs output)

/-- Did `py_to_strata` fail because Python could not parse the file? `strata_python.gen`
    reports a `SyntaxError` from the parser as `Parse failure:`; one raised elsewhere
    surfaces as a traceback naming `SyntaxError`. -/
private def isSyntaxError (out : String) : Bool :=
  hasSub out "Parse failure:" || hasSub out "SyntaxError"

/-- The message for a case `py_to_strata` could not lower, from its combined output and
    the minor version of the Python 3 that ran it (`none` when it could not be read).
    It always opens with `py_to_strata failed to lower the case to Ion` and always
    describes a failure: no cause makes the case pass. A missing module is named as a
    setup problem, since it fails every case alike. A syntax error under a Python older
    than 3.12 is named as a possible version problem, since some corpus cases use 3.12
    syntax. Everything else, including any syntax error under 3.12 or later, points at
    the front end. -/
public def loweringFailureMessage (stem python : String) (minor : Option Nat)
    (out : String) : String :=
  let interp := match minor with
    | some m => s!"{python} (Python 3.{m})"
    | none => s!"{python} (version unknown)"
  let cause :=
    if hasSub out "ModuleNotFoundError" then
      "the Python environment lacks a module py_to_strata needs; this is a setup \
       problem, not a front-end regression"
    else if isSyntaxError out && minor.any (· < 12) then
      "Python could not parse the file; this case may need Python 3.12 or later"
    else
      s!"fix the front end, or add {stem}.skip with the reason if the case is not \
         meant to run"
  s!"py_to_strata failed to lower the case to Ion with {interp}: {cause}"

/-- The minor version of the Python 3 that `python` runs, or `none` if it cannot be
    read. -/
private def pythonMinor (python : String) : IO (Option Nat) := do
  let o ← IO.Process.output {
    cmd := python, args := #["-c", "import sys; print(sys.version_info.minor)"]
    inheritEnv := true
  }
  return if o.exitCode == 0 then o.stdout.trimAscii.toString.toNat? else none

/-- Compile `tests/<stem>.py` to Ion in a private temp dir and run `pyInterpret` on
    it; return its exit code and combined output. When the Python front end cannot
    lower the file to Ion, return `loweringFailureMessage` followed by the compiler's
    combined output as the error instead, so the caller fails the case: a lowering regression must not pass silently, and a
    case that is meant not to run carries a `.skip` sidecar, which callers check before
    calling this. A corpus `.py` that is absent entirely throws (a stale committed
    child). Each case compiles into its own temp dir, so callers
    share no scratch and stay parallel. `INTERPRET_TIMEOUT` (default 60s) bounds the
    run with `timeout`; a timeout (exit 124) yields a stable one-line output. `--fuel`
    bounds execution steps but not translation, so the wall-clock bound is what keeps a
    non-terminating case from hanging CI. The interpreter echoes the scratch path it is
    handed, so the output is rewritten back to the canonical corpus path the `.expected`
    patterns embed. -/
public def compileAndRun (python : String) (root : System.FilePath) (stem : String)
    (v2 : Bool) : IO (Except String (UInt32 × String)) := do
  let canonical := s!"StrataPythonTest/tests/{stem}.python.st.ion"
  let timeoutStr := ((← IO.getEnv "INTERPRET_TIMEOUT").getD "60")
  let pyPath := root / "StrataPythonTest" / "tests" / (stem ++ ".py")
  -- A missing corpus file means a committed child names a `.py` that no longer
  -- exists; that calls for regenerating the children, not for a lowering diagnosis.
  unless ← pyPath.pathExists do
    throw <| IO.userError
      s!"interpret golden corpus file missing: {pyPath}; the child module for \"{stem}\" \
         references a test that is gone — regenerate the children (build once locally) \
         and commit the result"
  IO.FS.withTempDir fun scratch => do
    let ionAbs := scratch / (stem ++ ".python.st.ion")
    -- Compile Python → Ion. The dialect path is relative to `Python/strata-python`,
    -- so run there and pass the test and Ion paths absolute.
    let compile ← IO.Process.output {
      cmd := python
      args := #["-m", "strata_python.gen", "py_to_strata",
                "--dialect", "dialects/Python.dialect.st.ion",
                pyPath.toString,
                ionAbs.toString]
      cwd := some (root / "Python" / "strata-python").toString
      inheritEnv := true
    }
    if compile.exitCode != 0 then
      let out := compile.stdout ++ compile.stderr
      return .error s!"{loweringFailureMessage stem python (← pythonMinor python) out}\n{out}"
    let runOut ← IO.Process.output {
      cmd := "timeout"
      args := #[timeoutStr, (root / ".lake" / "build" / "bin" / "pyInterpret").toString]
                ++ (if v2 then #["--v2"] else #[]) ++ #[ionAbs.toString]
      cwd := some root.toString
      inheritEnv := true
    }
    let output :=
      if runOut.exitCode == 124 then s!"pyInterpret timed out after {timeoutStr}s"
      else (runOut.stdout ++ runOut.stderr).replace ionAbs.toString canonical
    return .ok (runOut.exitCode, output)

end StrataPython.InterpretGolden
