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

/-- Compile `tests/<stem>.py` to Ion in a private temp dir and run `pyInterpret` on
    it; return its combined output and exit code, or `none` when the Python front end
    cannot lower a present file to Ion (a parse failure, a silent skip). A corpus
    `.py` that is absent entirely throws instead — that is a stale committed child,
    not a skip. Each case compiles into its own temp dir, so callers
    share no scratch and stay parallel. `INTERPRET_TIMEOUT` (default 60s) bounds the
    run with `timeout`; a timeout (exit 124) yields a stable one-line output. `--fuel`
    bounds execution steps but not translation, so the wall-clock bound is what keeps a
    non-terminating case from hanging CI. The interpreter echoes the scratch path it is
    handed, so the output is rewritten back to the canonical corpus path the `.expected`
    patterns embed. -/
public def compileAndRun (python : String) (root : System.FilePath) (stem : String)
    (v2 : Bool) : IO (Option (UInt32 × String)) := do
  let canonical := s!"StrataPythonTest/tests/{stem}.python.st.ion"
  let timeoutStr := ((← IO.getEnv "INTERPRET_TIMEOUT").getD "60")
  let pyPath := root / "StrataPythonTest" / "tests" / (stem ++ ".py")
  -- A missing corpus file is not a parse failure: it means a committed child names a
  -- `.py` that no longer exists, so fail loudly instead of returning `none` (a skip).
  -- Only a real `py_to_strata` failure on a present file is the silent skip below.
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
      return none
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
    return some (runOut.exitCode, output)

end StrataPython.InterpretGolden
