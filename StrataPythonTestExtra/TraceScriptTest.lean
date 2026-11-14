/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.SemDiff
meta import StrataPythonTest.Util.Python

/-! # The CPython tracer runs a program as `python FILE` does

The differential test takes CPython's side from `StrataPythonTest/Dyn/trace.py`. These tests run
small programs with the tracer, and check that:
- the program sees the `sys.argv` and `sys.path[0]` of `python FILE`, which runs it too, so it
  imports its own sibling modules and not the tracer's, also through a symlink to the file;
- the tracer refuses a program that writes to file descriptor 1 without `sys.stdout`, since that
  output would land outside the trace's output section;
- a global with a key that isn't a `str`, and an exception whose `__str__` raises, give a trace,
  not a crash of the tracer.

No test runs a CPython run that ignores SIGTERM until `timeout` kills it: with the limit of 60 s,
such a test would take 65 s.
-/

namespace StrataPython.TraceScriptTest

/-- Runs `action` with CPython 3.12, which `trace.py` needs, unless `SKIP_PYTHON_TESTS` is set. -/
meta def withPython312 (action : System.FilePath → IO Unit) : IO Unit := do
  if let some skip ← IO.getEnv "SKIP_PYTHON_TESTS" then
    if !skip.isEmpty then return
  action (← StrataPython.findPython3 (minVersion := 12) (maxVersion := 12))

/-- The text between `--- stdout N` and `--- outcome` of a trace. -/
meta def stdoutOf (trace : String) : Option String := do
  let rest ← (trace.splitOn "\n").tail?
  let text := "\n".intercalate rest
  let [out, _] := text.splitOn "\n--- outcome" | none
  some out

/-- Runs `trace.py` on `file` with `python`, in a root of the test's own next to `file`
(`STRATA_TRACE_ROOT`), so that the test shares no directory with another checkout or user. -/
meta def trace (python file : System.FilePath) : IO IO.Process.Output :=
  IO.Process.output
    { cmd := python.toString, args := #["-S", SemDiff.traceScript.toString, file.toString]
      env := #[("STRATA_TRACE_ROOT", some ((file.parent.getD ".") / "trace-root").toString)] }

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- The program's own directory comes first on `sys.path`, and `sys.argv` is `[FILE]`.  Through
  -- a symlink in another directory, CPython puts the directory of the file it points to first.
  IO.FS.createDirAll (dir / "a")
  IO.FS.createDirAll (dir / "b")
  IO.FS.writeFile (dir / "a" / "helper.py") "x = 7\n"
  let prog := dir / "a" / "prog.py"
  IO.FS.writeFile prog "import sys, helper, trace\n\
    print(len(sys.argv), sys.argv[0] == sys.argv[-1], helper.x, hasattr(trace, \"exc_lines\"))\n"
  let link := dir / "b" / "link.py"
  let ln ← IO.Process.output { cmd := "ln", args := #["-s", prog.toString, link.toString] }
  unless ln.exitCode == 0 do throw <| .userError s!"TraceScriptTest: ln -s failed: {ln.stderr}"
  for file in [prog, link] do
    let plain ← IO.Process.output { cmd := python.toString, args := #["-S", file.toString] }
    let r ← trace python file
    unless r.exitCode == 0 && plain.exitCode == 0 && stdoutOf r.stdout == some plain.stdout do
      throw <| .userError s!"TraceScriptTest: {file}: python FILE printed {plain.stdout.quote} \
        ({plain.stderr}), the trace is:\n{r.stdout}{r.stderr}"
    unless plain.stdout == "1 True 7 False\n" do
      throw <| .userError s!"TraceScriptTest: {file}: python FILE printed {plain.stdout.quote}"
  IO.println "TraceScriptTest: the program sees python FILE's sys.argv and sys.path[0]"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- Output that bypasses `sys.stdout` makes the tracer fail, since the trace can't hold it.
  for (name, src) in [("raw", "import os\nos.write(1, b\"RAW\\n\")\n"),
                      ("dunder", "import sys\nsys.__stdout__.write(\"RAW\\n\")\n"),
                      ("rebound", "import sys, io\nsys.__stdout__.write(\"RAW\\n\")\n\
                        sys.__stdout__ = io.StringIO()\nprint(\"hi\")\n")] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let r ← trace python prog
    unless r.exitCode != 0 && (r.stderr.splitOn "outside sys.stdout").length > 1 &&
        !(r.stdout.splitOn "RAW").length > 1 do
      throw <| .userError s!"TraceScriptTest: {name}: exit code {r.exitCode}, stdout:\n\
        {r.stdout}stderr:\n{r.stderr}"
  IO.println "TraceScriptTest: the tracer refuses output that bypasses sys.stdout"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- A global whose key isn't a `str`, and an exception whose `__str__` raises.
  let prog := dir / "odd.py"
  IO.FS.writeFile prog "globals()[1] = 2\nclass E(Exception):\n    def __str__(self): raise ValueError\n\
    class K:\n    def __repr__(self): raise ValueError\nglobals()[K()] = 3\nraise E()\n"
  let r ← trace python prog
  let want := "--- stdout 0\n\n--- outcome\nraised E: <exception str() failed>\n--- globals\n\
    E = <class 'E'>\nK = <class 'K'>\n__doc__ = None\n__name__ = '__main__'\n1 = 2\n\
    <no repr: ValueError> = 3\n"
  unless r.exitCode == 0 && r.stdout == want do
    throw <| .userError s!"TraceScriptTest: odd globals: exit code {r.exitCode}, stdout:\n\
      {r.stdout}stderr:\n{r.stderr}"
  IO.println "TraceScriptTest: odd globals and exceptions give a trace"

end StrataPython.TraceScriptTest
