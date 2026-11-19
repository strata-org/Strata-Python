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
  not a crash of the tracer;
- the trace's output holds what `python FILE` prints after the program, in its order (threads,
  exit handlers, then the module's finalizers), and a program that closes `sys.stdout` still
  gives a trace, also one that deletes `sys.stdout` or `sys.__stdout__`; text and bytes written
  to `sys.stdout.buffer` come out in CPython's order;
- rendering the globals and the outcome runs none of the program's code, not even that of a
  global's key that isn't a `str`, or of an exception's metaclass;
- a collection while the globals render runs no finalizer and no gc callback;
- the tracer fails, under any locale, when the program writes bytes that aren't UTF-8;
- a CPython run that something else kills is a failure, not a run that doesn't end, and one that
  lasts until the time limit is a run that doesn't end;
- the trace ends with `--- teardown after <n>` when something that the program made can still run
  code at the teardown, or the program installed a trace, profile or monitoring hook, and the
  tracer fails on a program that adds an audit hook;
- the tracer's known differences from `python FILE` stay as they are pinned.
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

/-- Runs `file` with `python FILE` and with the tracer, and gives both results. -/
meta def runBoth (python file : System.FilePath) : IO (IO.Process.Output × IO.Process.Output) := do
  let plain ← IO.Process.output
    { cmd := python.toString, args := #["-S", file.toString], cwd := file.parent }
  return (plain, ← trace python file)

/-- The count `n` of the trace's line `--- teardown after <n>`, if it has one, and its output. -/
meta def cutOf (trace : String) : Option Nat × String :=
  let split := SemDiff.splitTeardown trace
  (split.map (·.1), (stdoutOf ((split.map (·.2)).getD trace)).getD "")

/-- Whether the trace's output is `out`, the output of `python FILE`: all of it, or its first `n`
characters if the trace ends with `--- teardown after <n>`. -/
meta def agreesWith (out trace : String) : Bool :=
  match cutOf trace with
  | (some n, mine) => mine.take n == out.take n
  | (none, mine) => mine == out

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
    let (plain, r) ← runBoth python file
    unless r.exitCode == 0 && plain.exitCode == 0 && stdoutOf r.stdout == some plain.stdout do
      throw <| .userError s!"TraceScriptTest: {file}: python FILE printed {plain.stdout.quote} \
        ({plain.stderr}), the trace is:\n{r.stdout}{r.stderr}"
    unless plain.stdout == "1 True 7 False\n" do
      throw <| .userError s!"TraceScriptTest: {file}: python FILE printed {plain.stdout.quote}"
  -- The package's root shows as `<package>`, so that a trace is the same in every checkout.
  let root := (← IO.FS.realPath (← IO.currentDir)).toString
  let named := dir / "named.py"
  IO.FS.writeFile named s!"print({root.quote} + \"/x\")\n"
  let r ← trace python named
  unless r.exitCode == 0 && stdoutOf r.stdout == some "<package>/x\n" do
    throw <| .userError s!"TraceScriptTest: named: exit code {r.exitCode}, the trace is:\n\
      {r.stdout}{r.stderr}"
  -- A coding line is read as `python FILE` reads it, undecoded, and only the lines after it are
  -- decoded: here its "\\n" stays in the comment, and hz's "~" joins no line.
  for (name, src) in [("unicodeEscape", "# coding: unicode_escape \\nprint('no')\nprint('both')\n"),
      ("hz", "# coding: hz ~\nprint('a')\nprint('b')\n"),
      ("emacsCookie", "# -*- coding: utf-8-unix -*-\nprint('ran')\n"),
      ("localeCookie", "# coding: locale\nprint('locale')\n"),
      -- Lone carriage returns end lines, so this coding line is line 3, which nothing reads.
      ("crLines", "#!x\rprint(1)\r# coding: bogus\n"),
      -- After a byte order mark and a line of code, line 2's coding line is a plain comment.
      ("bomCodeLine", "\uFEFFx = 1\n# coding: latin-1\nprint('ran', x)\n")] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let (plain, r) ← runBoth python prog
    unless r.exitCode == 0 && plain.exitCode == 0 && stdoutOf r.stdout == some plain.stdout do
      throw <| .userError s!"TraceScriptTest: {name}: python FILE printed {plain.stdout.quote}, \
        the trace is:\n{r.stdout}{r.stderr}"
  -- `python FILE` rejects these, as it reads them: an idna part over 1024 characters, which its
  -- piecewise decoder refuses, a null byte on a coding line, a vertical tab before one, and a
  -- UTF-16 coding line.
  for (name, src) in [("idnaLong", "# coding: idna\nprint('idna')\n# " ++
        String.ofList (List.replicate 1100 'x') ++ "\n"),
      ("nullCookie", "# \x00 coding: latin-1\nprint(1)\n"),
      ("verticalTab", "\x0b\n# coding: latin-1\nprint(1)\n"),
      ("utf16Cookie", "# -*- coding: utf-16 -*-\nprint(1)\n"),
      -- The decoder starts on the coding line's newline, so the first part is 1025 characters.
      ("idna1024", "# coding: idna\nprint('a')\n#" ++ String.ofList (List.replicate 1013 'x') ++
        "\n")] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let (plain, r) ← runBoth python prog
    unless plain.exitCode == 1 && r.exitCode == 0 && r.stdout == SemDiff.syntaxTrace do
      throw <| .userError s!"TraceScriptTest: {name}: python FILE exited {plain.exitCode}, \
        the trace is:\n{r.stdout}{r.stderr}"
  -- A module of the program's own directory is checked for the runtime too, and one named like a
  -- module that the tracer has loaded cuts the trace at 0, since `python FILE` would import it.
  IO.FS.createDirAll (dir / "sib")
  IO.FS.writeFile (dir / "sib" / "helper.py") "import sys\nn = len(sys.orig_argv)\n"
  IO.FS.writeFile (dir / "sib" / "keyword.py") "print(\"sibling keyword module runs\")\n"
  IO.FS.writeFile (dir / "sib" / "prog.py") "print(\"hi\")\nimport helper\nimport dataclasses\n"
  let r ← trace python (dir / "sib" / "prog.py")
  unless r.exitCode == 0 && (cutOf r.stdout).1 == some 0 do
    throw <| .userError s!"TraceScriptTest: siblings: the trace is:\n{r.stdout}{r.stderr}"
  IO.FS.removeFile (dir / "sib" / "keyword.py")
  let r ← trace python (dir / "sib" / "prog.py")
  unless r.exitCode == 0 && (cutOf r.stdout).1 == some 3 do
    throw <| .userError s!"TraceScriptTest: siblingRuntime: the trace is:\n{r.stdout}{r.stderr}"
  -- A package's relative import is followed too, and the program's own file counts as a module of
  -- its directory.
  IO.FS.createDirAll (dir / "rel" / "pkg")
  IO.FS.writeFile (dir / "rel" / "pkg" / "__init__.py") "from . import inner\n"
  IO.FS.writeFile (dir / "rel" / "pkg" / "inner.py") "import sys\n"
  IO.FS.writeFile (dir / "rel" / "prog.py") "print(\"hi\")\nimport pkg\n"
  IO.FS.createDirAll (dir / "own")
  IO.FS.writeFile (dir / "own" / "ast.py") "print(\"hi\")\n"
  IO.FS.createDirAll (dir / "std")
  IO.FS.writeFile (dir / "std" / "copy.py") "\n"
  IO.FS.writeFile (dir / "std" / "prog.py") "print(\"hi\")\n"
  IO.FS.createDirAll (dir / "star" / "pk")
  IO.FS.writeFile (dir / "star" / "pk" / "__init__.py") "__all__ = [\"sub\"]\n"
  IO.FS.writeFile (dir / "star" / "pk" / "sub.py") "import sys\n"
  IO.FS.writeFile (dir / "star" / "prog.py") "print(\"hi\")\nfrom pk import *\n"
  for (file, mark) in [(dir / "rel" / "prog.py", 3), (dir / "own" / "ast.py", 0),
      (dir / "std" / "prog.py", 0), (dir / "star" / "prog.py", 3)] do
    let r ← trace python file
    unless r.exitCode == 0 && (cutOf r.stdout).1 == some mark do
      throw <| .userError s!"TraceScriptTest: {file}: the trace is:\n{r.stdout}{r.stderr}"
  IO.println "TraceScriptTest: the program sees python FILE's sys.argv and sys.path[0]"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- Output that bypasses `sys.stdout` makes the tracer fail, since the trace can't hold it.
  for (name, src) in [("raw", "import os\nos.write(1, b\"RAW\\n\")\n"),
                      ("dunder", "import sys\nsys.__stdout__.write(\"RAW\\n\")\n"),
                      ("rebound", "import sys, io\nsys.__stdout__.write(\"RAW\\n\")\n\
                        sys.__stdout__ = io.StringIO()\nprint(\"hi\")\n"),
                      ("closedStderr", "import os, sys\nsys.stderr.close()\nos.write(1, b\"RAW\\n\")\n"),
                      -- Output that the program truncates again, through a path, still counts.
                      ("truncated", "import codecs\nf = codecs.open(\"/dev/stdout\", \"w\")\n\
                        f.write(\"RAW\\n\")\nf.flush()\ntry:\n    f.truncate(0)\n\
                        except OSError:\n    pass\nprint(\"hi\")\n")] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let r ← trace python prog
    unless r.exitCode != 0 && (r.stderr.splitOn "outside sys.stdout").length > 1 &&
        !(r.stdout.splitOn "RAW").length > 1 do
      throw <| .userError s!"TraceScriptTest: {name}: exit code {r.exitCode}, stdout:\n\
        {r.stdout}stderr:\n{r.stderr}"
  IO.println "TraceScriptTest: the tracer refuses output that bypasses sys.stdout"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- A global whose key isn't a `str`, a class whose `__qualname__` holds a line break, and an
  -- exception whose `__str__` raises.
  let prog := dir / "odd.py"
  IO.FS.writeFile prog "globals()[1] = 2\nclass E(Exception):\n    def __str__(self): raise ValueError\n\
    class K:\n    def __repr__(self): raise ValueError\nglobals()[K()] = 3\n\
    class D: pass\nD.__qualname__ = \"a\\n--- teardown after 5\"\nraise E()\n"
  let r ← trace python prog
  -- The program calls `globals()`, which reaches the runtime, so the trace is cut at its end.
  let want := "--- stdout 0\n\n--- outcome\nraised E: <exception str() failed>\n--- globals\n\
    D = <a render with a line break>\nE = <class 'E'>\nK = <class 'K'>\n__doc__ = None\n__name__ = '__main__'\n1 = 2\n\
    <K object> = 3\n--- teardown after 0\n"
  unless r.exitCode == 0 && r.stdout == want do
    throw <| .userError s!"TraceScriptTest: odd globals: exit code {r.exitCode}, stdout:\n\
      {r.stdout}stderr:\n{r.stderr}"
  IO.println "TraceScriptTest: odd globals and exceptions give a trace"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- Output after the program's last statement, in `python FILE`'s order: its threads, then its
  -- exit handlers, then its module's finalizers, which still see the globals.  A program that
  -- closes `sys.stdout` still gives a trace, and a write after the close raises, as in CPython.
  for (name, src, want, outcome) in [
      ("exit", "import atexit\natexit.register(print, \"late\")\nprint(\"hi\")\n", "hi\nlate\n", "ok"),
      ("thread", "import threading\nthreading.Timer(0.2, print, [\"late\"]).start()\nprint(\"hi\")\n",
        "hi\nlate\n", "ok"),
      ("final", "class C:\n    def __del__(self): print(\"late\")\nc = C()\nprint(\"hi\")\n", "hi\nlate\n",
        "ok"),
      ("finalGlobal", "def say(): print(\"late\")\nclass C:\n    def __del__(self): say()\nc = C()\n\
        print(\"hi\")\n", "hi\nlate\n", "ok"),
      ("order", "import atexit, threading\natexit.register(print, \"atexit\")\n\
        threading.Timer(0.2, print, [\"thread\"]).start()\nprint(\"main\")\n", "main\nthread\natexit\n", "ok"),
      ("closed", "import sys\nprint(\"hi\")\nsys.stdout.close()\n", "hi\n", "ok"),
      ("closedWrite", "import sys\nprint(\"hi\")\nsys.stdout.close()\nprint(\"x\")\n", "hi\n", "raise"),
      ("excLocal", "import atexit\nclass C:\n    def __del__(self): print(\"late local\")\n\
        atexit.register(print, \"atexit\")\ndef f():\n    c = C()\n    raise ValueError(\"boom\")\nf()\n",
        "atexit\nlate local\n", "raise"),
      ("sysExit", "import atexit\nclass C:\n    def __del__(self): print(\"late local\")\n\
        atexit.register(print, \"atexit\")\ndef f():\n    c = C()\n    raise SystemExit(0)\nf()\n",
        "late local\natexit\n", "raised SystemExit: 0"),
      ("rebound", "import io, sys\nclass C:\n    def __del__(self): print(\"late\")\nc = C()\n\
        print(\"hi\")\nsys.stdout = io.StringIO()\n", "hi\nlate\n", "ok"),
      ("ownStdout", "import sys\nclass B:\n    def __init__(self, inner):\n" ++
        "        self.inner = inner\n        self.parts = []\n    def write(self, s):\n" ++
        "        self.parts.append(s)\n        return len(s)\n    def flush(self):\n" ++
        "        self.inner.write(\"\".join(self.parts))\n        self.parts.clear()\n" ++
        "sys.stdout = B(sys.stdout)\nprint(\"hi\")\n", "hi\n", "ok"),
      ("ownWrapper", "import io, sys\nsys.stdout = io.TextIOWrapper(sys.stdout.buffer, write_through=False)\n\
        print(\"main\")\n", "main\n", "ok"),
      ("noStdout", "import sys\nprint(\"hi\")\ndel sys.stdout\n", "hi\n", "ok"),
      ("noDunder", "import sys\nprint(\"hi\")\ndel sys.__stdout__\n", "hi\n", "ok"),
      ("globalWrapper", "import io, sys\nw = io.TextIOWrapper(sys.stdout.buffer, write_through=False)\n" ++
        "print(\"x\", file=w)\n", "x\n", "ok"),
      ("mixed", "import sys\nprint(\"a\")\nsys.stdout.buffer.write(b\"b\\n\")\n", "b\na\n", "ok"),
      ("threadExitRaises", "import threading\ndef boom(): raise RuntimeError(\"cb\")\n" ++
        "threading._register_atexit(boom)\nprint(\"hi\")\n", "hi\n", "ok"),
      ("threadExitTwice", "import threading\ndef boom(): raise RuntimeError(\"cb\")\n" ++
        "threading._register_atexit(boom)\nthreading._register_atexit(lambda: print(\"cb ran\"))\n" ++
        "print(\"hi\")\n", "hi\ncb ran\n", "ok"),
      ("errFinalizer", "import sys\nclass C:\n    def __del__(self): print(\"fin err\", file=sys.stderr)\n" ++
        "c = C()\nsys.stderr = sys.stdout\nprint(\"hi\")\n", "hi\n", "ok"),
      ("threadExitJoin", "import threading, time\ndef boom(): raise RuntimeError(\"cb\")\n" ++
        "threading._register_atexit(boom)\n" ++
        "threading.Thread(target=lambda: (time.sleep(30), print(\"late thread\"))).start()\nprint(\"hi\")\n",
        "hi\n", "ok"),
      ("aliveAfterFail", "import atexit, threading\ndef boom(): raise RuntimeError(\"cb\")\n" ++
        "threading._register_atexit(boom)\n" ++
        "atexit.register(lambda: print(\"alive\", threading.main_thread().is_alive()))\nprint(\"hi\")\n",
        "hi\nalive True\n", "ok"),
      ("joinWaiter", "import threading\ndef boom(): raise RuntimeError(\"cb\")\n" ++
        "threading._register_atexit(boom)\n" ++
        "threading.Thread(target=lambda: (threading.main_thread().join(), print(\"joined\"))).start()\n" ++
        "print(\"hi\")\n", "hi\n", "ok"),
      ("streamAttrs", "import sys\nsys.stdout.saved = 1\nsys.stdout.wrote = 2\nclass C:\n" ++
        "    def __del__(self): print(sys.stdout.saved, sys.stdout.wrote)\nc = C()\n", "1 2\n", "ok"),
      ("threadExitNoStderr", "import sys, threading\ndef boom(): raise RuntimeError(\"cb\")\n" ++
        "threading._register_atexit(boom)\nprint(\"hi\")\ndel sys.stderr\n", "hi\n", "ok"),
      ("threadExitClosedStderr", "import sys, threading\ndef boom(): raise RuntimeError(\"cb\")\n" ++
        "threading._register_atexit(boom)\nprint(\"hi\")\nsys.stderr.close()\n", "hi\n", "ok"),
      ("threadExitStderrNone", "import sys, threading\ndef boom(): raise RuntimeError(\"cb\")\n" ++
        "threading._register_atexit(boom)\nprint(\"hi\")\nsys.stderr = None\n", "hi\n", "ok"),
      ("queueWorker", "import queue, threading\nq = queue.Queue()\nresults = []\ndef worker():\n" ++
        "    while True:\n        item = q.get()\n        results.append(item * 2)\n        q.task_done()\n" ++
        "threading.Thread(target=worker, daemon=True).start()\nfor i in range(3):\n    q.put(i)\n" ++
        "q.join()\nprint(results)\n", "[0, 2, 4]\n", "ok"),
      ("exitBytes", "import atexit, sys\natexit.register(sys.stdout.buffer.write, b\"exit\\n\")\n" ++
        "print(\"a\")\n", "a\nexit\n", "ok"),
      ("detached", "import sys\nprint(\"a\")\nb = sys.stdout.detach()\nb.write(b\"raw bytes\\n\")\n",
        "a\nraw bytes\n", "ok"),
      ("patchLstat", "import os\nreal = os.lstat\ndef lstat(*a, **k):\n    print(\"lstat called\")\n" ++
        "    return real(*a, **k)\nos.lstat = lstat\nprint(\"hi\")\n", "hi\n", "ok"),
      ("patchScandir", "import os\nos.scandir = None\nprint(\"hi\")\n", "hi\n", "ok"),
      ("patchIOBase", "import io\nio.IOBase.closed = property(lambda self: True)\nprint(\"hi\")\n",
        "hi\n", "ok"),
      ("captureData", "import sys\nprint(\"a\")\nsys.stdout.flush()\ntry:\n" ++
        "    sys.stdout.buffer.raw.data[:] = b\"forged\\n\"\nexcept AttributeError:\n    pass\nprint(\"b\")\n",
        "a\nb\n", "ok"),
      ("buffered", "import sys\nsys.stdout.reconfigure(write_through=False)\nprint(\"x\")\n", "x\n",
        "ok")] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let plain ← IO.Process.output
      { cmd := python.toString, args := #["-S", prog.toString], cwd := prog.parent }
    -- "raise": the outcome is the exception that ends `python FILE`, its last line of stderr.
    let outcome := if outcome == "raise" then
      "raised " ++ ((plain.stderr.trimAsciiEnd.toString.splitOn "\n").getLast?.getD "") else outcome
    let r ← trace python prog
    -- Nothing but the globals' lines follows the globals' header, after the teardown line, if any,
    -- is left out.
    let kept := ((SemDiff.splitTeardown r.stdout).map (·.2)).getD r.stdout
    let globalsOnly := match kept.splitOn "--- globals\n" with
      | [_, g] => (g.splitOn "\n").all fun l => l.isEmpty || (l.splitOn " = ").length > 1
      | _ => false
    unless plain.stdout == want && r.exitCode == 0 && stdoutOf r.stdout == some want &&
        (r.stdout.splitOn s!"--- outcome\n{outcome}\n").length > 1 && globalsOnly do
      throw <| .userError s!"TraceScriptTest: {name}: python FILE printed {plain.stdout.quote}, \
        exit code {r.exitCode}, the trace is:\n{r.stdout}{r.stderr}"
  -- An exception at threading's shutdown is reported where CPython reports it: to the program's
  -- `sys.stderr`, here its stdout.  The report holds CPython's install path, so it isn't pinned.
  let prog := dir / "threadExitReport.py"
  IO.FS.writeFile prog ("import sys, threading\nsys.stderr = sys.stdout\ndef boom(): raise RuntimeError(\"cb\")\n" ++
    "threading._register_atexit(boom)\nprint(\"hi\")\n")
  let (plain, r) ← runBoth python prog
  unless plain.stdout.startsWith "hi\nException ignored in: <module 'threading'" && r.exitCode == 0 &&
      stdoutOf r.stdout == some plain.stdout do
    throw <| .userError s!"TraceScriptTest: threadExitReport: python FILE printed {plain.stdout.quote}, \
      exit code {r.exitCode}, the trace is:\n{r.stdout}{r.stderr}"
  IO.println "TraceScriptTest: the trace holds the output that python FILE prints after the program"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- Rendering the globals runs none of the program's code: a metaclass's `__getattribute__` or
  -- `__eq__` that prints, or records what it is asked, changes nothing, and neither does a global's
  -- key whose `__repr__`, `__hash__` or `__lt__` prints, through any stream.
  let withMeta (body : String) : String :=
    "class M(type):\n    def __getattribute__(cls, n):\n" ++ body ++
    "        return super().__getattribute__(n)\nclass C(metaclass=M):\n    x = 1\n"
  for (name, src, want) in [
      ("render", withMeta "        print(\"ga\", n)\n" ++ "print(C.x)\n", some "ga x\n1\n"),
      ("renderSaved", "import sys\nout = sys.stdout\n" ++ withMeta "        print(\"ga\", n, file=out)\n",
        some ""),
      ("renderBuffered", "import sys\nsys.stdout.reconfigure(write_through=False)\nout = sys.stdout\n" ++
        withMeta "        print(\"ga\", n, file=out)\n", some ""),
      ("renderOwn", "import io, sys\nw = io.TextIOWrapper(sys.stdout.buffer, write_through=False)\n" ++
        withMeta "        print(\"ga\", n, file=w)\n", some ""),
      ("renderSeen", "seen = []\nclass D:\n    def __del__(self): print(\"seen\", seen)\nd = D()\n" ++
        withMeta "        seen.append(n)\n", some "seen []\n"),
      ("renderEq", "seen = []\nclass E(type):\n    def __eq__(cls, o):\n        seen.append(\"eq\")\n" ++
        "        return type.__eq__(cls, o)\n    __hash__ = type.__hash__\nclass F(metaclass=E): pass\n" ++
        "f = F()\nclass D:\n    def __del__(self): print(\"seen\", seen)\nd = D()\n", some "seen []\n"),
      ("renderTypeHash", "class M(type):\n    def __hash__(cls):\n        print(\"hash\")\n" ++
        "        return 1\nclass C(metaclass=M): pass\nc = C()\n", some ""),
      ("renderExcName", "class M(type):\n    def __getattribute__(cls, n):\n" ++
        "        if n == \"__qualname__\": print(\"ga\", n)\n        return super().__getattribute__(n)\n" ++
        "class E(Exception, metaclass=M): pass\nraise E(\"x\")\n", some ""),
      ("renderExcCause", "class E(Exception):\n    @property\n    def __cause__(self):\n" ++
        "        print(\"cause\")\n        return None\nraise E(\"x\")\n", some "")] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let (plain, r) ← runBoth python prog
    unless some plain.stdout == want && r.exitCode == 0 && stdoutOf r.stdout == want do
      throw <| .userError s!"TraceScriptTest: {name}: python FILE printed {plain.stdout.quote}, \
        exit code {r.exitCode}, the trace is:\n{r.stdout}{r.stderr}"
  let reprWrites (out : String) : String :=
    "class K:\n    def __repr__(self):\n        " ++ out ++ "\n        return \"K()\"\n"
  for (name, src) in [("renderKey", reprWrites "print(\"repr\")"),
      ("renderKeyBytes", "import sys\nb = sys.stdout.buffer\n" ++ reprWrites "b.write(b\"repr\\n\")"),
      ("renderKeyDetached", "import sys\nprint(\"a\")\nb = sys.stdout.detach()\n" ++
        reprWrites "b.write(b\"repr\\n\")"),
      ("renderKeyOwnBuffer", "import io, sys\nb = io.BufferedWriter(sys.stdout.buffer.raw)\n" ++
        reprWrites "b.write(b\"repr\\n\")"),
      ("renderKeyStacked", "import io, sys\nb = io.BufferedWriter(sys.stdout.buffer)\n" ++
        reprWrites "b.write(b\"repr\\n\")"),
      ("renderKeyHash", "class K:\n    def __hash__(self):\n        print(\"hash\")\n        return 1\n"),
      ("renderKeyStr", "class K(str):\n    def __repr__(self):\n        print(\"repr\")\n        return \"K\"\n" ++
        "    def __lt__(self, o):\n        print(\"lt\")\n        return str.__lt__(self, o)\n" ++
        "    __hash__ = str.__hash__\n")] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog (src ++ "globals()[K()] = 1\n")
    let (plain, r) ← runBoth python prog
    unless r.exitCode == 0 && stdoutOf r.stdout == some plain.stdout &&
        (((SemDiff.splitTeardown r.stdout).map (·.2)).getD r.stdout).endsWith "\n<K object> = 1\n" do
      throw <| .userError s!"TraceScriptTest: {name}: python FILE printed {plain.stdout.quote}, \
        exit code {r.exitCode}, the trace is:\n{r.stdout}{r.stderr}"
  IO.println "TraceScriptTest: rendering runs no program code, not even that of a global's key"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- A collection while the globals render runs no finalizer and no gc callback, so that their
  -- output lands in the program's output and doesn't fail the tracer: with a threshold of 1,
  -- every allocation collects, and each collection makes garbage whose finalizer prints.
  let prog := dir / "collect.py"
  IO.FS.writeFile prog ("import gc\nclass C:\n    def __del__(self):\n        print(\"late\")\n" ++
    "def cb(phase, info):\n    if phase == \"start\":\n        x = C()\n        x.me = x\n" ++
    "gc.callbacks.append(cb)\ngc.set_threshold(1)\nxs = [[1], [2]]\n")
  let r ← trace python prog
  let lines := ((stdoutOf r.stdout).getD "x").splitOn "\n" |>.filter (· != "")
  let tail := "--- outcome\nok\n--- globals\nC = <class 'C'>\n__doc__ = None\n__name__ = '__main__'\n" ++
    "cb = <function object>\ngc = <module object>\nxs = [[1], [2]]\n"
  -- The program's gc callback could still run at the teardown, so the trace is marked.
  let some (_, kept) := SemDiff.splitTeardown r.stdout
    | throw <| .userError s!"TraceScriptTest: collect: no teardown line:\n{r.stdout}{r.stderr}"
  unless r.exitCode == 0 && kept.startsWith "--- stdout " && kept.endsWith tail &&
      !lines.isEmpty && lines.all (· == "late") do
    throw <| .userError s!"TraceScriptTest: collect: exit code {r.exitCode}, the trace is:\n\
      {r.stdout}{r.stderr}"
  IO.println "TraceScriptTest: a collection during rendering runs no program code"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- Bytes that aren't UTF-8, written through `sys.stdout.buffer`, make the tracer fail under any
  -- locale, since a trace is UTF-8 text.
  let prog := dir / "bytes.py"
  IO.FS.writeFile prog "import sys\nprint(\"hi\")\nsys.stdout.buffer.write(b\"\\xff\\n\")\n"
  for loc in ["C.UTF-8", "en_US.UTF-8"] do
    let r ← IO.Process.output
      { cmd := python.toString, args := #["-S", SemDiff.traceScript.toString, prog.toString]
        env := #[("STRATA_TRACE_ROOT", some (dir / "trace-root").toString), ("LC_ALL", some loc)] }
    unless r.exitCode != 0 && (r.stderr.splitOn "wrote bytes that aren't UTF-8").length > 1 do
      throw <| .userError s!"TraceScriptTest: bytes under {loc}: exit code {r.exitCode}, \
        stderr:\n{r.stderr}"
  IO.println "TraceScriptTest: the tracer fails on bytes that aren't UTF-8, under any locale"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- A run that something else kills with SIGKILL is a failure, not a run that doesn't end.
  let prog := dir / "kill.py"
  IO.FS.writeFile prog "import os, signal\nprint(\"x\")\nos.kill(os.getpid(), signal.SIGKILL)\n"
  match ← (SemDiff.cpythonTrace python prog).toBaseIO with
  | .ok t => throw <| .userError s!"TraceScriptTest: a killed run gave the trace:\n{t}"
  | .error e =>
    unless ((toString e).splitOn "trace.py failed with exit code 137").length > 1 do
      throw <| .userError s!"TraceScriptTest: a killed run failed with: {e}"
  IO.println "TraceScriptTest: a killed CPython run fails"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- A run that lasts until the time limit doesn't end, also one that ignores SIGTERM until
  -- `timeout` kills it 5 s later.
  for (name, src) in [("loop", "while True: pass\n"),
      ("stubborn", "import signal\nsignal.signal(signal.SIGTERM, signal.SIG_IGN)\nwhile True: pass\n")] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let t ← SemDiff.cpythonTrace python prog (seconds := 1)
    unless t == SemDiff.endlessTrace do
      throw <| .userError s!"TraceScriptTest: {name}: the run gave the trace:\n{t}"
  IO.println "TraceScriptTest: a run that lasts until the time limit doesn't end"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- When something that the program made can still run code at the teardown (a finalizer, a
  -- suspended generator with a `try`, a weak reference's callback, a thread, a gc callback, a
  -- stream that isn't closed), or the program installed a trace, profile or monitoring hook, the
  -- trace ends with `--- teardown after <n>`: only its first n characters of output are in
  -- `python FILE`'s order.  A finished program leaves none of these.
  let hi := "print(\"hi\")\n"
  for (name, src, mark) in [
      ("plain", hi ++ "x = 1\n", none),
      ("closedFile", "with open(\"f\", \"w\") as f:\n    f.write(\"x\")\n" ++ hi, some 3),
      ("memoryStream", "import io\ns = io.StringIO()\n" ++ hi, some 3),
      ("finishedGenerator", "def g():\n    try:\n        yield 1\n    finally:\n        pass\n" ++
        "for _ in g(): pass\n" ++ hi, none),
      ("finalizer", hi ++ "class C:\n    def __del__(self): print(\"del\")\nx = [C(), C()]\n",
        some 3),
      ("generator", "def g():\n    try:\n        yield 1\n    finally:\n        print(\"fin\")\n" ++
        "it = g()\nnext(it)\n" ++ hi, some 3),
      ("weakrefCallback", "import weakref\nclass C: pass\nc = C()\n" ++
        "r = weakref.ref(c, lambda r: print(\"cb\"))\n" ++ hi, some 3),
      ("weakrefFinalize", "import weakref\nclass C: pass\nc = C()\n" ++
        "f = weakref.finalize(c, print, \"fin\")\n" ++ hi, some 3),
      ("weakrefFinalizeLate", "import weakref\nclass C: pass\nc = C()\n" ++
        "f = weakref.finalize(c, print, \"fin\")\nf.atexit = False\n" ++ hi, some 3),
      ("thread", "import threading\nthreading.Timer(0.01, print, [\"late\"]).start()\n" ++ hi, some 3),
      ("daemon", "import queue, threading\nq = queue.Queue()\n" ++
        "threading.Thread(target=q.get, daemon=True).start()\n" ++ hi, some 3),
      ("gcCallback", "import gc\ngc.callbacks.append(lambda phase, info: None)\n" ++ hi, some 3),
      ("ownStream", "import io, sys\nw = io.TextIOWrapper(sys.stdout.buffer)\n" ++ hi, some 3),
      ("baselineDel", "import os\ntype(os.environ).__del__ = lambda self: print(\"environ gone\")\n" ++
        hi, some 3),
      -- A program that rebinds builtins, module functions or `gc.callbacks`, also only for a while,
      -- changes none of the tracer's code.
      ("patchGc", "import gc\ngc.get_objects = lambda *a, **k: []\n" ++
        "class C:\n    def __del__(self): pass\nc = C()\n" ++ hi, some 3),
      ("patchAtExit", "import atexit, gc\natexit.register(setattr, gc, \"collect\", None)\n" ++ hi,
        some 3),
      ("patchAndRestore", "import gc, sys\nclass D:\n    def __del__(self): print(\"del\")\n" ++
        "class Writer:\n    def __init__(self, inner): self.inner = inner\n" ++
        "    def write(self, s): return self.inner.write(s)\n" ++
        "    def flush(self): self.inner.flush()\n" ++
        "    def __del__(self):\n        if hasattr(gc, \"saved\"): gc.get_objects = gc.saved\n" ++
        "class Patcher:\n    def __del__(self):\n        gc.saved = gc.get_objects\n" ++
        "        gc.get_objects = lambda *a, **k: []\n" ++
        "x = [D(), D()]\nsys.stdout = Writer(sys.stdout)\ndef f():\n    p = Patcher()\n" ++
        "    raise ValueError(\"v\")\nf()\n", some 0),
      ("gcCallbacksRebound", "import gc\ngc.callbacks.append(lambda phase, info: None)\n" ++
        "gc.callbacks = []\n" ++ hi, some 3),
      ("patchBuiltins", "import atexit, builtins\nbuiltins.any = lambda it: False\n" ++
        "atexit.register(setattr, builtins, \"len\", None)\n" ++
        "class C:\n    def __del__(self): pass\nc = C()\n" ++ hi, some 3),
      ("profileHook", "import sys\nsys.setprofile(lambda *a: None)\n" ++ hi, some 3),
      ("traceOff", "import sys\nsys.settrace(lambda *a: None)\nsys.settrace(None)\n" ++ hi, some 3),
      ("monitoring", "import sys\nsys.monitoring.use_tool_id(3, \"t\")\n" ++
        "sys.monitoring.register_callback(3, sys.monitoring.events.PY_START, lambda *a: None)\n" ++
        hi, some 3),
      ("unawaited", "import atexit, warnings\n" ++
        "warnings.showwarning = lambda message, *a, **k: print(\"warned:\", message)\n" ++
        "async def co():\n    pass\nc = co()\n" ++ hi, some 3),
      ("releaseBuffer", "class B:\n    def __buffer__(self, flags):\n        return memoryview(b\"abc\")\n" ++
        "    def __release_buffer__(self, view):\n        print(\"released\")\na = memoryview(B())\n" ++ hi,
        some 3),
      -- A program that reaches the interpreter's runtime is cut at its end, whatever it does after.
      ("importSys", hi ++ "import sys\n", some 3),
      ("importInFunction", hi ++ "def f():\n    import os\n", some 3),
      ("runtimeAttribute", "import dataclasses\n" ++ hi ++ "x = dataclasses.sys\n", some 3),
      ("builtinsName", hi ++ "x = __builtins__\n", some 3),
      ("subclasses", hi ++ "x = object.__subclasses__()\n", some 3),
      ("computedGetattr", hi ++ "n = \"x\"\nv = getattr(1, n, None)\n", some 3),
      ("runtimeGetattr", hi ++ "def f(): pass\nv = getattr(f, \"__globals__\")\n", some 3),
      ("globalsCall", hi ++ "g = globals()\n", some 3),
      ("dynamicImport", "import importlib\n" ++ hi, some 3),
      ("literalGetattr", hi ++ "v = getattr(1, \"real\")\n", none),
      ("runtimeString", hi ++ "n = \"{0.tb_frame}\"\n", some 3),
      ("runtimePattern", hi ++ "match 1:\n    case object(tb_frame=t):\n        pass\n", some 3),
      ("stackLevel", hi ++ "def f(**k): pass\nf(stacklevel=2)\n", some 3),
      ("attrGetter", "import operator\n" ++ hi ++ "g = operator.attrgetter(\"x\")\n", some 3),
      ("attrGetterAlias", "from operator import attrgetter as ag\n" ++ hi, some 3),
      ("moduleString", hi ++ "n = \"sys:_getframe\"\n", some 3),
      ("resolveName", "import pkgutil\n" ++ hi ++ "f = pkgutil.resolve_name\n", some 3),
      ("helpString", hi ++ "def f():\n    help(\"x\")\n", some 3),
      -- `python FILE` fails on some f-string fields that span lines, so nothing is compared.
      ("splitField", "x = 1\nprint(f\"\"\"{x=!r\n}\"\"\")\n", some 0),
      ("getattributeString", hi ++ "n = \"C.__getattribute__\"\n", none),
      ("frozen", "import builtins, gc\nclass C:\n    def __del__(self): print(\"late\")\n" ++
        "builtins.c = C()\ngc.freeze()\n" ++ hi, some 3),
      ("weakProxy", "import weakref\nclass C: pass\nc = C()\n" ++
        "p = weakref.proxy(c, lambda r: print(\"proxy cb\"))\n" ++ hi, some 3),
      -- Programs that don't reach the runtime, so that only the teardown check marks them: a
      -- library's weak reference callback, a library's thread, a coroutine that never ran, and a
      -- suspended generator.
      ("libraryWeakref", "import logging\n" ++ hi, some 3),
      ("libraryThread", "import logging.handlers, queue\n" ++
        "logging.handlers.QueueListener(queue.Queue()).start()\n" ++ hi, some 3),
      ("coroutinePlain", "async def co():\n    pass\nc = co()\n" ++ hi, some 3),
      ("generatorPlain", "def g():\n    yield 1\nit = g()\nnext(it)\n" ++ hi, some 3)] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let (plain, r) ← runBoth python prog
    unless r.exitCode == 0 && (cutOf r.stdout).1 == mark && agreesWith plain.stdout r.stdout do
      throw <| .userError s!"TraceScriptTest: {name}: exit code {r.exitCode}, the trace is:\n\
        {r.stdout}{r.stderr}"
  -- An audit hook can't be removed, and it would see the tracer's own code; and a program that
  -- changes the capture of its output would change the tracer's results.  The tracer fails on
  -- each.
  for (name, src, message) in [
      ("audit", "import sys\nsys.addaudithook(lambda *a: None)\n", "added an audit hook"),
      ("fork", "import os\nif os.fork() == 0:\n    os._exit(0)\nos.wait()\n", "forked"),
      ("patchCapture", "import sys\ntry:\n    type(sys.stdout.buffer.raw).write = lambda self, b: len(b)\n" ++
        "except TypeError:\n    pass\n" ++ hi, "changed the capture")] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let r ← trace python prog
    unless r.exitCode != 0 && (r.stderr.splitOn message).length > 1 do
      throw <| .userError s!"TraceScriptTest: {name}: exit code {r.exitCode}, the trace is:\n\
        {r.stdout}{r.stderr}"
  IO.println "TraceScriptTest: the trace marks the output that a shutdown or a hook may reorder"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- The tracer reports the program's uncaught exception as `python FILE` does, so what the report
  -- runs of the program's code (an exception's `__str__`, the lookups of a "Did you mean"
  -- suggestion, a `SyntaxError`'s fields) prints as there.  The trace is marked where the
  -- tracer's own `str` of the outcome's exception would run the program's code again, and where
  -- CPython's last flush of a replaced stream runs it; up to the mark, its output is
  -- `python FILE`'s.
  let hi := "print(\"hi\")\n"
  for (name, src, mark) in [
      ("excPlain", "class E(Exception): pass\nprint(\"hi\")\nraise E(\"x\")\n", false),
      ("excChainStr", "class A(Exception):\n    def __str__(self):\n        print(\"str of A ran\")\n" ++
        "        return \"a\"\ntry:\n    raise A()\nexcept A:\n    raise ValueError(\"v\")\n", false),
      ("chainOSError", "class Weird:\n    def __str__(self):\n        print(\"weird str\")\n" ++
        "        return \"w\"\ntry:\n    e = OSError(2, \"plain\")\n    e.strerror = Weird()\n" ++
        "    raise e\nexcept OSError:\n    raise ValueError(\"outer\")\n", false),
      ("attrErrorPlain", "x = 1\nx.missing\n", false),
      -- The `str` of the outcome's exception, and of a SystemExit's code, prints, and the tracer's
      -- own `str` would print it again; a SystemExit whose `code` raises is reported as CPython
      -- reports it, through the exception itself.
      ("excStrPrints", "class E(Exception):\n    def __str__(self):\n        print(\"str of E\")\n" ++
        "        return \"e\"\n" ++ hi ++ "raise E()\n", true),
      ("exitCodeStr", "class C:\n    def __str__(self):\n        print(\"str of C\")\n" ++
        "        return \"c\"\n" ++ hi ++ "raise SystemExit(C())\n", true),
      ("exitCodeRaises", "class E(SystemExit):\n    @property\n    def code(self):\n" ++
        "        raise ValueError(\"no\")\n" ++ hi ++ "raise E()\n", true),
      -- The program's module starts with `python FILE`'s names.
      ("startNames", "print(__annotations__, __cached__)\nx: int = 1\nprint(__annotations__)\n",
        false),
      -- `__loader__` reaches the runtime, so the trace is cut at the program's end.
      ("loaderName", "print(type(__loader__).__name__)\n", true),
      ("attrErrorDir", "class C:\n    def __dir__(self):\n        print(\"dir\")\n        return []\n" ++
        "C().missing\n", false),
      ("attrErrorGetattribute", "class C:\n    def __getattribute__(self, n):\n" ++
        "        if n == \"__dict__\":\n            print(\"getattribute\", n)\n" ++
        "        return object.__getattribute__(self, n)\nc = C()\nc.missing\n", true),
      ("nameErrorSelf", "class C:\n    def __getattr__(self, n):\n        print(\"getattr\", n)\n" ++
        "        raise AttributeError(n)\n    def m(self):\n        return undefined_name\nC().m()\n",
        false),
      ("nameSelfProperty", "class C:\n    @property\n    def size(self):\n" ++
        "        print(\"size computed\")\n        return 3\n    def m(self):\n        return size\n" ++
        "C().m()\n", false),
      ("lastExcAtExit", "import atexit, sys\n" ++
        "atexit.register(lambda: print(\"last\", type(sys.last_exc).__name__))\nraise KeyError(\"k\")\n",
        true),
      ("flushBeforeReport", "import sys\nclass C:\n    def __dir__(self):\n" ++
        "        sys.stdout.buffer.write(b\"dir bytes\\n\")\n        return []\nprint(\"a\")\nC().missing\n",
        true),
      ("exitClassTrick", "class E(Exception):\n    __class__ = SystemExit\n    code = None\n" ++
        "    def __getattr__(self, name):\n        print(\"looked up\", name)\n" ++
        "        raise AttributeError(name)\nraise E\n", false),
      ("exitCodeSwitchesStderr", "import sys, atexit\nclass Bye(SystemExit):\n    @property\n" ++
        "    def code(self):\n        sys.stderr = sys.stdout\n        return \"bye\"\n" ++
        "atexit.register(print, \"atexit\")\nraise Bye\n", true),
      ("stdoutFlushShadowed", "import sys\nraw = sys.stdout.buffer.raw\n" ++
        "sys.stdout.flush = lambda: raw.write(b\"stdout flush called\\n\")\n" ++ hi, true),
      ("fileDeleted", "import atexit\n__file__ = \"mine\"\n" ++
        "atexit.register(lambda: print(globals().get(\"__file__\")))\n", true),
      ("modulesRebound", "import sys, threading\n" ++
        "threading._register_atexit(print, \"threading exit callback\")\nsys.modules = {}\n", true),
      ("unraisableToStdout", "import sys, threading\nsys.stderr = sys.stdout\n" ++
        "def boom(): raise RuntimeError(\"cb\")\nthreading._register_atexit(boom)\n" ++ hi, true),
      ("syntaxErrorMsg", "class E(SyntaxError):\n    @property\n    def msg(self):\n" ++
        "        print(\"msg read\")\n        return \"m\"\nraise E(\"x\")\n", false),
      ("errWrite", "import sys\nw0 = sys.stderr.write\ndef w(s):\n    print(\"W\")\n" ++
        "    return w0(s)\nsys.stderr.write = w\n" ++ hi ++ "raise ValueError(\"v\")\n", true),
      ("exitPlain", "import sys\nprint(\"hi\")\nsys.exit(3)\n", true),
      ("exitObject", "import sys\nclass C:\n    def __str__(self):\n        print(\"str\")\n" ++
        "        return \"c\"\n" ++ hi ++ "sys.exit(C())\n", true),
      ("stderrReplaced", "import sys\nclass E:\n    def write(self, s):\n        return len(s)\n" ++
        "    def flush(self):\n        print(\"stderr flushed\")\nsys.stderr = E()\n" ++ hi, true),
      -- The tracer reads `sys` through its namespace after the program, as CPython's C code does, so
      -- a class that the program gave `sys` doesn't run.
      ("sysClass", "import sys\nclass M(type(sys)):\n    def __getattribute__(self, name):\n" ++
        "        if name == \"stdout\":\n            print(\"sys.stdout read\")\n" ++
        "        return super().__getattribute__(name)\nsys.__class__ = M\n" ++ hi, true)] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let (plain, r) ← runBoth python prog
    unless r.exitCode == 0 && (cutOf r.stdout).1.isSome == mark && agreesWith plain.stdout r.stdout do
      throw <| .userError s!"TraceScriptTest: {name}: python FILE printed {plain.stdout.quote}, \
        exit code {r.exitCode}, the trace is:\n{r.stdout}{r.stderr}"
  IO.println "TraceScriptTest: the report of an uncaught exception runs as in python FILE"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- Known differences of the tracer's in-process run from `python FILE`, pinned until the tracer
  -- runs the program as `python FILE` itself: the tracer has imported `hashlib`, the program's
  -- module has no `__file__`, the tracer's frames lower the recursion depth that the program
  -- reaches by 2 and the C recursion limit by 3, its `sys.stdout` has no file descriptor, and a
  -- flush at the deepest depth raises `RecursionError`.  Its `__builtins__` is the builtins
  -- module, as in `python FILE`.
  let prog := dir / "inProcess.py"
  IO.FS.writeFile prog ("import sys\nprint(\"hashlib\" in sys.modules, \"__file__\" in globals(), " ++
    "type(__builtins__).__name__)\ndef d(n):\n    try:\n        return d(n + 1)\n" ++
    "    except RecursionError:\n        return n\nprint(d(0))\ntry:\n    print(sys.stdout.fileno())\n" ++
    "except Exception as e:\n    print(type(e).__name__)\n")
  let (plain, r) ← runBoth python prog
  unless plain.stdout == "False True module\n998\n1\n" && r.exitCode == 0 &&
      stdoutOf r.stdout == some "True False module\n996\nUnsupportedOperation\n" do
    throw <| .userError s!"TraceScriptTest: inProcess: python FILE printed {plain.stdout.quote}, \
      exit code {r.exitCode}, the trace is:\n{r.stdout}{r.stderr}"
  -- At the deepest depth that the program reaches, a flush of `sys.stdout` raises
  -- `RecursionError`, since the capture's `write` is a Python frame.
  let deep := dir / "deepFlush.py"
  IO.FS.writeFile deep ("def f(n):\n    if n == 0:\n        print(\"x\", flush=True)\n" ++
    "        return\n    f(n - 1)\nf(996)\nprint(\"done\")\n")
  let (plain, r) ← runBoth python deep
  unless plain.stdout == "x\ndone\n" && r.exitCode == 0 && (cutOf r.stdout).1.isNone &&
      ((r.stdout.splitOn "--- outcome\nraised RecursionError").length > 1) do
    throw <| .userError s!"TraceScriptTest: deepFlush: python FILE printed {plain.stdout.quote}, \
      exit code {r.exitCode}, the trace is:\n{r.stdout}{r.stderr}"
  -- The C recursion limit is 3 levels lower: nested lists compare to a smaller depth.
  let cLimit := dir / "cLimit.py"
  IO.FS.writeFile cLimit ("def nest(d):\n    x = []\n    for _ in range(d):\n        x = [x]\n" ++
    "    return x\nlo, hi = 9900, 10100\nwhile lo < hi:\n    mid = (lo + hi + 1) // 2\n" ++
    "    try:\n        nest(mid) == nest(mid)\n        lo = mid\n    except RecursionError:\n" ++
    "        hi = mid - 1\nprint(lo)\n")
  let (plain, r) ← runBoth python cLimit
  unless plain.stdout == "9997\n" && r.exitCode == 0 && stdoutOf r.stdout == some "9994\n" do
    throw <| .userError s!"TraceScriptTest: cLimit: python FILE printed {plain.stdout.quote}, \
      exit code {r.exitCode}, the trace is:\n{r.stdout}{r.stderr}"
  -- The collector runs at other points than in `python FILE`, since the tracer's allocations shift
  -- its counts, so cyclic garbage collected during the run prints at another point, inside the
  -- part of the output that the trace claims is `python FILE`'s.  SemDiff would fail on it if the
  -- semantics agreed with `python FILE`; today the semantics stops with a gap on any class with
  -- `__del__`.
  let gcProg := dir / "gcTiming.py"
  IO.FS.writeFile gcProg ("class C:\n    def __init__(self, i):\n        self.i = i\n" ++
    "        self.me = self\n    def __del__(self):\n        print(\"collected\", self.i)\n" ++
    "for i in range(3000):\n    C(i)\n    if i % 500 == 0:\n        print(\"at\", i)\ndel C\n")
  let (plain, r) ← runBoth python gcProg
  unless r.exitCode == 0 && !agreesWith plain.stdout r.stdout do
    throw <| .userError s!"TraceScriptTest: gcTiming: python FILE printed {plain.stdout.quote}, \
      exit code {r.exitCode}, the trace is:\n{r.stdout}{r.stderr}"
  IO.println "TraceScriptTest: the known differences of the in-process run stay as pinned"

#eval withPython312 fun python => IO.FS.withTempDir fun dir => do
  -- The tracer's known differences from `python FILE` that no line marks give no wrong agree only
  -- because the semantics stops with a gap on each, or the translator rejects it.  Each one's
  -- verdict is pinned, so that a change that makes the semantics run such a program fails here
  -- first, before it can agree with a trace that isn't `python FILE`'s.
  let nest := "def nest(d):\n    x = []\n    for _ in range(d):\n        x = [x]\n    return x\n"
  -- The tracer checks a module of the program's own for the runtime as it checks the program, and
  -- reads it only from source; the semantics gaps on importing one.
  IO.FS.writeFile (dir / "localhelper.py") "n = 1\n"
  for (name, src, want) in [
      ("noFile", "print(__file__)\n",
        "gap | the translator does not support module attribute __file__"),
      ("dirNoFile", "print(sorted(dir()))\n", "gap | built-in dir is not modelled yet"),
      ("helpClass", "# A comment.\nclass A:\n    pass\nhelp(A)\n",
        "gap | built-in help is not modelled yet"),
      ("recursionDepth", "def d(n):\n    try:\n        return d(n + 1)\n" ++
        "    except RecursionError:\n        return n\nprint(d(0))\n",
        "gap | Python call depth over 900"),
      ("cLimit", nest ++ "print(nest(9995) == nest(9995))\n",
        "gap | a C recursion depth over 9000"),
      ("deepFlush", "def f(n):\n    if n == 0:\n        print(\"x\", flush=True)\n" ++
        "        return\n    f(n - 1)\nf(996)\nprint(\"done\")\n",
        "gap | Python call depth over 900"),
      ("stdoutFileno", "import argparse\nprint(argparse.FileType(\"w\")(\"-\").fileno())\n",
        "gap | import of module argparse is not modelled yet"),
      ("gcTiming", "class C:\n    def __init__(self, i):\n        self.me = self\n" ++
        "    def __del__(self):\n        print(\"collected\")\nfor i in range(3000):\n    C(i)\n",
        "gap | a class with a finalizer is not modelled yet"),
      ("identityHash", "class A: pass\nclass B: pass\nclass C: pass\n" ++
        "print([c.__name__ for c in {A, B, C}])\n",
        "gap | a slot of a set whose layout is inexact"),
      ("identityOrder", "def f(): pass\ndef g(): pass\nprint(id(f) < id(g))\n",
        "gap | built-in id is not modelled yet"),
      ("frameWalk", "import enum\nE = enum.Enum._create_(\"E\", \"A B\")\nprint(E.__module__)\n",
        "gap | import of module enum is not modelled yet"),
      ("importedModules", "import copy\nprint(len(copy.dispatch_table))\n",
        "gap | import of module copy is not modelled yet"),
      ("importedModulesDataclass", "from dataclasses import dataclass\n@dataclass\nclass P:\n" ++
        "    __module__ = \"hashlib\"\n    x: \"ClassVar[int]\" = 1\nprint(P())\n",
        "gap | a dataclass whose __module__ is not a loaded module is not modelled yet"),
      ("importedModulesHints", "import typing\nclass P:\n    __module__ = \"hashlib\"\n" ++
        "    x: \"sha256\"\nprint(typing.get_type_hints(P))\n",
        "gap | the attribute typing.get_type_hints is not modelled yet"),
      ("interned", "import typing\ns = \"file\"\ns += \"_digest\"\n" ++
        "P = typing.NamedTuple(\"P\", [(s, int)])\nprint(P._fields[0] is s)\n",
        "gap | the functional form of NamedTuple is not modelled yet"),
      ("abcToken", "import dataclasses\nprint(dataclasses.abc.get_cache_token())\n",
        "gap | the attribute dataclasses.abc is not modelled yet"),
      ("localModule", "import localhelper\nprint(localhelper.n)\n",
        "gap | import of module localhelper is not modelled yet"),
      ("seedSample", "print(list({\"a\", \"b\"}))\n",
        "gap | a slot of a set whose layout is inexact")] do
    let prog := dir / s!"{name}.py"
    IO.FS.writeFile prog src
    let r ← trace python prog
    let v ← SemDiff.verdict name prog r.stdout none
    let got := match v with
      | .ok (.gap m) => s!"gap | {m}"
      | .ok _ => "no gap"
      | .error e => s!"fails: {(e.splitOn "\n").head!}"
    unless got == want do
      throw <| .userError s!"TraceScriptTest: {name}: the verdict is {got.quote}, the trace is:\n\
        {r.stdout}{r.stderr}"
  -- The translator decodes a coding line too, where `python FILE` doesn't, so it drops the line
  -- that hz's "~" joins to the coding line: the test fails on this program, visibly, until the
  -- translator reads the coding line as `python FILE` does.
  let hz := dir / "hzLine.py"
  IO.FS.writeFile hz "# coding: hz ~\nprint(1)\nprint(2)\n"
  let r ← trace python hz
  let got := match ← SemDiff.verdict "hzLine" hz r.stdout none with
    | .ok _ => "no failure"
    | .error e => s!"fails: {(e.splitOn "\n").head!}"
  unless got == "fails: hzLine: the traces differ" do
    throw <| .userError s!"TraceScriptTest: hzLine: the verdict is {got.quote}, the trace is:\n\
      {r.stdout}{r.stderr}"
  -- The translator decodes an idna file whole, so it runs one whose part `python FILE` rejects.
  let idna := dir / "idnaPart.py"
  IO.FS.writeFile idna ("# coding: idna\nprint(1)\n# " ++ String.ofList (List.replicate 1100 'x') ++
    "\n")
  let r ← trace python idna
  let got := match ← SemDiff.verdict "idnaPart" idna r.stdout none with
    | .ok _ => "no failure"
    | .error e => s!"fails: {(e.splitOn "\n").head!}"
  unless got == "fails: idnaPart: CPython reports a syntax error, but the program runs" do
    throw <| .userError s!"TraceScriptTest: idnaPart: the verdict is {got.quote}, the trace is:\n\
      {r.stdout}{r.stderr}"
  IO.println "TraceScriptTest: the known differences that no line marks give a gap"

end StrataPython.TraceScriptTest
