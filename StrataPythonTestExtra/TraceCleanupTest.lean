/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.SemDiff
meta import StrataPythonTest.Util.Python

/-! # The CPython tracer cleans up after the programs it runs

`StrataPythonTest/Dyn/trace.py` runs each program in a fresh directory and removes it afterwards.
The test runs the tracer in a root of its own (`STRATA_TRACE_ROOT`), so that it shares no directory
with another checkout or user, on two programs:
- `trace_cleanup_modes.py` leaves a read-only directory and an unreadable one, each with a nested
  one and files;
- `trace_cleanup_swap.py` replaces its directory with a symlink that points nowhere.
It runs each one twice, under two hash seeds, and the first one once more under the umask `0277`, so
that the second run must remove what the first one left, and the mode of a directory that a program
makes doesn't depend on the caller. After the runs, only lock files are left in the root.
An empty `STRATA_TRACE_ROOT` counts as unset: the test loads the tracer as a module, without running
it, and checks that its root is then the default. The tracer needs CPython 3.12, and
`SKIP_PYTHON_TESTS=1` skips the test.
-/

namespace StrataPython.TraceCleanupTest

/-- The trace of `trace_cleanup_modes.py`, the same under every hash seed.  It imports `os`, which
reaches the interpreter's runtime, so the trace is cut at the program's end. -/
meta def modesTrace : String := "--- stdout 5
done

--- outcome
ok
--- globals
__doc__ = None
__name__ = '__main__'
d = 'nr'
f = 'nr/inner/f'
mode = 0
os = <module object>
out = <TextIOWrapper object>
--- teardown after 5
"

/-- The trace of `trace_cleanup_swap.py`, whose directory shows as `<cwd>`. -/
meta def swapTrace : String := "--- stdout 5
done

--- outcome
ok
--- globals
__doc__ = None
__name__ = '__main__'
d = '<cwd>'
os = <module object>
--- teardown after 5
"

/-- Run the tracer on `program` with the hash seed `seed`, in the root `root`, under the umask
`umask` when one is given, and check that it gives `expected`. -/
meta def traceOnce (python root : System.FilePath) (program expected seed : String)
    (umask : Option String := none) : IO Unit := do
  let run := #[python.toString, SemDiff.traceScript.toString, program]
  let (cmd, args) := match umask with
    | some u => ("sh", #["-c", s!"umask {u} && exec \"$@\"", "sh"] ++ run)
    | none => (run[0]!, run.extract 1 run.size)
  let r ← IO.Process.output {
    cmd, args, env := #[("PYTHONHASHSEED", some seed), ("STRATA_TRACE_ROOT", some root.toString)] }
  unless r.exitCode == 0 && r.stdout == expected do
    throw <| .userError
      s!"TraceCleanupTest: {program} (seed {seed}) exited {r.exitCode}:\n{r.stdout}{r.stderr}"

/-- Run the tracer on both programs, in a fresh root, and check each trace and the cleanup. -/
meta def runTest : IO Unit := do
  if let some skip ← IO.getEnv "SKIP_PYTHON_TESTS" then
    if !skip.isEmpty then return
  let python ← StrataPython.findPython3 (minVersion := 12) (maxVersion := 12)
  IO.FS.withTempDir fun root => do
    let modes := "StrataPythonTestExtra/trace_cleanup_modes.py"
    let swap := "StrataPythonTestExtra/trace_cleanup_swap.py"
    for seed in ["0", "1"] do
      traceOnce python root modes modesTrace seed
      traceOnce python root swap swapTrace seed
    traceOnce python root modes modesTrace "0" (umask := some "0277")
    let left := (← root.readDir).filter fun e => !e.fileName.endsWith ".lock"
    unless left.isEmpty do
      throw <| .userError s!"TraceCleanupTest: left behind: {left.map (·.fileName)}"
  -- Loading the tracer runs no program: `main` runs only when the file is the script.
  let load := "import importlib.util as u, sys\n\
    s = u.spec_from_file_location('trace_mod', sys.argv[1])\n\
    m = u.module_from_spec(s)\n\
    s.loader.exec_module(m)\n\
    print(m.TRACE_ROOT)\n"
  let r ← IO.Process.output {
    cmd := python.toString, args := #["-I", "-B", "-c", load, SemDiff.traceScript.toString]
    env := #[("STRATA_TRACE_ROOT", some "")] }
  unless r.exitCode == 0 && r.stdout == "/tmp/strata-trace\n" do
    throw <| .userError s!"TraceCleanupTest: the root for an empty STRATA_TRACE_ROOT is \
      {r.stdout}{r.stderr}"
  IO.println "TraceCleanupTest: each run cleaned up, and an empty root is the default"

#eval runTest

end StrataPython.TraceCleanupTest
