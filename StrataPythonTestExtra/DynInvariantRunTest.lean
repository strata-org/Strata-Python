/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Dyn.TestUtil

/-! # Loop-invariant programs run unchanged on CPython

The translator drops the calls of the loop-invariant markers (`docs/PythonToDyn.md` §6.11). That
is faithful because the markers do nothing when CPython runs them. This test runs every
loop-invariant program of the translator's corpus, the `li_*` rows of
`StrataPythonTest/Dyn/dyn_tests.txt` with no expected rejection, with CPython and the marker
module `Python/pyhard/pyhard.py` on the module path. It compares the
program's output and exit status with `NAME.expected.out` beside `NAME.py`. Each program prints
what its loops compute, so a marker that did something would show.

Set `DYN_UPDATE=1` to rewrite the goldens.
-/

namespace StrataPython.DynInvariantRunTest

open StrataPython (withPython)
open StrataPython.Dyn.TestUtil (firstDiff)

private meta def listFile : System.FilePath := "StrataPythonTest" / "Dyn" / "dyn_tests.txt"

private meta def testDir : System.FilePath := "StrataPythonTest" / "Dyn" / "dyn_tests"

/-- The directory of the marker module. -/
private meta def pyhardDir : System.FilePath := "Python" / "pyhard"

/-- The suffix of a run golden. -/
private meta def goldenSuffix : String := ".expected.out"

/-- The loop-invariant programs of the list: the `li_` tests that are supported and expect no
rejection. -/
private meta def programs : IO (Array String) := do
  let mut names := #[]
  for line in (← IO.FS.readFile listFile).splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match (line.splitOn "|").map (·.trimAscii.toString) with
    | [path, "yes", ""] => if path.startsWith "li_" then names := names.push path
    | _ => pure ()
  return names

/-- Run `name.py` with `python`, with `pyhard` first on the module path: its output and
status. -/
private meta def run (python : System.FilePath) (name : String) : IO String := do
  let out ← IO.Process.output {
    cmd := python.toString, args := #["-I", "-B", "-c", runner, (testDir / s!"{name}.py").toString] }
  return s!"{out.stdout}exit {out.exitCode}\n"
where
  /-- `-I` keeps the `PYTHON*` variables, the program's directory and the current one off the
  module path, and the runner puts `Python/pyhard/` first and fails unless `import pyhard` loads
  `Python/pyhard/pyhard.py` and the module's only names that aren't dunders are the two markers,
  which the Python semantics' model of `pyhard` holds. It then puts the program's directory next,
  as `python FILE.py` does, so that a program can import another program module, and runs the
  program as `__main__`; `-B` keeps CPython from writing bytecode beside it. -/
  runner : String :=
    s!"import os, runpy, sys; d = os.path.abspath({repr pyhardDir.toString}); \
      sys.path.insert(0, d); import pyhard; \
      assert os.path.dirname(os.path.abspath(pyhard.__file__)) == d, pyhard.__file__; \
      assert sorted(n for n in vars(pyhard) if not n.startswith('__')) == ['OLD', 'loop_invariant']; \
      sys.path.insert(1, os.path.dirname(os.path.abspath(sys.argv[1]))); \
      runpy.run_path(sys.argv[1], run_name='__main__')"

#eval withPython fun python => do
  let update := (← IO.getEnv "DYN_UPDATE").isSome
  let names ← programs
  let mut failures : Array String := #[]
  for f in ← testDir.readDir do
    if f.fileName.endsWith goldenSuffix then
      unless names.contains (f.fileName.dropEnd goldenSuffix.length).toString do
        if update then IO.FS.removeFile f.path
        else failures := failures.push s!"{f.path}: golden for no loop-invariant program"
  for name in names do
    let out ← run python name
    let golden := testDir / s!"{name}{goldenSuffix}"
    if update then IO.FS.writeFile golden out
    else if !(← golden.pathExists) then failures := failures.push s!"{name}: missing {golden}"
    else if let some d := firstDiff out (← IO.FS.readFile golden) then
      failures := failures.push s!"{name}: differs from {golden} at {d}"
  IO.println s!"DynInvariantRunTest: {names.size} programs"
  if !failures.isEmpty then
    for f in failures do IO.println f
    throw <| IO.userError s!"DynInvariantRunTest: {failures.size} failure(s)"

end StrataPython.DynInvariantRunTest
