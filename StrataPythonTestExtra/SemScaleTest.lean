/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.SemDiff
meta import StrataPythonTest.Util.Python

/-! # Loops of calls and container writes run fast

Runs `pydyn run` on loops of 200000 steps: calls that each allocate a kwargs dict and a list, and
writes that grow a dict, a list and a set, deletions that shrink a list, the iteration of a
non-ASCII `str`, a loop after many iterators of a non-ASCII `str` that stopped early, the walks of
a tuple of a million members, an empty `str` repeated `2 ** 40` times, indexing and growing a
non-ASCII `str`, the hash of a tuple of a million members, and the reprs of a tuple, a list and a
dict of 100,000 members, `<` of two tuples nested 800 deep, and `==` of two tuples that share their
parts 16 levels deep (sizes that currently run within the native stack, and costs that
docs/PythonToDyn.md §13.6 states).  Each run takes a few seconds of CPU time, and the test fails if
one takes more than 30 seconds of it; a store or a container that copied itself on each write would
take about a minute.  It also checks how one cost grows: `<` of two tuples that differ only
innermost, nested 1,000 deep, may take at most 4.5 times its time at 500 deep, as a cost in the
square of the depth does (CPython's), where one in its cube took 6.5 to 8.5 times in our runs.
It measures the CPU time of `pydyn`, not the time on the clock, so that a busy build host doesn't
make it fail.
-/

namespace StrataPython.SemScaleTest

/-- The loops, each with the line its run's globals must hold. -/
private meta def programs : List (String × String × String) := [
  ("calls", "def f():\n    return [1]\ni = 0\nwhile i < 200000:\n    x = f()\n    i = i + 1\n",
    "i = 200000"),
  ("dict", "d = {}\ni = 0\nwhile i < 200000:\n    d[i] = i\n    i = i + 1\nn = i\n",
    "n = 200000"),
  ("list", "l = []\ni = 0\nwhile i < 200000:\n    l += [i]\n    i = i + 1\nn = i\n",
    "n = 200000"),
  ("set", "s = {-1}\ni = 0\nwhile i < 200000:\n    s |= {i}\n    i = i + 1\nn = i\n",
    "n = 200000"),
  ("list deletion", "l = [0] * 200000\ni = 200000\nwhile i > 0:\n    del l[-1]\n    i = i - 1\n",
    "l = []"),
  ("non-ASCII str iteration", "s = 'é' * 200000\nn = 0\nfor c in s:\n    n = n + 1\n",
    "n = 200000"),
  ("stopped str iterators", "i = 0\nwhile i < 100000:\n    for c in 'éa':\n        break\n    i = i + 1\n\
    l = [0] * 100000\nn = 0\nfor x in l:\n    n = n + 1\n", "n = 100000"),
  ("long tuples", "t = (0,) * 1000000\na = t == t[:]\nb = 1 in t\nc = t < t[:]\n", "c = False"),
  ("empty str repetition", "s = '' * 2 ** 40\n", "s = ''"),
  ("non-ASCII str indexing", "s = 'é' * 100000\nn = 0\ni = 0\nwhile i < 100000:\n    \
    if s[i] == 'é':\n        n = n + 1\n    i = i + 1\n", "n = 100000"),
  ("str concatenation", "s = ''\ni = 0\nwhile i < 100000:\n    s += 'é'\n    i = i + 1\n\
    n = len(s)\ndel s\n", "n = 100000"),
  ("hash of a long tuple", "t = (0,) * 1000000\nr = len({t})\ndel t\n", "r = 1"),
  ("reprs of long containers", "t = (0,) * 100000\nl = [0] * 100000\nd = {}\ni = 0\n\
    while i < 100000:\n    d[i] = i\n    i = i + 1\na = len(repr(t))\nb = len(repr(l))\n\
    c = len(repr(d))\ndel t, l, d\n", "c = 1377780"),
  ("deep tuple comparison", "a = 0\nb = 0\ni = 0\nwhile i < 800:\n    a = (a,)\n    b = (b, 1)\n    \
    i = i + 1\nr = a < b\ndel a, b\n", "r = True"),
  ("shared tuples", "t = ()\ni = 0\nwhile i < 16:\n    t = (t, t)\n    i = i + 1\n\
    r = (t,) == (t,)\ndel t\n", "r = True")]

/-- A Python program that runs `pydyn run FILE`, then prints its exit code and its CPU time in ms
(user and system) on a first line, and its output after it. -/
private meta def cpuTime : String :=
  "import resource, subprocess, sys\n\
   r = subprocess.run(sys.argv[1:], capture_output=True)\n\
   u = resource.getrusage(resource.RUSAGE_CHILDREN)\n\
   sys.stdout.write(f'{r.returncode} {int((u.ru_utime + u.ru_stime) * 1000)}\\n')\n\
   sys.stdout.flush()\n\
   sys.stdout.buffer.write(r.stdout)\n\
   sys.stderr.buffer.write(r.stderr)\n"

/-- `<` of two tuples nested `d` deep that differ only innermost: CPython compares about `d²/2`
members. -/
private meta def sameShape (d : Nat) : String :=
  s!"a = ()\nb = (1,)\ni = 0\nwhile i < {d}:\n    a = (a,)\n    b = (b,)\n    i = i + 1\n\
    r = a < b\ndel a, b\n"

/-- The CPU time in ms of `pydyn run` on `program`, which it writes to a file in `dir`.  The run
must exit with 0, and its output must hold the line `expected`. -/
private meta def measure (python : System.FilePath) (dir : System.FilePath)
    (name program expected : String) : IO Nat := do
  let file := dir / s!"{name.replace " " "_"}.py"
  IO.FS.writeFile file program
  let r ← IO.Process.output
    { cmd := python.toString, args := #["-c", cpuTime, SemDiff.pydynPath.toString, "run", file.toString] }
  let lines := r.stdout.splitOn "\n"
  let (code, ms) ← match (lines.headD "").splitOn " " with
    | [c, t] => match c.toInt?, t.toNat? with
      | some code, some ms => pure (code, ms)
      | _, _ => throw <| .userError s!"SemScaleTest: no CPU time for the {name} run:\n{r.stdout}{r.stderr}"
    | _ => throw <| .userError s!"SemScaleTest: no CPU time for the {name} run:\n{r.stdout}{r.stderr}"
  unless code == 0 && (lines.drop 1).contains expected do
    throw <| .userError s!"SemScaleTest: the {name} run failed:\n{r.stderr}"
  IO.println s!"SemScaleTest: {name} {ms} ms of CPU time"
  return ms

-- `pydyn run` parses the program with Python, so the test needs it, as the other tests do.
#eval StrataPython.withPython fun python => do
  IO.FS.withTempDir fun dir => do
    for (name, program, expected) in programs do
      let ms ← measure python dir name program expected
      if ms > 30000 then
        throw <| .userError s!"SemScaleTest: the {name} run took {ms} ms of CPU time, more than 30000"
    let half ← measure python dir "same-shape tuples 500 deep" (sameShape 500) "r = True"
    let full ← measure python dir "same-shape tuples 1000 deep" (sameShape 1000) "r = True"
    if full * 2 > half * 9 then
      throw <| .userError s!"SemScaleTest: `<` of same-shape tuples took {full} ms at 1,000 deep and \
        {half} ms at 500 deep, more than 4.5 times"

end StrataPython.SemScaleTest
