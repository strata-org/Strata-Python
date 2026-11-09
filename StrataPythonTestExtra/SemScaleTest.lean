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
a tuple of a million members, and an empty `str` repeated `2 ** 40` times.  Each run takes about 2 seconds, and the test fails if
one takes more than 30 seconds; a store or a container that copied itself on each write would take
minutes.
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
  ("empty str repetition", "s = '' * 2 ** 40\n", "s = ''")]

-- `pydyn run` parses the program with Python, so the test needs it, as the other tests do.
#eval StrataPython.withPython fun _ => do
  IO.FS.withTempDir fun dir => do
    for (name, program, expected) in programs do
      let file := dir / s!"{name.replace " " "_"}.py"
      IO.FS.writeFile file program
      let start ← IO.monoMsNow
      let r ← IO.Process.output { cmd := SemDiff.pydynPath.toString, args := #["run", file.toString] }
      let ms := (← IO.monoMsNow) - start
      unless r.exitCode == 0 && ((r.stdout.splitOn "\n").contains expected) do
        throw <| .userError s!"SemScaleTest: the {name} run failed:\n{r.stderr}"
      IO.println s!"SemScaleTest: {name} {ms} ms"
      if ms > 30000 then
        throw <| .userError s!"SemScaleTest: the {name} run took {ms} ms, more than 30000"

end StrataPython.SemScaleTest
