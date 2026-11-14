/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.SemDiff
meta import StrataPythonTest.Util.Python

/-! # Eight loops cost linear time

Runs `pydyn run` on eight loops, at 100,000 and at 1,000,000 iterations: `print`, a `try` whose
`except` catches, a list append (`l += [i]`), `d[i] = i`, `del d[i]` (after the writes), an
attribute write, a call of a Python function, and a list comprehension.  For each loop it prints the time and the peak
memory of both runs and the time of one iteration at 1,000,000.  It fails if a run doesn't end
with the outcome `ok`, or if the run of 1,000,000 iterations takes more than 12 times the run of
100,000, as a cost that grows quadratically would.  The runs take a few minutes, so the test
runs only when `SEM_LOOPS` is set; otherwise it prints that it skipped.
-/

namespace StrataPython.SemLoopsTest

/-- Each loop's program for `n` iterations. -/
private meta def loops (n : Nat) : List (String × String) := [
  ("print", s!"for i in range({n}):\n    print(i)\n"),
  ("try and except", s!"for i in range({n}):\n    try:\n        raise ValueError\n    except ValueError:\n        pass\n"),
  ("list append", s!"l = []\nfor i in range({n}):\n    l += [i]\n"),
  ("dict write", s!"d = \{}\nfor i in range({n}):\n    d[i] = i\n"),
  ("dict deletion", s!"d = \{}\nfor i in range({n}):\n    d[i] = i\nfor i in range({n}):\n    del d[i]\n"),
  ("attribute write", s!"class A:\n    pass\no = A()\nfor i in range({n}):\n    o.x = i\n"),
  ("call", s!"def f(x):\n    return x\nfor i in range({n}):\n    f(i)\n"),
  ("comprehension", s!"l = [i + 1 for i in range({n})]\n")]

/-- A Python program that runs `pydyn run FILE` and prints its exit code, whether the run ended
with the outcome `ok` (not with a gap or out of fuel), and its peak memory in kB. -/
private meta def rusage : String :=
  "import resource, subprocess, sys\n\
   r = subprocess.run(sys.argv[1:], capture_output=True)\n\
   ok = b'\\n--- outcome\\nok\\n' in r.stdout\n\
   print(r.returncode, int(ok), resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)\n"

/-- The time in ms, whether the run ended with exit code 0 and the outcome `ok`, and the peak
memory in kB of `pydyn run` on `program`. -/
private meta def measure (python : System.FilePath) (dir : System.FilePath) (name program : String) :
    IO (Nat × Bool × Nat) := do
  let file := dir / s!"{name.replace " " "_"}.py"
  IO.FS.writeFile file program
  let start ← IO.monoMsNow
  let r ← IO.Process.output
    { cmd := python.toString, args := #["-c", rusage, SemDiff.pydynPath.toString, "run", file.toString] }
  let ms := (← IO.monoMsNow) - start
  match (r.stdout.trimAscii.toString.splitOn " ").map String.toNat? with
  | [some code, some ok, some kb] => return (ms, code == 0 && ok == 1, kb)
  | _ => throw <| .userError s!"SemLoopsTest: no measure for {name}: {r.stdout}{r.stderr}"

#eval show IO Unit from do
  if (← IO.getEnv "SEM_LOOPS").isNone then
    IO.println "SEM_LOOPS not set; skipping the eight loops."
    return
  StrataPython.withPython fun python => IO.FS.withTempDir fun dir => do
    let mut failures : Array String := #[]
    for ((name, small), (_, large)) in (loops 100000).zip (loops 1000000) do
      let (t₁, c₁, m₁) ← measure python dir name small
      let (t₂, c₂, m₂) ← measure python dir name large
      if !c₁ || !c₂ then failures := failures.push s!"{name}: a run did not end with the outcome ok"
      IO.println s!"SemLoopsTest: {name}: 100k {t₁} ms {m₁ / 1024} MB, 1M {t₂} ms {m₂ / 1024} MB, \
        {t₂} ns per iteration at 1M"
      if t₂ > 12 * t₁ then failures := failures.push s!"{name}: 1M took {t₂} ms, more than 12 times {t₁} ms"
    unless failures.isEmpty do
      throw <| .userError s!"SemLoopsTest: {", ".intercalate failures.toList}"

end StrataPython.SemLoopsTest
