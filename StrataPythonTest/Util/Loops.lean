/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import StrataPythonTest.Util.SemDiff
public meta import StrataPythonTest.Util.Python

/-! # Loops that must cost linear time

`run` runs `pydyn run` on each loop of a test, three times at 100,000 and three times at
1,000,000 iterations, and keeps the fastest run of each size, so that a slower run on a busy
machine doesn't count. For each loop it prints the time and the peak memory of both sizes and the
time of one iteration at 1,000,000. It fails if a run doesn't end with the outcome `ok`, or if
the fastest run of 1,000,000 iterations takes more than 12 times the fastest run of 100,000, as a
cost that grows quadratically would.
The runs take minutes, so it runs only when `SEM_LOOPS` is set; otherwise it prints that it
skipped.
-/

public meta section

namespace StrataPython.Loops

/-- A Python program that runs `pydyn run FILE` and prints its exit code, whether the run ended
with the outcome `ok` (not with a gap or out of fuel), and its peak memory in kB. -/
def rusage : String :=
  "import resource, subprocess, sys\n\
   r = subprocess.run(sys.argv[1:], capture_output=True)\n\
   ok = b'\\n--- outcome\\nok\\n' in r.stdout\n\
   print(r.returncode, int(ok), resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)\n"

/-- The time in ms, whether the run ended with exit code 0 and the outcome `ok`, and the peak
memory in kB of `pydyn run` on `program`. -/
def measure (test : String) (python dir : System.FilePath) (name program : String) :
    IO (Nat × Bool × Nat) := do
  let file := dir / s!"{name.replace " " "_"}.py"
  IO.FS.writeFile file program
  let start ← IO.monoMsNow
  let r ← IO.Process.output
    { cmd := python.toString, args := #["-c", rusage, SemDiff.pydynPath.toString, "run", file.toString] }
  let ms := (← IO.monoMsNow) - start
  match (r.stdout.trimAscii.toString.splitOn " ").map String.toNat? with
  | [some code, some ok, some kb] => return (ms, code == 0 && ok == 1, kb)
  | _ => throw <| .userError s!"{test}: no measure for {name}: {r.stdout}{r.stderr}"

/-- The fastest of three runs of `program`: its time in ms, whether all three ended with exit code
0 and the outcome `ok`, and the largest peak memory in kB. -/
def fastest (test : String) (python dir : System.FilePath) (name program : String) :
    IO (Nat × Bool × Nat) := do
  let (t, c, m) ← measure test python dir name program
  let mut best := (t, c, m)
  for _ in [0:2] do
    let (t', c', m') ← measure test python dir name program
    best := (min best.1 t', best.2.1 && c', max best.2.2 m')
  return best

/-- Runs the loops of the test `test`: `loops n` gives each loop's name and its program for `n`
iterations. -/
def run (test : String) (loops : Nat → List (String × String)) : IO Unit := do
  if (← IO.getEnv "SEM_LOOPS").isNone then
    IO.println s!"SEM_LOOPS not set; {test} skips its loops."
    return
  StrataPython.withPython fun python => IO.FS.withTempDir fun dir => do
    let mut failures : Array String := #[]
    for ((name, small), (_, large)) in (loops 100000).zip (loops 1000000) do
      let (t₁, c₁, m₁) ← fastest test python dir name small
      let (t₂, c₂, m₂) ← fastest test python dir name large
      if !c₁ || !c₂ then failures := failures.push s!"{name}: a run did not end with the outcome ok"
      IO.println s!"{test}: {name}: 100k {t₁} ms {m₁ / 1024} MB, 1M {t₂} ms {m₂ / 1024} MB, \
        {t₂} ns per iteration at 1M"
      if t₂ > 12 * t₁ then failures := failures.push s!"{name}: 1M took {t₂} ms, more than 12 times {t₁} ms"
    unless failures.isEmpty do
      throw <| .userError s!"{test}: {", ".intercalate failures.toList}"

end StrataPython.Loops

end
