/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Dyn.TestUtil

/-! # The translator does not take quadratic time in the branches of a function

Runs `pydyn dyn` on a module of 5,000 statements `if x: y_i = i` and on one of 20,000, both
parsed to Python Ion files first.  Each run must succeed within 600 seconds and print one
`branch` per `if`.  It runs `.lake/build/bin/pydyn` and imports modules of
`StrataPythonTest`, so build both first.

Only with `DYN_SCALE_TIME=1` does it time them, as `StrataDynTest/ScaleTest.lean` does: timing
on a loaded shared build host is not reliable enough for a build, so a build runs each module
once and times nothing.  Run the timed test as
`DYN_SCALE_TIME=1 lake env lean StrataPythonTestExtra/DynTranslateScaleTest.lean`.  Timed, it
runs the modules in turns, up to three times each, and fails if the larger one's shortest run
takes 7 times as much CPU time as the smaller one's, or more.  When the translator is linear in
the branches, the larger module takes about 5 times as much CPU time (the builder's checks grow
a little faster than linearly); when it is quadratic, about 9 to 16 times as much.  So the test
does not depend on how fast the machine is.  It fails if translating a statement copies a
structure that grows with the function, such as the set of the jump targets so far.

It measures the CPU time of `pydyn` with Python's `getrusage`, not the time on the clock.  It
doesn't run the translator in Lean's interpreter: interpreted, the translator's own steps are so
slow that the copies hide among them.
-/

namespace StrataPython.DynTranslateScaleTest

open StrataPython (withPython)
open StrataPython.Dyn.TestUtil (compilePython)

/-- Run the command given as its arguments, and print its exit code, the number of `branch(` in
its output, and the CPU time it took, in milliseconds. -/
private meta def cpuTime : String :=
  "import resource, subprocess, sys\n\
   r = subprocess.run(sys.argv[1:], stdout=subprocess.PIPE, timeout=600)\n\
   u = resource.getrusage(resource.RUSAGE_CHILDREN)\n\
   print(r.returncode, r.stdout.decode().count('branch('), round(1000 * (u.ru_utime + u.ru_stime)))\n"

/-- The module `x = 0`, then `if x: y_i = i` for each `i < n`. -/
private meta def ifs (n : Nat) : String := Id.run do
  let mut s := "x = 0\n"
  for i in [0:n] do
    s := s ++ s!"if x:\n    y{i} = {i}\n"
  return s

/-- The CPU time, in milliseconds, of `pydyn dyn ion`, which must succeed and print `n`
branches. -/
private meta def timeRun (pythonCmd ion : System.FilePath) (n : Nat) : IO Nat := do
  let out ← IO.Process.output
    { cmd := pythonCmd.toString,
      args := #["-c", cpuTime, ".lake/build/bin/pydyn", "dyn", ion.toString] }
  let [code, branches, ms] := (out.stdout.trimAscii.toString.splitOn " ").map String.toNat?
    | throw <| .userError s!"unexpected output: {out.stdout}{out.stderr}"
  unless code == some 0 && branches == some n do
    throw <| .userError s!"pydyn on {n} ifs: exit code {code}, {branches} branches"
  let some ms := ms | throw <| .userError s!"unexpected output: {out.stdout}"
  return ms

#guard_msgs in
#eval withPython fun pythonCmd => IO.FS.withTempDir fun dir => do
  let small := 5000
  let large := 4 * small
  let mut ions : Array System.FilePath := #[]
  for n in [small, large] do
    let py := dir / s!"ifs_{n}.py"
    IO.FS.writeFile py (ifs n)
    ions := ions.push (← compilePython pythonCmd py dir)
  unless (← IO.getEnv "DYN_SCALE_TIME") == some "1" do
    discard <| timeRun pythonCmd ions[0]! small
    discard <| timeRun pythonCmd ions[1]! large
    return
  -- Up to three rounds, each running the smaller module, then the larger.  It compares the
  -- shortest time of each so far, and stops as soon as their ratio is below 7.  Taking turns
  -- means that a change of the load on the machine slows both modules alike.
  let mut tSmall : Option Nat := none
  let mut tLarge : Option Nat := none
  for _ in [0:3] do
    let s ← timeRun pythonCmd ions[0]! small
    let l ← timeRun pythonCmd ions[1]! large
    let s := (tSmall.map (min s)).getD s
    let l := (tLarge.map (min l)).getD l
    if l < 7 * s then return
    tSmall := some s
    tLarge := some l
  throw <| .userError s!"{large} ifs took \
    {(tLarge.getD 0).toFloat / (tSmall.getD 1).toFloat} times as much CPU time as {small}"

end StrataPython.DynTranslateScaleTest
