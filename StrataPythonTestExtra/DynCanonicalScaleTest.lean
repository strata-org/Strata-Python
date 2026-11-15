/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! # The canonical form of a function with many loops, in work that grows with its size

Counts the work of the canonical form's computation in heartbeats, as `pydyn canonical --time`
reports them, on three shapes:
a function of sequential `for` loops, each with a `break` and a `return`; a function of
sequential outer loops, each holding an inner loop with a `break` and a `return`; and a function
of sequential loops that never jump back to their head, each a `for` loop whose body returns.
A heartbeat is one constructor cell that the computation allocates, so the count is the same on
every run of the same file.  For each shape, four times the loops must take less than six times
the heartbeats: the pass gives about four here, growth in n log n at most five, and quadratic
growth sixteen.
Heartbeats do not count arrays, strings or closures.  So they miss a scan that allocates nothing,
and a copy of an array or a map whose in-place update was lost.  Only timing sees those, and timing
on a shared builder is not reliable enough for `lake test`.  So with `CANON_SCALE_TIME=1` only,
each shape is also timed in CPU time, where `pydyn canonical --time` reports it, and in wall-clock
time otherwise: each small run is compared with the large run right after it, and in at least two
of the three pairs four times the loops must take less than ten times as long.
Every run must finish within 600 seconds, so that a hang fails the test, and the test stops at the
first run that does not.  It needs the built `pydyn` and a CPython with `PYTHON` set, as the build
sets it. -/

namespace StrataPython.DynCanonicalScaleTest

/-- The directory for the generated programs. -/
private meta def dir : System.FilePath := ".lake" / "build" / "canonical-scale"

/-- A function of `n` sequential `for` loops, each with a `break` and a `return`. -/
private meta def flat (n : Nat) : String :=
  "def f(xs, x):\n" ++ String.join ((List.range n).map fun i =>
    s!"    for v{i} in xs:\n        if c(v{i}): break\n        if c(x): return v{i}\n") ++
    "    return 0\n"

/-- A function of `n` sequential outer loops, each holding an inner loop with a `break` and a
`return`. -/
private meta def nested (n : Nat) : String :=
  "def f(xs, x):\n" ++ String.join ((List.range n).map fun i =>
    s!"    for v{i} in xs:\n        for w{i} in xs:\n            if c(w{i}): break\n" ++
    s!"            if c(x): return w{i}\n") ++
    "    return 0\n"

/-- A function of `n` sequential `for` loops, each of which returns at once, so that no back
edge enters its head. -/
private meta def noBack (n : Nat) : String :=
  "def f(xs, x):\n" ++ String.join ((List.range n).map fun _ =>
    "    for v in xs:\n        return v\n") ++ "    return 0\n"

/-- The longest that one run of `pydyn canonical` may take, in seconds. -/
private meta def limit : Nat := 600

/-- The heartbeats and the milliseconds that `pydyn canonical --time` reports for the file
`path`, or why it failed. -/
private meta def measure (path : System.FilePath) : IO (Except String (Nat × Nat)) := do
  let out ← IO.Process.output
    { cmd := "timeout"
      args := #[toString limit, ".lake/build/bin/pydyn", "canonical", "--time", path.toString] }
  if out.exitCode == 124 then
    throw <| IO.userError s!"DynCanonicalScaleTest: {path}: pydyn canonical did not finish within \
      {limit} seconds"
  if out.exitCode != 0 then
    return .error s!"{path}: pydyn canonical exited with {out.exitCode}"
  if (out.stdout.splitOn "-- not canonical").length > 1 then
    return .error s!"{path}: a function was not put in canonical form"
  let before (key : String) : Option Nat :=
    (out.stderr.splitOn key)[0]? >>= fun t => (t.splitOn " ").getLast? >>= String.toNat?
  let after (key : String) : Option Nat :=
    (out.stderr.splitOn key)[1]? >>= fun t => (t.splitOn " ms")[0]? >>= String.toNat?
  match before " heartbeats", after "cpu " <|> after "canonical: " with
  | some hb, some ms => return .ok (hb, ms)
  | _, _ => return .error s!"{path}: no heartbeats or time in pydyn's output: {out.stderr}"

/-- The heartbeats of one run on each of the files `ps` and `pl`. -/
private meta def heartbeats (ps pl : System.FilePath) : IO (Except String (Nat × Nat)) := do
  match ← measure ps, ← measure pl with
  | .ok (a, _), .ok (b, _) => return .ok (a, b)
  | .error e, _ | _, .error e => return .error e

/-- Three pairs of timed runs on the files `ps` and `pl`: each pair is a run on `ps` and the run
on `pl` right after it. -/
private meta def timePairs (ps pl : System.FilePath) : IO (Except String (Array (Nat × Nat))) := do
  let mut pairs := #[]
  for _ in [0:3] do
    match ← measure ps, ← measure pl with
    | .ok (_, a), .ok (_, b) => pairs := pairs.push (a, b)
    | .error e, _ | _, .error e => return .error e
  return .ok pairs

#eval show IO Unit from do
  IO.FS.createDirAll dir
  let timed := (← IO.getEnv "CANON_SCALE_TIME") == some "1"
  let mut failures := #[]
  for (shape, gen, n) in [("flat", flat, 400), ("nested", nested, 200), ("noback", noBack, 400)] do
    let ps := dir / s!"{shape}{n}.py"
    let pl := dir / s!"{shape}{4 * n}.py"
    IO.FS.writeFile ps (gen n)
    IO.FS.writeFile pl (gen (4 * n))
    match ← heartbeats ps pl with
    | .ok (a, b) =>
      IO.println s!"DynCanonicalScaleTest: {shape}, heartbeats for {n}/{4 * n} loops: {a}/{b}"
      if b ≥ 6 * max a 1 then
        failures := failures.push
          s!"{shape}: {4 * n} loops took {b} heartbeats, at least six times the {a} of {n}"
    | .error e => failures := failures.push e
    if timed then
      match ← timePairs ps pl with
      | .ok pairs =>
        let shown := ", ".intercalate (pairs.toList.map fun (a, b) => s!"{a}/{b}")
        IO.println s!"DynCanonicalScaleTest: {shape}, ms for {n}/{4 * n} loops: {shown}"
        if (pairs.filter fun (a, b) => b ≥ 10 * max a 1).size ≥ 2 then
          failures := failures.push
            s!"{shape}: in at least two of the pairs {shown}, {4 * n} loops took at least ten \
              times as long as {n}"
      | .error e => failures := failures.push e
  unless failures.isEmpty do
    throw <| IO.userError s!"DynCanonicalScaleTest: {failures.size} failure(s): \
      {"; ".intercalate failures.toList}"

end StrataPython.DynCanonicalScaleTest
