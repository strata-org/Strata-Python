/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.SemDiff
meta import StrataPythonTest.Util.Python

/-! # Attribute reads of user-made values against CPython

For each sample of `StrataPythonTest/Dyn/hasattr/expected.txt` (a value that
`StrataPythonTest/Dyn/hasattr/prelude.py` makes: instances, classes, methods, `property`,
`staticmethod`, `classmethod` and `super` objects, a class with a metaclass) and each name of the
union of all samples' `dir`s, `pydyn run` reads `sample.name` inside a `try` that catches
`AttributeError`, and the result must be CPython 3.12's `hasattr`. A run that stops with a gap
starts again after the name it stopped at, so every name is read. The test fails on any
disagreement, and pins the number of agreeing names and of gaps per sample in
`StrataPythonTest/Dyn/hasattr/summary.txt`; `HASATTR_UPDATE=1` rewrites it. Regenerate
`expected.txt` with `gen_hasattr_user.py` and CPython 3.12.
-/

namespace StrataPython.HasattrUserTest

private meta def dir : System.FilePath := "StrataPythonTest" / "Dyn" / "hasattr"

/-- The program that reads `src.n` for each name `n` of `names`, numbered from `0`, after the
prelude: `@ k` before the `k`-th read, `R k True` or `R k False` after it, and `@ n` at the end. -/
private meta def program (prelude src : String) (names : Array String) : String := Id.run do
  let mut out := prelude
  for h : k in [:names.size] do
    out := out ++ s!"print('@', {k})\ntry:\n    ({src}).{names[k]}\n    print('R', {k}, True)\n" ++
      s!"except AttributeError:\n    print('R', {k}, False)\n"
  out ++ s!"print('@', {names.size})\n"

/-- The last `@ k` of the output `out`, and the results `R k b` it printed. -/
private meta def parse (out : String) : Option Nat × Array (Nat × Bool) := Id.run do
  let mut last := none
  let mut res := #[]
  for l in out.splitOn "\n" do
    match l.splitOn " " with
    | ["@", k] => last := k.toNat?
    | ["R", k, b] => if let some k := k.toNat? then res := res.push (k, b == "True")
    | _ => pure ()
  (last, res)

/-- For the sample `src` and its names with CPython's answers, the number of names that agree and
of gaps, or the disagreements. -/
private meta def runSample (prelude src : String) (expected : Array (String × Bool))
    (work : System.FilePath) : IO (Nat × Nat × Array String) := do
  let mut todo := (List.range expected.size).toArray
  let mut agree := 0
  let mut gaps := 0
  let mut bad := #[]
  while !todo.isEmpty do
    IO.FS.writeFile work (program prelude src (todo.map fun i => expected[i]!.1))
    let r ← IO.Process.output { cmd := SemDiff.pydynPath.toString, args := #["run", work.toString] }
    let some (out, rest) := SemDiff.splitOutput r.stdout |
      return (agree, gaps, bad.push s!"{src}: the run has no output section:\n{r.stdout}{r.stderr}")
    let (last, res) := parse out
    for (k, b) in res do
      if h : k < todo.size then
        let (n, want) := expected[todo[k]]!
        if b == want then agree := agree + 1
        else bad := bad.push s!"{src}.{n}: CPython {want}, the rules {b}"
    match last with
    | some l =>
      if l == todo.size then break
      -- The read of name `l` stopped the run: it must be a gap, never another ending.
      unless (rest.splitOn "\n").any (·.startsWith "--- gap ") do
        return (agree, gaps, bad.push s!"{src}.{expected[todo[l]!]!.1}: the run ended without a gap:\n{rest}")
      gaps := gaps + 1
      todo := todo.extract (l + 1) todo.size
    | none => return (agree, gaps, bad.push s!"{src}: the run stopped in the prelude:\n{rest}")
  return (agree, gaps, bad)

-- `pydyn run` parses the program with Python, so the test needs it, as the other tests do.
#eval StrataPython.withPython fun _ => do
  let update := (← IO.getEnv "HASATTR_UPDATE").isSome
  let prelude ← IO.FS.readFile (dir / "prelude.py")
  let mut samples : Array (String × Array (String × Bool)) := #[]
  for l in (← IO.FS.readFile (dir / "expected.txt")).splitOn "\n" do
    let [s, n, b] := (l.splitOn " | ") | continue
    let entry := (n, b == "true")
    match samples.findIdx? (·.1 == s) with
    | some i => samples := samples.modify i fun (s, es) => (s, es.push entry)
    | none => samples := samples.push (s, #[entry])
  let (summary, failures₀) ← IO.FS.withTempDir fun tmp => do
    let mut summary : Array String := #[]
    let mut failures : Array String := #[]
    for (src, expected) in samples do
      let (agree, gaps, bad) ← runSample prelude src expected (tmp / "work.py")
      summary := summary.push s!"{src} | {agree} agree | {gaps} gap"
      failures := failures ++ bad
    return (summary, failures)
  let mut failures := failures₀
  let text := "\n".intercalate summary.toList ++ "\n"
  let pinned := dir / "summary.txt"
  if update then IO.FS.writeFile pinned text
  else if (← pinned.pathExists) then
    if (← IO.FS.readFile pinned) != text then
      failures := failures.push s!"{pinned} differs; run with HASATTR_UPDATE=1:\n{text}"
  else failures := failures.push s!"missing {pinned}; run with HASATTR_UPDATE=1"
  IO.println s!"HasattrUserTest: {samples.size} samples"
  unless failures.isEmpty do
    for f in failures do IO.println f
    throw <| .userError s!"HasattrUserTest: {failures.size} failure(s)"

end StrataPython.HasattrUserTest
