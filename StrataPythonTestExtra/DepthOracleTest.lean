/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python

/-! # The depth tests' depths are CPython's

Each `StrataPythonTest/Dyn/sem_modules/gap_depth_*.py` runs a recursion to a depth where the model
must stop with a gap ("Python call depth over 900"), which `SemDiffTest` checks. That depth is the
first one where CPython raises `RecursionError` when 100 Python frames sit below the program, the
most below which the semantics stays below CPython's limit (the trust about the caller's stack
allows 97). Since the model counts the program's frames, its module frame included, from 1 and stops
past 900, a native that charges fewer frames than CPython stops after that depth and fails
`SemDiffTest`. This test runs each program in the pinned CPython 3.12 with those 100 frames below
it, under `-S` (no `site` import, so that a module's first import is the program's, as in the
model), at its depth and one level shallower, and fails unless CPython raises at its depth and runs
one level shallower. So a CPython release that pushes a frame more inside `typing`, `dataclasses` or
the named tuples fails here, rather than leaving a test whose depth is no longer CPython's.

A program's depth is the argument of its last call `f(N)` or `make(N)`.
-/

namespace StrataPython.DepthOracleTest

/-- A Python program that runs the program in `sys.argv[2]` with exactly `int(sys.argv[1])` Python
frames below its module frame. -/
private meta def outside : String :=
  "import sys\n\
   n = int(sys.argv[1]); prog = sys.argv[2]\n\
   code = compile(open(prog).read(), prog, 'exec')\n\
   def r(k):\n\
   \x20   if k == 0:\n\
   \x20       f, d = sys._getframe(0), 0\n\
   \x20       while f is not None:\n\
   \x20           d += 1; f = f.f_back\n\
   \x20       assert d == n, d\n\
   \x20       exec(code, {'__name__': '__main__'})\n\
   \x20   else:\n\
   \x20       r(k - 1)\n\
   r(n - 2)\n"

/-- The text before the argument of the last call `f(` or `make(` in `src`, the argument, and the
text after it. -/
private meta def lastCall (src : String) : Option (String × Nat × String) :=
  let split (call : String) : Option (String × Nat × String) :=
    match src.splitOn call with
    | [] | [_] => none
    | parts =>
      let rest := (parts.getLast!).toList
      let digits := rest.takeWhile Char.isDigit
      match (String.ofList digits).toNat? with
      | some n => some (call.intercalate parts.dropLast ++ call, n, String.ofList (rest.drop digits.length))
      | none => none
  match split "    f(", split "    make(" with
  | some a, some b => some (if a.1.length ≥ b.1.length then a else b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

#eval StrataPython.withPython fun python => do
  let ver ← IO.Process.output { cmd := python.toString, args := #["-c", "import sys; print(sys.version_info[:2])"] }
  unless ver.stdout.trimAscii.toString == "(3, 12)" do
    throw <| .userError s!"DepthOracleTest: needs CPython 3.12, but {python} is {ver.stdout.trimAscii.toString}"
  let dir : System.FilePath := "StrataPythonTest" / "Dyn" / "sem_modules"
  let files := (← dir.readDir).filter fun e =>
    e.fileName.startsWith "gap_depth_" && e.fileName.endsWith ".py"
  if files.isEmpty then throw <| .userError "DepthOracleTest: no gap_depth_*.py program"
  IO.FS.withTempDir fun tmp => do
    let driver := tmp / "outside.py"
    IO.FS.writeFile driver outside
    let mut checked := 0
    for e in files.qsort (·.fileName < ·.fileName) do
      let src ← IO.FS.readFile e.path
      let some (pre, n, post) := lastCall src
        | throw <| .userError s!"DepthOracleTest: {e.fileName} has no call f(N) or make(N)"
      let run (depth : Nat) : IO String := do
        let file := tmp / e.fileName
        IO.FS.writeFile file (pre ++ toString depth ++ post)
        let r ← IO.Process.output
          { cmd := python.toString, args := #["-S", driver.toString, "100", file.toString] }
        pure r.stdout.trimAscii.toString
      let at_ ← run n
      let below ← run (n - 1)
      unless at_.endsWith "RecursionError" do
        throw <| .userError
          s!"DepthOracleTest: {e.fileName}: CPython doesn't raise at depth {n} with 100 outside frames; \
            it printed {at_}"
      unless below.endsWith "ok" do
        throw <| .userError
          s!"DepthOracleTest: {e.fileName}: CPython doesn't run at depth {n - 1} with 100 outside frames; \
            it printed {below}"
      checked := checked + 1
    IO.println s!"DepthOracleTest: {checked} depths are CPython's first raising depth"

end StrataPython.DepthOracleTest
