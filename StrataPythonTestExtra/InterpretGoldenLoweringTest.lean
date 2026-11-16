/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.InterpretGolden.Generate
meta import StrataPythonTest.Util.Python

/-! ## Tests: an interpret golden whose case does not lower to Ion

A corpus case the Python front end cannot lower must fail the interpret golden under
both front ends, so a lowering regression cannot turn it green; a `.skip` sidecar is
the only way to opt a case out. Each test builds a scratch package root holding one
corpus file that `py_to_strata` rejects, with the real `Python/` directory linked in
so the compiler runs as it does for the corpus. -/

open StrataPython
open StrataPython.GoldenText
open StrataPython.InterpretGolden

/-- Run `k` on a scratch root whose corpus holds `<stem>.py`, a file `py_to_strata`
    cannot lower, with a `.skip` sidecar in both expectation sets when `skip` is set. -/
private meta def withUnlowerableCase (stem : String) (skip : Bool)
    (k : System.FilePath → IO Unit) : IO Unit := do
  let realRoot ← IO.currentDir
  IO.FS.withTempDir fun root => do
    let tests := root / "StrataPythonTest" / "tests"
    IO.FS.createDirAll tests
    IO.FS.writeFile (tests / (stem ++ ".py")) "def broken(:\n"
    for dir in ["expected_interpret", "expected_interpret_v1"] do
      let expectedDir := root / "StrataPythonTest" / dir
      IO.FS.createDirAll expectedDir
      if skip then
        IO.FS.writeFile (expectedDir / (stem ++ ".skip")) "not meant to run\n"
    -- `withTempDir`'s cleanup (`removeDirAll`) does not follow symlinks, so it removes
    -- this link and leaves the real `Python/` alone. Recheck on a toolchain upgrade.
    let ln ← IO.Process.output {
      cmd := "ln", args := #["-s", (realRoot / "Python").toString, (root / "Python").toString]
    }
    unless ln.exitCode == 0 do
      throw <| .userError s!"could not link Python/ into the scratch root: {ln.stderr}"
    k root

-- Without a `.skip`, the lowering failure fails each front end's pass.
#guard_msgs in
#eval withPython fun pythonCmd =>
  withUnlowerableCase "test_unlowerable" (skip := false) fun root => do
    for v2 in [false, true] do
      let failed ← try
          runOnePass pythonCmd root "test_unlowerable" v2
          pure none
        catch e => pure (some e.toString)
      match failed with
      | none => throw <| .userError s!"v2={v2}: an unlowerable case passed"
      | some msg =>
        unless hasSub msg "py_to_strata failed to lower" do
          throw <| .userError s!"v2={v2}: unexpected failure: {msg}"

-- With a `.skip` in each set, both passes skip the case.
#guard_msgs in
#eval withPython fun pythonCmd =>
  withUnlowerableCase "test_unlowerable" (skip := true) fun root => do
    for v2 in [false, true] do
      runOnePass pythonCmd root "test_unlowerable" v2

/-! ## Tests: which cause the lowering-failure message names

A test cannot choose the interpreter, so the message is checked as a function of the
compiler output and the Python minor version. Every message reports a failure. -/

private meta def parseFailureOut : String :=
  "Parse failure:\n  invalid syntax (test_x.py, line 1)\n"

private meta def checkCause (minor : Option Nat) (out : String) (want : String) : IO Unit := do
  let msg := loweringFailureMessage "test_x" "python3" minor out
  unless hasSub msg "py_to_strata failed to lower" && hasSub msg want do
    throw <| .userError s!"minor={minor}: expected a message containing {want}, got: {msg}"

-- A syntax error under Python 3.11 names the version.
#guard_msgs in
#eval checkCause (some 11) parseFailureOut "may need Python 3.12 or later"

-- The same syntax error under Python 3.12 points at the front end.
#guard_msgs in
#eval checkCause (some 12) parseFailureOut "fix the front end"

-- An unreadable version is not taken as an old one.
#guard_msgs in
#eval checkCause none parseFailureOut "fix the front end"

-- A missing module is a setup problem, whatever the version.
#guard_msgs in
#eval checkCause (some 11) "ModuleNotFoundError: No module named 'strata'\n"
  "setup problem"

-- The message names the interpreter and its version.
#guard_msgs in
#eval checkCause (some 11) parseFailureOut "python3 (Python 3.11)"
