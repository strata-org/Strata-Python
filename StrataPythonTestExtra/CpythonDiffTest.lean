/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python -- shake: keep
public meta import StrataDDM
public meta import StrataPython.PythonDialect
import StrataPython
import StrataPython.ReadPython

/-! ## CPython differential test

Round-trips every `.py` file under a directory through the Python generator and
the Strata Ion (de)serializer, mirroring the old `run_test.sh` shell script.

For each Python file the test:

1. Runs `python -m strata_python.gen py_to_strata` to produce a `.python.st.ion`
   file (the subject under test is the Python parser/generator).
2. Reads that Ion file into a `StrataDDM.Program`, re-serializes it to Ion, and
   reads it back — then asserts the two programs are syntactically equal. This
   replaces the `strata toIon` + `strata diff` round-trip the shell script ran
   through the `strata` CLI; here it is an in-process library call, so no
   separate `StrataCLI` build is required.

Orchestration (cloning CPython at a given version, choosing the version, and
the list of files expected to fail) stays in the calling shell script. This
test is driven entirely by environment variables so it stays inert during a
plain `lake test`:

- `CPYTHON_DIR`   — directory to scan recursively for `*.py` files. When unset
                    or empty, the test is a no-op and succeeds, so local
                    `lake test` runs stay green without a CPython checkout.
- `CPYTHON_EXPECTED_FAILURES` — optional path to a plaintext file listing, one
                    per line, path suffixes of files that are expected to FAIL
                    to parse/round-trip. A line matches a discovered file when
                    the file path ends with that suffix (matching the
                    substring logic of the original shell script). Blank lines
                    and lines starting with `#` are ignored.
- `CPYTHON_FAIL_FAST` — when set to a non-empty value, stop and report on the
                    first unexpected outcome instead of scanning everything.
-/

open StrataDDM.Parser (stringInputContext)
open StrataPython (withPython)

namespace StrataPython.CpythonDiffTest

meta section

/-- Recursively collect all `*.py` files under `dir`. -/
private partial def findPyFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut results := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      results := results ++ (← findPyFiles entry.path)
    else if entry.path.extension == some "py" then
      results := results.push entry.path
  return results

/-- Read the expected-failures list: a plaintext file with one path suffix per
    line. Blank lines and `#` comments are ignored. -/
private def readExpectedFailures (path : System.FilePath) : IO (Array String) := do
  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n"
    |>.map (·.trimAscii.toString)
    |>.filter (fun l => !l.isEmpty && !l.startsWith "#")
  return lines.toArray

/-- Is `file` expected to fail? True when its path ends with any listed suffix. -/
private def isExpectedFailure (expected : Array String) (file : System.FilePath) : Bool :=
  let s := file.toString
  expected.any (fun suffix => s.endsWith suffix)

/-- Run the generator on `pyFile`, writing Ion to `ionFile`. Returns `.ok ()` on
    success or `.error msg` if the generator exits non-zero. -/
private def runPyToStrata (pythonCmd : System.FilePath)
    (dialectFile pyFile ionFile : System.FilePath) : IO (Except String Unit) := do
  let child ← IO.Process.spawn {
    cmd := pythonCmd.toString
    args := #["-m", "strata_python.gen", "py_to_strata",
              "--dialect", dialectFile.toString,
              pyFile.toString, ionFile.toString]
    inheritEnv := true
    stdin := .null, stdout := .null, stderr := .piped
  }
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode = 0 then
    return .ok ()
  else
    return .error s!"py_to_strata failed (exit code {exitCode}): {stderr}"

/-- The in-process equivalent of `strata toIon` followed by `strata diff`: read
    the Python Ion program, re-serialize it to Ion, read it back, and require
    the two programs to be syntactically identical. -/
private def roundTripIon (ionFile : System.FilePath) : IO (Except String Unit) := do
  let bytes ← IO.FS.readBinFile ionFile
  match StrataDDM.Program.fromIon Python_map Python.name bytes with
  | .error msg => return .error s!"read failed: {msg}"
  | .ok pgm =>
    let reBytes := StrataDDM.writeStrataIon pgm
    match StrataDDM.Program.fromIon Python_map Python.name reBytes with
    | .error msg => return .error s!"re-read failed: {msg}"
    | .ok pgm2 =>
      if pgm.dialect != pgm2.dialect then
        return .error s!"dialects differ: {pgm.dialect} and {pgm2.dialect}"
      if pgm.commands.size != pgm2.commands.size then
        return .error
          s!"command count differs: {pgm.commands.size} and {pgm2.commands.size}"
      for (c1, c2) in pgm.commands.zip pgm2.commands do
        if c1 != c2 then
          return .error "commands differ after Ion round-trip"
      return .ok ()

/-- Process a single Python file: generate Ion, then round-trip it. Returns
    `.ok ()` on a clean round-trip, `.error msg` otherwise. -/
private def checkFile (pythonCmd dialectFile : System.FilePath) (pyFile : System.FilePath)
    : IO (Except String Unit) := do
  IO.FS.withTempDir fun tmpDir => do
    let ionFile := tmpDir / "out.python.st.ion"
    match ← runPyToStrata pythonCmd dialectFile pyFile ionFile with
    | .error msg => return .error msg
    | .ok () => roundTripIon ionFile

/-- Run the differential test over `dir`. -/
private def runOn (pythonCmd : System.FilePath) (dir : System.FilePath)
    (expected : Array String) (failFast : Bool) : IO Unit := do
  IO.FS.withTempDir fun tmpDir => do
    -- Write the Python dialect once for the generator to consume.
    let dialectFile := tmpDir / "Python.dialect.st.ion"
    IO.FS.writeBinFile dialectFile Python.toIon

    let files ← findPyFiles dir
    IO.println s!"Found {files.size} Python file(s) under {dir}"

    let mut count := 0
    let mut failures := 0
    for pyFile in files do
      count := count + 1
      let shouldFail := isExpectedFailure expected pyFile
      let result ← checkFile pythonCmd dialectFile pyFile
      match result, shouldFail with
      | .ok (), false => pure ()
      | .error _, true =>
        IO.println s!"  ok (expected failure): {pyFile}"
      | .ok (), true =>
        IO.println s!"  UNEXPECTED PASS (expected failure): {pyFile}"
        failures := failures + 1
      | .error msg, false =>
        IO.println s!"  FAIL: {pyFile}\n    {msg}"
        failures := failures + 1
      if failFast && failures > 0 then
        throw <| .userError s!"Failed on {pyFile} (fail-fast)"

    IO.println s!"Checked {count} file(s), {failures} failure(s)."
    if failures > 0 then
      throw <| .userError s!"{failures} CPython differential test failure(s)."

/-- Entry point: read configuration from the environment and run, or no-op when
    `CPYTHON_DIR` is unset. -/
def main : IO Unit := do
  match ← IO.getEnv "CPYTHON_DIR" with
  | none =>
    IO.println "CPYTHON_DIR not set; skipping CPython differential test."
  | some dirStr =>
    if dirStr.trimAscii.toString.isEmpty then
      IO.println "CPYTHON_DIR empty; skipping CPython differential test."
      return
    let dir : System.FilePath := dirStr
    let expected ← match ← IO.getEnv "CPYTHON_EXPECTED_FAILURES" with
      | some p => if p.trimAscii.toString.isEmpty then pure #[] else readExpectedFailures p
      | none => pure #[]
    let failFast := match ← IO.getEnv "CPYTHON_FAIL_FAST" with
      | some v => !v.trimAscii.toString.isEmpty
      | none => false
    withPython fun pythonCmd => runOn pythonCmd dir expected failFast

end

end StrataPython.CpythonDiffTest

#eval StrataPython.CpythonDiffTest.main
