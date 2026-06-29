/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython

/-! # Golden test harness

Generic test runner for file-based golden tests. Parameterized by:
- A test directory containing test files (matched by a glob prefix/suffix)
- An expected-output directory containing `.expected` and/or `.skip` files
- A comparison mode (regex match on failure output, or exact diff)
- A monadic action that receives each test file path and returns (exitCode, output)

The harness is agnostic to what the test files are or how they're processed —
callers handle compilation, tool invocation, etc.
-/

public meta section

namespace StrataPython.CI.GoldenTest

inductive CompareMode where
  | regex
  | exact

structure Config where
  testsDir : System.FilePath
  expectedDir : System.FilePath
  compareMode : CompareMode
  filePrefix : String := "test_"
  fileSuffix : String := ".py"

structure Results where
  passed : Nat := 0
  errors : Nat := 0
  skipped : Nat := 0

instance : ToString Results where
  toString r := s!"{r.passed} passed, {r.errors} errors, {r.skipped} skipped"

private def matchesPattern (output pattern : String) : IO Bool := do
  let result ← IO.Process.output {
    cmd := "bash"
    args := #["-c", s!"echo {repr output} | grep -qE {repr pattern}"]
  }
  return result.exitCode == 0

/-- Run a golden test suite. The `runTest` action receives the full path to each
    test file and returns `some (exitCode, output)` or `none` to skip the test.
    The harness handles skip files, expected-output comparison, and result tallying. -/
def run (cfg : Config) (runTest : System.FilePath → IO (Option (UInt32 × String))) : IO Results := do
  let entries ← System.FilePath.readDir cfg.testsDir
  let testFiles := entries.filter (fun e =>
    e.fileName.startsWith cfg.filePrefix && e.fileName.endsWith cfg.fileSuffix)
  let testFiles := testFiles.toList.mergeSort (fun a b => a.fileName < b.fileName) |>.toArray

  let mut results : Results := {}

  for entry in testFiles do
    let baseName := (entry.fileName.dropEnd cfg.fileSuffix.length).toString
    let skipFile := cfg.expectedDir / (baseName ++ ".skip")
    let expectedFile := cfg.expectedDir / (baseName ++ ".expected")

    if ← skipFile.pathExists then
      let reason ← IO.FS.readFile skipFile
      IO.println s!"SKIP: {baseName} — {reason.trimAscii}"
      results := { results with skipped := results.skipped + 1 }
      continue

    let some (exitCode, output) ← runTest entry.path
      | do IO.println s!"SKIP (action): {baseName}"
           results := { results with skipped := results.skipped + 1 }
           continue

    match cfg.compareMode with
    | .regex =>
      if ← expectedFile.pathExists then
        let pattern := (← IO.FS.readFile expectedFile).trimAscii.toString
        if pattern.isEmpty then
          IO.println s!"ERR:  {baseName} (empty .expected file — must contain a pattern)"
          results := { results with errors := results.errors + 1 }
        else if exitCode == 0 then
          IO.println s!"ERR:  {baseName} (expected failure matching /{pattern}/ but test passed)"
          results := { results with errors := results.errors + 1 }
        else
          let matched ← matchesPattern output pattern
          if matched then
            IO.println s!"OK:   {baseName} (expected failure)"
            results := { results with passed := results.passed + 1 }
          else
            IO.println s!"ERR:  {baseName} (output does not match expected pattern /{pattern}/)"
            IO.println s!"      actual: {output.take 200}"
            results := { results with errors := results.errors + 1 }
      else
        if exitCode == 0 then
          IO.println s!"OK:   {baseName}"
          results := { results with passed := results.passed + 1 }
        else
          IO.println s!"ERR:  {baseName} (expected pass but failed) — {output.take 200}"
          results := { results with errors := results.errors + 1 }
    | .exact =>
      if ← expectedFile.pathExists then
        let expected := (← IO.FS.readFile expectedFile).trimAsciiEnd |>.toString
        let actual := output.trimAsciiEnd |>.toString
        if expected.isEmpty then
          IO.println s!"ERR:  {baseName} (empty .expected file — must contain expected output)"
          results := { results with errors := results.errors + 1 }
        else if actual == expected then
          IO.println s!"OK:   {baseName}"
          results := { results with passed := results.passed + 1 }
        else
          IO.println s!"ERR:  {baseName} (output does not match expected)"
          let expectedLines := expected.splitOn "\n"
          let actualLines := actual.splitOn "\n"
          for i in [:Nat.max expectedLines.length actualLines.length] do
            let exp := expectedLines.getD i ""
            let act := actualLines.getD i ""
            if exp != act then
              IO.println s!"      line {i + 1}:"
              IO.println s!"        expected: {exp}"
              IO.println s!"        actual:   {act}"
              break
          results := { results with errors := results.errors + 1 }
      else
        IO.println s!"SKIP (no expected): {baseName}"
        results := { results with skipped := results.skipped + 1 }

  IO.println s!"\nResults: {results}"
  return results

end StrataPython.CI.GoldenTest

end -- public meta section
