/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python -- shake: keep
meta import StrataPython
meta import StrataPython.Pipeline.PyAnalyzeLaurel
meta import Strata.Languages.Core.SarifOutput

import Strata.Languages.Core.Verifier

/-! ## SARIF output tests for `pyAnalyzeLaurel`

Ports `run_py_analyze_sarif.py` + `validate_sarif.py` to a Lean test. For each
`tests/test_*.py` file the test:

1. Spawns `strata_python.gen py_to_strata` to compile the Python source to Ion.
2. Runs `StrataPython.Pipeline.runPyAnalyzePipeline` in-process — the same
   pipeline `pyAnalyzeLaurel --sarif` drives — and builds the SARIF document
   via `Core.Sarif.vcResultsToSarif`.
3. Asserts the SARIF document is well-formed.

Unlike the Python version this runs entirely in-process: it inspects the typed
`Strata.Sarif.SarifDocument` directly rather than serializing to JSON and
re-parsing, so most of `validate_sarif.py`'s structural checks (version,
single run, valid `level`, present `ruleId`/`message`) are guaranteed by the
types. The remaining checks — tool name, the per-test expectations for
`test_precondition_verification` and `test_arithmetic` — are asserted below.

This is a runtime test (needs Python with `strata_python.gen`, plus the SMT
solvers cvc5 and z3 on PATH), run from `StrataPythonTestExtra/` via `lake test`.
-/

open Strata
open StrataPython (withPython)

namespace StrataPython.SarifTest

meta section

/-- Test files that produce no usable SARIF output and are skipped, mirroring
    `SKIP_TESTS` in the original `run_py_analyze_sarif.py`. -/
def skipTests : Std.HashSet String := Std.HashSet.ofList [
  "test_foo_client_folder",
  "test_invalid_client_type",
  "test_unsupported_config",
  "test_with_void_enter",
  "test_class_no_init_extra_args", -- No SARIF output: does not run SMT analysis
  "test_user_error_metadata",      -- No SARIF output: does not run SMT analysis
  "test_is_non_none",              -- No SARIF output: does not run SMT analysis
  "test_is_not_non_none",          -- No SARIF output: does not run SMT analysis
  "test_list"                      -- Module-level asserts: "asserts not supported" error
]

def testsDir : System.FilePath := "StrataPythonTest/tests"

/-- Compile a Python source file to a `.python.st.ion` Ion file in `outDir`. -/
def compilePython (pythonCmd dialectFile pyFile outDir : System.FilePath)
    : IO System.FilePath := do
  let some stem := pyFile.fileStem
    | throw <| .userError s!"No stem for {pyFile}"
  let ionPath := outDir / s!"{stem}.python.st.ion"
  let child ← IO.Process.spawn {
    cmd := pythonCmd.toString
    args := #["-m", "strata_python.gen", "py_to_strata",
              "--dialect", dialectFile.toString,
              pyFile.toString, ionPath.toString]
    inheritEnv := true
    stdin := .null, stdout := .null, stderr := .piped
  }
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode ≠ 0 then
    throw <| .userError s!"py_to_strata failed for {pyFile} (exit {exitCode}): {stderr}"
  return ionPath

/-- Run the analysis pipeline on a compiled Ion file and return the SARIF
    document, mirroring the `pyAnalyzeLaurel --sarif` path: deductive mode,
    `entryPoint = .all`, quiet output. `pyFile` is the original Python source,
    used (as the CLI does) both as the pipeline `sourcePath` and to build the
    `files` map so SARIF locations resolve. Returns `none` if the pipeline did
    not reach verification (e.g. aborted), matching the Python script's "no
    SARIF file created" failure. -/
def analyzeToSarif (ionFile pyFile specDir : System.FilePath)
    : IO (Option Strata.Sarif.SarifDocument) := do
  let options : Core.VerifyOptions :=
    { Core.VerifyOptions.default with
      verbose := .quiet, removeIrrelevantAxioms := .Precise,
      checkMode := .deductive }
  let (outcome, _stats, _pctx) ← StrataPython.Pipeline.runPyAnalyzePipeline {
    filePath := ionFile.toString
    specDir
    sourcePath := some pyFile.toString
    verifyOptions := options
    entryPoint := .all
    isBugFinding := false
    outputMode := .quiet
  }
  match outcome with
  | .verified vcResults _coreProgram =>
    -- Build the source file map so VC metadata file-ranges resolve to
    -- SARIF locations, keyed by the same URI the pipeline stamps on them.
    let srcText ← IO.FS.readFile pyFile
    let files := Map.empty.insert (Strata.Uri.file pyFile.toString)
      (Lean.FileMap.ofString srcText)
    pure (some (Core.Sarif.vcResultsToSarif options.checkMode files vcResults))
  | .failed => pure none

/-- Validate a SARIF document for `baseName`, mirroring `validate_sarif.py`.
    Returns an error message, or `none` if valid. Structural invariants
    (version, single run, valid `level` enum, present `ruleId`/`message`) hold
    by construction of `SarifDocument`; we check the remaining properties. -/
def validate (doc : Strata.Sarif.SarifDocument) (baseName : String) : Option String := Id.run do
  if doc.version != "2.1.0" then
    return some s!"wrong version: {doc.version}"
  if doc.runs.size != 1 then
    return some s!"expected 1 run, got {doc.runs.size}"
  let run := doc.runs[0]!
  if run.tool.driver.name != "Strata" then
    return some s!"wrong tool name: {run.tool.driver.name}"
  let results := run.results
  let errorResults := results.filter (·.level == .error)
  let locatedResults := results.filter (·.locations.size > 0)

  if baseName == "test_precondition_verification" then
    if errorResults.size < 1 then
      return some s!"expected error-level results, got {errorResults.size}"

  if baseName == "test_arithmetic" then
    if errorResults.size != 0 then
      return some s!"expected 0 errors, got {errorResults.size}"
    if locatedResults.size < 1 then
      return some s!"expected results with locations, got {locatedResults.size}"

  return none

/-- Recursively unused: tests live directly under `testsDir`; collect `test_*.py`. -/
def findTestFiles : IO (Array System.FilePath) := do
  let mut results := #[]
  for entry in ← testsDir.readDir do
    let p := entry.path
    if p.extension == some "py" then
      if let some stem := p.fileStem then
        if stem.startsWith "test_" then
          results := results.push p
  return results.qsort (·.toString < ·.toString)

def main : IO Unit := do
  withPython fun pythonCmd => do
    IO.FS.withTempDir fun tmpDir => do
      let dialectFile := tmpDir / "Python.dialect.st.ion"
      IO.FS.writeBinFile dialectFile Python.toIon

      let files ← findTestFiles
      let mut failures := 0
      for pyFile in files do
        let some stem := pyFile.fileStem
          | continue
        if skipTests.contains stem then
          IO.println s!"Skipping: {stem}"
          continue
        IO.println s!"Testing SARIF output for {stem}..."
        let ionFile ← compilePython pythonCmd dialectFile pyFile tmpDir
        match ← analyzeToSarif ionFile pyFile tmpDir with
        | none =>
          IO.println s!"ERROR: pipeline produced no SARIF output for {stem}"
          failures := failures + 1
        | some doc =>
          match validate doc stem with
          | some err =>
            IO.println s!"ERROR: SARIF validation failed for {stem}: {err}"
            failures := failures + 1
          | none =>
            IO.println s!"Test passed: {stem}"

      if failures > 0 then
        throw <| .userError s!"{failures} SARIF test failure(s)."

end

end StrataPython.SarifTest

#eval StrataPython.SarifTest.main
