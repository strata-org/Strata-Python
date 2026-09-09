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
file named in `sarifTests` the test:

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

### Why a fixed list rather than the whole corpus

This used to walk every `tests/test_*.py` minus a skip list. That bought one
repetition of the same three input-independent checks per case — version, one run,
tool name — plus "the pipeline emitted a document at all", which the analyze goldens
already record per case as their `RESULT:` line. The only input-dependent assertions
are the three named cases in `validate`.

The cost was not small: over a 1,478-case corpus it was ~794 analyses at ~4s each,
about 52 minutes of SMT per build, against ~5 minutes for the list below. It also
needed a 684-entry skip list to suppress the cases where the pipeline declines,
which had to be maintained by hand every time the corpus or the front end moved.

So the list is explicit. Add a case here when it asserts something about SARIF that
no case here already asserts — not to give a program SARIF coverage for its own
sake, which is the analyze goldens' job.

This is a runtime test (needs Python with `strata_python.gen`, plus the SMT
solvers cvc5 and z3 on PATH), run from `StrataPythonTestExtra/` via `lake test`.
-/

open Strata
open StrataPython (withPython)

namespace StrataPython.SarifTest

meta section

/-- The cases this suite analyzes. Each one is here because it asserts something
    about the SARIF document that no other case here asserts; see the note above
    before adding to it.

    The first three carry the input-dependent assertions in `validate`. The rest
    cover distinct pipeline shapes that reach SMT, so a document is produced and
    the structural checks run against more than one program. -/
def sarifTests : Array String := #[
  -- Asserted individually in `validate`.
  "test_precondition_verification",              -- must report error-level results
  "test_arithmetic",                             -- must report no errors, with locations
  "test_soundness_global_read_before_assignment",-- unbound global: error with a location
  -- Shape coverage: gradual types, loops, context managers, slicing.
  "test_any_arithmetic",
  "test_while_loop",
  "test_with_statement",
  "test_list_slice"
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

  if baseName == "test_soundness_global_read_before_assignment" then
    if errorResults.size < 1 then
      return some "expected an error for an unbound module global"
    if locatedResults.size < 1 then
      return some "expected the unbound-global error to have a source location"

  return none

def main : IO Unit := do
  withPython fun pythonCmd => do
    IO.FS.withTempDir fun tmpDir => do
      let dialectFile := tmpDir / "Python.dialect.st.ion"
      IO.FS.writeBinFile dialectFile Python.toIon

      let mut failures := 0
      for stem in sarifTests do
        let pyFile := testsDir / s!"{stem}.py"
        -- A name here that no longer exists is a stale list, not a skip.
        unless ← pyFile.pathExists do
          IO.println s!"ERROR: {stem} is listed in sarifTests but {pyFile} is missing"
          failures := failures + 1
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
