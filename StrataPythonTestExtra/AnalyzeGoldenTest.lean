/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.PythonDialect
meta import StrataPython.Cli
meta import StrataPythonTest.CI.GoldenTest
open Strata
open StrataPython

meta section

/-- Compile a Python file to Ion. Returns the Ion file path on success. -/
private def compilePythonToIon (pythonFile : System.FilePath)
    (dialectFile : System.FilePath) : IO (Option System.FilePath) := do
  let python ← match ← IO.getEnv "PYTHON" with
    | some p => pure p
    | none => throw <| IO.userError "PYTHON env var not set. Is this running via custom-build?"
  let baseName := pythonFile.fileName.getD "test"
  let stem := (baseName.dropEnd 3).toString
  let ionFile := pythonFile.parent.getD "." / (stem ++ ".python.st.ion")
  let result ← IO.Process.output {
    cmd := python
    args := #["-m", "strata_python.gen", "-q", "py_to_strata",
              "--dialect", dialectFile.toString,
              pythonFile.toString, ionFile.toString]
  }
  if result.exitCode != 0 then
    return none
  if !(← ionFile.pathExists) then
    return none
  return some ionFile

/-- Read per-file strata arguments from a `# strata-args:` comment. -/
private def readExtraArgs (pyFile : System.FilePath) : IO (Array String) := do
  let content ← IO.FS.readFile pyFile
  let lines := content.splitOn "\n"
  match lines.find? (·.startsWith "# strata-args:") with
  | some line =>
    let argsStr := (line.drop "# strata-args:".length).trimAscii.toString
    return argsStr.splitOn " " |>.filter (!·.isEmpty) |>.toArray
  | none => return #[]

/-- Parse extra args into VerifyOptions overrides. Currently only
    `--check-mode bugFinding` and `--check-level full` are used by tests. -/
private def applyExtraArgs (baseOpts : Core.VerifyOptions) (args : Array String)
    : Core.VerifyOptions := Id.run do
  let mut opts := baseOpts
  let mut i := 0
  while i < args.size do
    if args[i]! == "--check-mode" && i + 1 < args.size then
      match args[i+1]! with
      | "bugFinding" => opts := { opts with checkMode := .bugFinding }
      | "bugFindingAssumingCompleteSpec" =>
        opts := { opts with checkMode := .bugFindingAssumingCompleteSpec }
      | _ => pure ()
      i := i + 2
    else if args[i]! == "--check-level" && i + 1 < args.size then
      match args[i+1]! with
      | "full" => opts := { opts with checkLevel := .full }
      | _ => pure ()
      i := i + 2
    else
      i := i + 1
  return opts

/-- Run the analyze pipeline in-process and produce the same stdout the CLI would. -/
private def runPyAnalyze (ionFile : System.FilePath) (pyFile : String)
    (extraArgs : Array String) : IO (UInt32 × String) := do
  let baseOpts : Core.VerifyOptions :=
    { Core.VerifyOptions.default with
      verbose := .quiet, removeIrrelevantAxioms := .Precise }
  let options := applyExtraArgs baseOpts extraArgs
  let isBugFinding := options.checkMode == .bugFinding
                    || options.checkMode == .bugFindingAssumingCompleteSpec
  let entryPoint : Core.EntryPoint := if isBugFinding then .roots else .all
  let (outcome, _stats, pctx) ← StrataPython.Pipeline.runPyAnalyzePipeline {
    filePath := ionFile.toString
    specDir := "."
    sourcePath := some pyFile
    verifyOptions := options
    entryPoint
    isBugFinding
    outputMode := .quiet
  }
  let toolErrors ← pctx.getToolErrors
  let userErrors ← pctx.getUserCodeErrors
  let msgs ← pctx.getMessages
  -- The pyFile is relative (e.g. "tests/test_foo.py") matching golden file paths,
  -- but the actual source is at "StrataPythonTest/tests/test_foo.py" from cwd.
  let pyFileOnDisk : System.FilePath := "StrataPythonTest" / pyFile

  if let some lastErr := toolErrors.back? then
    let s := s!"DETAIL: {lastErr.message}\nRESULT: Internal error\n"
    return (ExitCode.internalError.toUInt32, s)

  if let some lastErr := userErrors.back? then
    let range := lastErr.loc
    let mfm : Option (String × Lean.FileMap) ←
      if (← System.FilePath.pathExists pyFileOnDisk) then
        let srcText ← IO.FS.readFile pyFileOnDisk
        pure (some (pyFile, Lean.FileMap.ofString srcText))
      else pure none
    let location := if range.isNone then "" else
      match mfm with
      | some (_, fm) =>
        let pos := fm.toPosition range.start
        s!" at line {pos.line}, col {pos.column}"
      | none => ""
    let mut lines := #[
      s!"(set-info :file {repr pyFile})"
    ]
    unless range.isNone do
      lines := lines.push s!"(set-info :start {range.start})"
      lines := lines.push s!"(set-info :stop {range.stop})"
    lines := lines.push s!"(set-info :error-message {repr lastErr.message})"
    let setInfoStr := "\n".intercalate lines.toList ++ "\n"
    let detail := s!"{lastErr.message}{location}"
    let s := s!"{setInfoStr}DETAIL: {detail}\nRESULT: User error\n"
    return (ExitCode.userError.toUInt32, s)

  match outcome with
  | .verified vcResults _coreProgram =>
    let classifier : Cli.ResultClassifier :=
      match options.checkMode with
      | .bugFinding | .bugFindingAssumingCompleteSpec =>
        { isSuccess := (·.isBugFindingSuccess)
          isFailure := (·.isBugFindingFailure) }
      | _ => {}
    let mfm : Option (String × Lean.FileMap) ←
      if (← System.FilePath.pathExists pyFileOnDisk) then
        let srcText ← IO.FS.readFile pyFileOnDisk
        pure (some (pyFile, Lean.FileMap.ofString srcText))
      else pure none
    let mut s := ""
    for vcResult in vcResults do
      let fileMap := mfm.map (·.2)
      let location := match Imperative.getFileRange vcResult.obligation.metadata with
        | some fr =>
          if fr.range.isNone then ""
          else s!"{fr.format fileMap (includeEnd? := false)}"
        | none => ""
      let messageSuffix := match vcResult.obligation.metadata.getPropertySummary with
        | some msg => s!" - {msg}"
        | none =>
          -- Strip unstable numeric parts from generated labels. Labels follow
          -- patterns like `name(NNN)_NNN` or `name(NNN)` where `(NNN)` is a
          -- location ID and `_NNN` is a uniqueness counter — both change when
          -- internal pipeline numbering shifts. We normalize to `name(…)` for
          -- stable golden-test comparison.
          let label := vcResult.obligation.label
          -- Normalize: find `(` and `)`, check content is numeric, replace.
          -- Only normalize if the text after `)` is empty or a bare `_NNN`
          -- counter. Labels like `assert_assert(71)_calls_Any_get_0` have
          -- meaningful suffixes and must NOT be normalized.
          let label := match label.splitOn "(" with
            | [pfx, rest] =>
              match rest.splitOn ")" with
              | [inside, afterParen] =>
                if inside.all Char.isDigit && !inside.isEmpty then
                  if afterParen.isEmpty then
                    pfx ++ "(…)"
                  else match afterParen.splitOn "_" with
                    | ["", digits] =>
                      if digits.all Char.isDigit && !digits.isEmpty then pfx ++ "(…)"
                      else label
                    | _ => label
                else label
              | _ => label
            | _ => label
          s!" - {label}"
      let outcomeStr := vcResult.formatOutcome
      let loc := if !location.isEmpty then s!"{location}: " else "unknown location: "
      s := s ++ s!"{loc}{outcomeStr}{messageSuffix}\n"
    -- Summary
    let (implError, rest1) :=
      vcResults.partition (fun r => r.isImplementationError || r.hasSMTError)
    let (timeouts, classifiable) := rest1.partition (·.isTimeout)
    let (success, rest) := classifiable.partition classifier.isSuccess
    let (failure, inconclusive) := rest.partition classifier.isFailure
    let nUnreachable := vcResults.filter (·.isUnreachable) |>.size
    let nImplError := implError.size
    let nTimeout := timeouts.size
    let nSuccess := success.size
    let nFailure := failure.size
    let nInconclusive := inconclusive.size
    let unreachableStr := if nUnreachable > 0 then s!", {nUnreachable} unreachable" else ""
    let implErrorStr := if nImplError > 0 then s!", {nImplError} internal errors" else ""
    let timeoutStr := if nTimeout > 0 then s!", {nTimeout} solver timeouts" else ""
    let counts := s!"{nSuccess} passed, {nFailure} failed, {nInconclusive} inconclusive{unreachableStr}{timeoutStr}{implErrorStr}"
    if nImplError > 0 then
      s := s ++ s!"DETAIL: An unexpected result was produced. {counts}\nRESULT: Internal error\n"
      return (ExitCode.internalError.toUInt32, s)
    else if nFailure > 0 then
      s := s ++ s!"DETAIL: {counts}\nRESULT: Failures found\n"
      return (ExitCode.failuresFound.toUInt32, s)
    else
      let label :=
        if nTimeout > 0 then "Solver timeout"
        else if nInconclusive > 0 then "Inconclusive"
        else "Analysis success"
      s := s ++ s!"DETAIL: {counts}\nRESULT: {label}\n"
      return (0, s)
  | .failed =>
    let knownLimitations := msgs.filter (·.kind.impact == .knownLimitation)
    match knownLimitations.back? with
    | some lastErr =>
      let s := s!"DETAIL: {lastErr.message}\nRESULT: Known limitation\n"
      return (ExitCode.knownLimitation.toUInt32, s)
    | none =>
      let msg := match msgs.back? with
        | some m => m.message
        | none => "Pipeline aborted"
      let s := s!"DETAIL: {msg}\nRESULT: Internal error\n"
      return (ExitCode.internalError.toUInt32, s)

#eval show IO Unit from do
  let dialectFile : System.FilePath := "/tmp/brazillake-test-dialect.ion"
  IO.FS.writeBinFile dialectFile StrataPython.Python.toIon

  let cfg : StrataPython.CI.GoldenTest.Config := {
    testsDir := "StrataPythonTest/tests"
    expectedDir := "StrataPythonTest/expected_laurel"
    compareMode := .exact
  }
  let results ← StrataPython.CI.GoldenTest.run cfg fun testFile => do
    let extraArgs ← readExtraArgs testFile
    match ← compilePythonToIon testFile dialectFile with
    | none => return none
    | some ionFile =>
      let baseName := testFile.fileName.getD "test"
      let stem := (baseName.dropEnd 3).toString
      let pyRelPath := s!"tests/{stem}.py"
      let result ← runPyAnalyze ionFile pyRelPath extraArgs
      IO.FS.removeFile ionFile
      return some result
  if results.errors > 0 then
    throw <| IO.userError s!"{results.errors} analyze tests failed"

end -- meta section
