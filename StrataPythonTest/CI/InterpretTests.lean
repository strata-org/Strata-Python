/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.PythonDialect
meta import StrataPython.Cli
meta import StrataPython.PySpecPipeline
meta import StrataPython.PyFactory
meta import StrataPythonTest.CI.GoldenTest
open Strata
open StrataPython

meta section

/-- Run the pyInterpret pipeline on an Ion file and return (exitCode, output). -/
private def runPyInterpret (ionFile : String) (fuel : Nat := 100000) : IO (UInt32 × String) := do
  let quietCtx ← Pipeline.PipelineContext.create (outputMode := .quiet)
  let (core, _diags) ←
    match ← (pythonAndSpecToLaurel ionFile (specDir := ".")).run quietCtx |>.toBaseIO with
    | .ok laurel =>
      match ← translateCombinedLaurel laurel (analysisMode := .Execute) with
      | (some core, diags) => pure (core, diags)
      | (none, diags) => return (1, s!"Laurel to Core translation failed: {diags}")
    | .error () =>
      let msgs ← quietCtx.getMessages
      let detail := match msgs.back? with | some m => m.message | none => "Pipeline aborted"
      return (1, detail)
  let core ← match Core.typeCheck Core.VerifyOptions.quiet core
      (moreFns := StrataPython.RuntimeFactory) with
    | .ok prog => pure prog
    | .error e => return (1, s!"Core type checking failed: {e.message}")
  match core.run (moreFns := StrataPython.RuntimeFactory) with
  | .ok E =>
    let mainProc := Core.Program.Procedure.find? core ⟨"__main__", ()⟩
    let outputNames := match mainProc with
      | some p => p.header.outputs.keys.map (·.name)
      | none => []
    let (lhs, exprEnv) := Core.Env.genVars outputNames E.exprEnv
    let E := { E with exprEnv }
    let E := Core.Statement.Command.runCall lhs "__main__" [] fuel E
    match E.error with
    | none => return (0, "Execution completed successfully.")
    | some e => return (1, s!"{Std.format e}")
  | .error diag => return (1, s!"Error: {diag}")

/-- Compile a Python file to Ion. Returns the Ion file path on success. -/
private def compilePythonToIon (pythonFile : System.FilePath)
    (dialectFile : System.FilePath) : IO (Option (System.FilePath × String)) := do
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
  let relIon := s!"StrataPythonTest/tests/{stem}.python.st.ion"
  return some (ionFile, relIon)

#eval show IO Unit from do
  let dialectFile : System.FilePath := "/tmp/brazillake-test-dialect.ion"
  IO.FS.writeBinFile dialectFile StrataPython.Python.toIon

  let cfg : StrataPython.CI.GoldenTest.Config := {
    testsDir := "StrataPythonTest/tests"
    expectedDir := "StrataPythonTest/expected_interpret"
    compareMode := .regex
  }
  let results ← StrataPython.CI.GoldenTest.run cfg fun testFile => do
    match ← compilePythonToIon testFile dialectFile with
    | none => return none
    | some (ionFile, relIon) =>
      let result ← runPyInterpret relIon
      IO.FS.removeFile ionFile
      return some result
  if results.errors > 0 then
    throw <| IO.userError s!"{results.errors} interpret tests failed"

end -- meta section
