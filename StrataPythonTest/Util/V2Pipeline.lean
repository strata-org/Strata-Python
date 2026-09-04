/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.SimpleAPI
public meta import StrataPython.PySpecPipeline
public meta import StrataPython.Resolution
public meta import Strata.Languages.Laurel.Resolution
public meta import Strata.Transform.ProcedureInlining
public meta import StrataPython.PyFactory
public meta import StrataPythonTest.Util.Python
public meta import StrataPython

namespace StrataPython.V2TestUtil

open Strata.Pipeline (PipelineContext)

meta section

public def testDir : System.FilePath :=
  "StrataPythonTestExtra/Specs/dispatch_test"

public def compilePython
    (pythonCmd : System.FilePath)
    (dialectFile : System.FilePath) (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  let some stem := pyFile.fileStem
    | throw <| .userError s!"No stem for {pyFile}"
  let ionPath := outDir / s!"{stem}.python.st.ion"
  let child ← IO.Process.spawn {
    cmd := toString pythonCmd
    args := #["-m", "strata_python.gen", "py_to_strata",
      "--dialect", dialectFile.toString, pyFile.toString, ionPath.toString]
    cwd := none
    inheritEnv := true
    stdin := .null
    stdout := .piped
    stderr := .piped
  }
  let _ ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode ≠ 0 then
    throw <| .userError s!"py_to_strata failed for {pyFile} (exit {exitCode}): {stderr}"
  return ionPath

public def setupPySpecs (pythonCmd : System.FilePath) (tmpDir : System.FilePath)
    (modules : Array String) : IO Unit := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.toIon
    match ← pySpecsDir testDir (tmpDir / "specs") dialectFile
        (modules := modules) (warningOutput := .none)
        (pythonCmd := toString pythonCmd) |>.toBaseIO with
    | .ok () => pure ()
    | .error msg => throw <| IO.userError s!"pySpecsDir failed: {msg}"

public def compileTestScript (pythonCmd : System.FilePath)
    (scriptName : String) (tmpDir : System.FilePath) : IO System.FilePath := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.toIon
    compilePython pythonCmd dialectFile (testDir / scriptName) tmpDir

public def runV2 (pythonCmd : System.FilePath) (tmpDir : System.FilePath)
    (scriptName : String) (pyspecModules : Array String := #[])
    (dispatchModules : Array String := #[])
    (keepAllFilesPrefix : Option String := none)
    : IO (System.FilePath × Except String (Option Core.Program × List Strata.Pipeline.Message)) := do
  let ion ← compileTestScript pythonCmd scriptName tmpDir
  let pctx ← PipelineContext.create (outputMode := .quiet)
  let result ← pyAnalyzeV2ToCore ion.toString
    (keepAllFilesPrefix := keepAllFilesPrefix)
    (specDir := tmpDir / "specs")
    (dispatchModules := dispatchModules)
    (pyspecModules := pyspecModules)
    (pipelineCtx := some pctx)
  return (ion, result)

public def verifyCore (coreProgram : Core.Program) (userSources : List String := [])
    : IO (Except String (Array Core.VCResult)) := do
  let (_, userProcNames) := splitProcNames coreProgram userSources
  let cg := coreProgram.toProcedureCG
  let userSet := Std.HashSet.ofList userProcNames
  let entryPoints := (cg.computeRoots (preferredRoots := userProcNames)).filter userSet.contains
  let entrySet := Std.HashSet.ofList entryPoints
  let inlinePhases : List Core.PipelinePhase :=
    [_root_.Core.procedureInliningPipelinePhase
      { doInline := fun caller callee a =>
          (match caller with | some c => entrySet.contains c | none => false)
          && _root_.Core.doInlineNonRecursive callee a }]
  let options : Core.VerifyOptions :=
    { Core.VerifyOptions.default with
      stopOnFirstError := false, verbose := .quiet, solver := "z3",
      checkMode := .bugFinding, checkLevel := .full }
  match ← Strata.Core.verifyProgram coreProgram options
      (moreFns := StrataPython.RuntimeFactory)
      (proceduresToVerify := some entryPoints)
      (externalPhases := [Strata.frontEndPhase])
      (prefixPhases := inlinePhases) |>.toBaseIO with
  | .ok results => return .ok results
  | .error msg => return .error (toString msg)

public def runAndVerify (pythonCmd : System.FilePath) (tmpDir : System.FilePath)
    (scriptName : String) (pyspecModules : Array String := #[])
    (dispatchModules : Array String := #[]) : IO (Array Core.VCResult) := do
  let (ion, result) ← runV2 pythonCmd tmpDir scriptName pyspecModules dispatchModules
  match result with
  | .error msg => throw <| IO.userError s!"V2 pipeline failed: {msg}"
  | .ok (none, diags) =>
    throw <| IO.userError s!"V2 produced no Core: {String.intercalate "; " (diags.map (·.message))}"
  | .ok (some core, _) =>
    match ← verifyCore core [ion.toString] with
    | .error msg => throw <| IO.userError s!"verification failed: {msg}"
    | .ok results => return results

public def precondVC (pythonCmd : System.FilePath) (tmpDir : System.FilePath)
    (scriptName : String) (pyspecModules : Array String := #[]) : IO Core.VCResult := do
  let results ← runAndVerify pythonCmd tmpDir scriptName pyspecModules
  let matchingVCs := results.filter fun r =>
    (r.obligation.metadata.getPropertySummary.getD "").contains "precondition 0"
  match matchingVCs with
  | #[vc] => return vc
  | _ => throw <| IO.userError s!"Expected one precondition 0 VC, got {matchingVCs.size}"

public def vcBySummary (results : Array Core.VCResult) (needle : String) : IO Core.VCResult := do
  let matchingVCs := results.filter fun r =>
    (r.obligation.metadata.getPropertySummary.getD "").contains needle
  match matchingVCs with
  | #[vc] => return vc
  | _ => throw <| IO.userError s!"Expected one '{needle}' VC, got {matchingVCs.size}"

public def dumpProcChunk (pythonCmd : System.FilePath) (tmpDir : System.FilePath)
    (scriptName : String) (pyspecModules : Array String) (procName : String)
    (dispatchModules : Array String := #[]) : IO String := do
  let dumpPrefix := tmpDir / "v2dump"
  match (← runV2 pythonCmd tmpDir scriptName pyspecModules dispatchModules
      (keepAllFilesPrefix := some dumpPrefix.toString)).2 with
  | .error msg => throw <| IO.userError s!"V2 pipeline failed: {msg}"
  | .ok (none, diags) =>
    throw <| IO.userError s!"V2 produced no Core: {String.intercalate "; " (diags.map (·.message))}"
  | .ok (some _, diags) =>
    -- A dump can look right while elaboration failed; surface that instead of green-lighting it.
    if let some d := diags.find? (·.message.startsWith "elaboration failure") then
      throw <| IO.userError s!"V2 elaboration failed: {d.message}"
  let dump ← IO.FS.readFile (dumpPrefix.toString ++ ".v2.elaborated.laurel.st")
  match (dump.splitOn "procedure ").find? (·.startsWith procName) with
  | some chunk => return chunk
  | none => throw <| IO.userError s!"V2 Laurel dump has no {procName} procedure"

public def checkExternalSigSplit
    (args : List (String × Option (StrataPython.expr StrataDDM.SourceRange)))
    (expReq expOpt expKw : List String) (kwonlyCount : Nat := 0) : Option String :=
  let sig := StrataPython.Resolution.externalFunctionSig "f" "m_f" args kwonlyCount
  match sig.params with
  | .static p =>
    let reqIds := p.required.map (·.1)
    let optIds := p.optional.map (·.1)
    let kwIds := p.kwonly.map fun (name, _, _) => name
    let ids := fun names => names.map StrataPython.Resolution.PythonIdentifier.builtin
    if reqIds == ids expReq && optIds == ids expOpt && kwIds == ids expKw then none
    else some s!"split mismatch: expected {expReq}/{expOpt}/{expKw}, \
      got {repr reqIds}/{repr optIds}/{repr kwIds}"
  | _ => some "expected a static param list"

public def checkExternalKwargs : Option String :=
  let sig := StrataPython.Resolution.externalFunctionSig "f" "m_f" []
    (kwargsName := some "kwargs")
  if sig.kwargName == some (StrataPython.Resolution.PythonIdentifier.builtin "kwargs") then none
  else some s!"kwargName mismatch: got {repr sig.kwargName}"

public def someDefaultArg : Option (StrataPython.expr StrataDDM.SourceRange) :=
  some (.Constant .none (.ConNone .none) ⟨.none, none⟩)

/-- A default that `externalFunctionSig` cannot resolve to a constant. -/
public def nonConstDefaultArg : Option (StrataPython.expr StrataDDM.SourceRange) :=
  some (.Name .none ⟨.none, "SOME_CONST"⟩ (.Load .none))

end -- meta section

end StrataPython.V2TestUtil
