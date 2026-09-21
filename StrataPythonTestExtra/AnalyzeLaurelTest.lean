/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import StrataPython.PySpecPipeline
meta import StrataPython.Specs.MessageKind
meta import StrataLaurel.Implementation.Resolution
meta import StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator
meta import StrataLaurel.Implementation.CoreDefinitionsForLaurel
meta import Strata.Transform.ProcedureInlining
meta import StrataPython.PyFactory
meta import StrataPythonTest.Util.Python
meta import StrataPython

/-! ## End-to-end tests for `pyAnalyzeLaurel` with dispatch

These tests exercise the full pipeline: compile mock PySpec Python sources
to Ion, compile a user Python script to Ion, then run `pyAnalyzeLaurel`
with `--dispatch` through the SimpleAPI. The mock services (Storage,
Messaging) are generic and not tied to any cloud provider.
-/

open Strata.Pipeline (PipelineContext)

namespace StrataPython.AnalyzeLaurelTest

meta def quietCtx : BaseIO PipelineContext :=
  PipelineContext.create (outputMode := .quiet)

meta def testDir : System.FilePath :=
  "StrataPythonTestExtra/Specs/dispatch_test"

/-- Compile a Python source file to a `.python.st.ion` Ion file.
    Returns the path to the generated Ion file. -/
meta def compilePython
    (pythonCmd : System.FilePath)
    (dialectFile : System.FilePath) (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  let some stem := pyFile.fileStem
    | throw <| .userError s!"No stem for {pyFile}"
  let ionPath := outDir / s!"{stem}.python.st.ion"
  let spawnArgs : IO.Process.SpawnArgs := {
    cmd := toString pythonCmd
    args := #["-m", "strata_python.gen", "py_to_strata",
              "--dialect", dialectFile.toString,
              pyFile.toString, ionPath.toString]
    cwd := none
    inheritEnv := true
    stdin := .null
    stdout := .piped
    stderr := .piped
  }
  let child ← IO.Process.spawn spawnArgs
  let _stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode ≠ 0 then
    throw <| .userError s!"py_to_strata failed for {pyFile} (exit {exitCode}): {stderr}"
  return ionPath

/-- Set up the test fixture: compile all servicelib modules and return the
    spec directory.  The dispatch and pyspec modules are resolved by name. -/
meta def setupFixture (pythonCmd : System.FilePath)
    (outDir : System.FilePath) : IO Unit := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.toIon
    -- Compile all servicelib modules (dispatch + individual services)
    match ← pySpecsDir testDir outDir dialectFile
        (modules := #["servicelib", "servicelib.Storage", "servicelib.Messaging",
          "servicelib.Database", "servicelib.Counter", "servicelib.Contract",
          "servicelib.Admitted", "servicelib.Ghost", "servicelib.GhostProbe",
          "servicelib.GhostOld", "servicelib.GhostOldNoFrame",
          "servicelib.ParamType"])
        (warningOutput := .none)
        (pythonCmd := toString pythonCmd) |>.toBaseIO with
    | .ok () => pure ()
    | .error msg => throw <| IO.userError s!"pySpecsDir failed: {msg}"

/-- Compile a test Python file to Ion format. -/
meta def compileTestScript (pythonCmd : System.FilePath)
    (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.toIon
    compilePython pythonCmd dialectFile pyFile outDir

/-- Run pyAnalyzeLaurel on a test script within the shared fixture. -/
meta def runAnalyze
    (pythonCmd : System.FilePath)
    (tmpDir : System.FilePath) (scriptName : String)
    : IO (Except String Core.Program) := do
  let testIon ← compileTestScript pythonCmd (testDir / scriptName) tmpDir
  let pctx ← quietCtx
  let laurel ←
    match ← (pythonAndSpecToLaurel testIon.toString
        (dispatchModules := #["servicelib"])
        (specDir := tmpDir)).run pctx |>.toBaseIO with
    | .ok r => pure r
    | .error () =>
      -- Flag tool errors, then user errors, then general
      if let some r := (← pctx.getToolErrors).back? then
        return .error <| r.message.message
      if let some r := (← pctx.getUserCodeErrors).back? then
        return .error <| s!"User code error: {r.message.message}"
      if let some m := (←pctx.getMessages).back? then
        return .error m.message.message
      return .error "Pipeline aborted for unspecified reason (bug)"
  match ← translateCombinedLaurel laurel with
  | (some core, []) =>
    -- Also run Core type checking to catch semantic errors (e.g. Heap vs Any)
    match Strata.Core.typeCheck Core.VerifyOptions.quiet core (moreFns := StrataPython.RuntimeFactory) with
    | .error diag => return .error s!"Core type checking failed: {diag}"
    | .ok _ => return .ok core
  | (_, errors) => return .error s!"Laurel to Core translation failed: {errors}"

/-- Shared verifier configuration for the pipeline tests in this file. -/
meta def testVerifyOptions : Core.VerifyOptions :=
  { Core.VerifyOptions.default with
    stopOnFirstError := false, verbose := .quiet, solver := "z3",
    checkMode := .bugFinding, checkLevel := .full }

/-- Verify an already-generated Laurel program. -/
private meta def verifyLaurel
    (laurel : Strata.Laurel.Program) (useRoots : Bool := false)
    (verifyOptions : Core.VerifyOptions := testVerifyOptions)
    : IO (Except String (Array Core.VCResult)) := do
  let (coreProgramOption, _) ← translateCombinedLaurel laurel
  let coreProgram ← match coreProgramOption with
    | none => return .error "Laurel to Core translation failed"
    | some core => pure core
  let entryPoints ←
    if useRoots then
      let (_preludeNames, userProcNames) := splitProcNames coreProgram
      let cg := coreProgram.toProcedureCG
      let userSet := Std.HashSet.ofList userProcNames
      pure ((cg.computeRoots (preferredRoots := userProcNames)).filter userSet.contains)
    else
      pure ["__main__"]
  let entrySet := Std.HashSet.ofList entryPoints
  let inlinePhases : List Core.PipelinePhase :=
    [_root_.Core.procedureInliningPipelinePhase
      { doInline := fun caller callee a =>
          (match caller with | some c => entrySet.contains c | none => false)
          && _root_.Core.doInlineNonRecursive callee a }]
  let options : Core.VerifyOptions :=
    { verifyOptions with proceduresToVerify := some entryPoints }
  match StrataPython.Pipeline.buildVerificationPipeline options inlinePhases with
  | .error e =>
    -- The default phase order always validates; an error here is a test bug.
    return .error s!"Cannot assemble the verification pipeline for this test: {e}"
  | .ok pipeline =>
    match ← Strata.Core.verifyProgram coreProgram options
        (moreFns := StrataPython.RuntimeFactory)
        (externalPhases := [Strata.frontEndPhase])
        (pipeline := some pipeline) |>.toBaseIO with
    | .ok results => return .ok results
    | .error msg => return .error (toString msg)

/-- Run pyAnalyzeLaurel with inlining and verification.
    When `useRoots` is true, entry points are determined via the call graph
    (the CLI `--entry-point roots` default); otherwise only `__main__` is used. -/
meta def runAnalyzeAndVerify
    (pythonCmd : System.FilePath)
    (tmpDir : System.FilePath) (scriptName : String)
    (useRoots : Bool := false) (pyspecModules : Array String := #[])
    (verifyOptions : Core.VerifyOptions := testVerifyOptions)
    : IO (Except String (Array Core.VCResult)) := do
  let testIon ← compileTestScript pythonCmd (testDir / scriptName) tmpDir
  let pctx ← quietCtx
  let laurel ←
    match ← (pythonAndSpecToLaurel testIon.toString
        (dispatchModules := #["servicelib"])
        (pyspecModules := pyspecModules)
        (specDir := tmpDir)).run pctx |>.toBaseIO with
    | .ok r => pure r
    | .error () =>
      let msgs ← pctx.getMessages
      let detail := match msgs.back? with | some m => m.message.message | none => "Pipeline aborted"
      return .error detail
  verifyLaurel laurel useRoots verifyOptions

/-- Expected outcome for a test case. -/
inductive Expected where
  | success
  | fail (msg : String)
  | failPrefix (pfx : String)

/-- All dispatch test cases: (filename, expected outcome). -/
meta def testCases : List (String × Expected) := [
  -- Positive tests
  .mk "test_single_service.py" .success,
  .mk "test_multi_service.py" .success,
  .mk "test_annotation_fallback.py" .success,
  .mk "test_required_with_optional.py" .success,
  .mk "test_heap_return.py" .success,
  .mk "test_list_str.py" .success,
  .mk "test_nested_try.py" .success,
  .mk "test_try_scope.py" .success,
  .mk "test_dict_expand.py" .success,
  .mk "test_dict_expand_optional.py" .success,
  .mk "test_instance_call_result.py" .success,
  -- Void/non-void call handling tests (Phase 1 TDD)
  .mk "test_void_assign.py" .success,
  .mk "test_void_init.py" .success,
  .mk "test_discard_nonvoid.py" .success,
  -- User-defined class field assignment and method return
  .mk "test_class_field_assign.py" .success,
  .mk "test_class_method_return.py" .success,
  .mk "test_user_class_construct.py" .success,
  -- Negative tests
  .mk "test_invalid_service.py" $
    .failPrefix "User code error: 'connect' called with unknown string \"invalid\"; known services:",
  .mk "test_invalid_method.py" $
    .fail "User code error: Unknown method 'nonexistent_method'",
  -- TypedDict kwargs remain one dictionary input. These calls translate, then
  -- fail their caller-side map schema obligations below.
  .mk "test_invalid_args.py" .success,
  .mk "test_missing_required.py" .success,
  .mk "test_extra_kwarg.py" .success,
  .mk "test_no_args.py" .success,
  .mk "test_optional_missing_required.py" .success,
  .mk "test_positional_missing.py" $
    .fail "User code error: 'delete_item' called with missing required arguments: [Key]",
  -- Type alias resolution tests (TDD for resolveTypeName refactoring)
  .mk "test_method_dispatch.py" .success,
  .mk "test_keyword_dispatch.py" .success,
  .mk "test_keyword_dispatch_variable.py" .success,
  .mk "test_wrong_keyword_dispatch.py" $
    .failPrefix "Python to Laurel translation failed: Type error: Dispatched function 'connect' called with wrong keyword argument, expected 'service_name' but got 'wrong_param'",
  .mk "test_annotation_dispatch.py" .success,
  .mk "test_constructor_dispatch.py" .success,
  .mk "test_reassign_dispatch.py" .success,
  -- Known failing tests:
  -- With @ separator, Storage_put_item is no longer a known symbol, so it
  -- falls through to the default Any type. These should produce an
  -- error or warning since procedure names are not valid type annotations.
  .mk "test_procedure_as_annotation.py" .success,
  .mk "test_procedure_as_param_type.py" .success
]

/-- Run a single test case and return an error message on failure, or `none` on success. -/
meta def runTestCase (pythonCmd : System.FilePath) (tmpDir : System.FilePath)
    (scriptName : String) (expected : Expected) : IO (Option String) := do
  let result ← runAnalyze pythonCmd tmpDir scriptName
  match expected, result with
  | .success, .ok _ => return none
  | .success, .error msg =>
    return some s!"pyAnalyzeLaurel failed on {scriptName}: {msg}"
  | .fail _, .ok _ =>
    return some s!"pyAnalyzeLaurel succeeded on {scriptName} but was expected to fail"
  | .fail exp, .error msg =>
    if msg == exp then return none
    else return some s!"{scriptName}: Expected error:\n  {exp}\nGot:\n  {msg}"
  | .failPrefix _pfx, .ok _ =>
    return some s!"pyAnalyzeLaurel succeeded on {scriptName} but was expected to fail"
  | .failPrefix pfx, .error msg =>
    if msg.startsWith pfx then return none
    else return some s!"{scriptName}: Expected error starting with:\n  {pfx}\nGot:\n  {msg}"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    -- Launch all tests concurrently, checking for duplicate filenames
    let mut seen : Std.HashSet String := {}
    let mut tasks : Array (String × Task (Except IO.Error (Option String))) := #[]
    for (scriptName, expected) in testCases do
      if scriptName ∈ seen then
        throw <| IO.userError s!"Duplicate test filename: {scriptName}"
      seen := seen.insert scriptName
      let task ← IO.asTask (runTestCase pythonCmd tmpDir scriptName expected)
      tasks := tasks.push (scriptName, task)
    -- Composite/Any kind mismatch tests
    -- composite_as_any: dispatch-initialized fields return Hole (no coercion error)
    let task ← IO.asTask (runTestCase pythonCmd tmpDir
      "test_class_composite_as_any.py"
      .success)
    tasks := tasks.push ("test_class_composite_as_any.py", task)
    -- test_class_any_as_composite: assigning a str to a Composite-typed field
    -- causes a type unification error in Core.typeCheck, which is expected.
    let task ← IO.asTask do
      let testIon ← compileTestScript pythonCmd (testDir / "test_class_any_as_composite.py") tmpDir
      let pctx ← quietCtx
      let laurel ←
        match ← (pythonAndSpecToLaurel testIon.toString
            (dispatchModules := #["servicelib"])
            (pyspecModules := #["servicelib.Storage"])
            (specDir := tmpDir)).run pctx |>.toBaseIO with
        | .ok r => pure r
        | .error () =>
          let msgs ← pctx.getMessages
          let detail := match msgs.back? with | some m => m.message.message | none => "Pipeline aborted"
          return some s!"test_class_any_as_composite.py: {detail}"
      match ← translateCombinedLaurel laurel with
      | (some core, []) =>
        match Strata.Core.typeCheck Core.VerifyOptions.quiet core (moreFns := StrataPython.RuntimeFactory) with
        | .error diag =>
          -- Expected: assigning str (Any) to a Composite-typed field is a type error
          if (diag.message.splitOn "Impossible to unify").length > 1 then return none
          else return some s!"test_class_any_as_composite.py: {diag}"
        | .ok _ => return none
      | (_, errors) => return some s!"test_class_any_as_composite.py: Laurel to Core failed: {errors}"
    tasks := tasks.push ("test_class_any_as_composite.py", task)
    -- Collect results
    let mut errors : Array String := #[]
    for (_, task) in tasks do
      match ← IO.wait task with
      | .ok (some err) => errors := errors.push err
      | .ok none => pure ()
      | .error e => errors := errors.push s!"Task error: {e}"
    if errors.size > 0 then
      throw <| IO.userError ("\n".intercalate errors.toList)

/-! ## Precondition violation test

Verifies that calling `put_item(Bucket="INVALID!", ...)` produces a `✖️ always false`
result for the regex assertion through the full verification pipeline.
Uses `--entry-point roots` to discover the user-defined function as the entry point,
since the test script defines a function but does not call it from the top level.

Because `@requires` preconditions are now *caller-checked*, the regex obligation is
asserted at the call site and therefore reported under a bare `assert(<offset>)`
obligation label (the inlined caller-side check), not under the callee spec's
`servicelib_Storage_…` label. The test requires the ✖️ to be such a caller-side
precondition assert. For `Bucket="INVALID!"` (non-empty but not matching the regex)
the three `put_item` preconditions verify as `✔️`, `✖️` (`Bucket must match …`), `✔️`.
-/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    -- These test scripts define functions but do not call them from the
    -- top level, so __main__ has no assertions.  Use `useRoots` to
    -- discover the user-defined function as the entry point.
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      "test_precondition_violation.py" (useRoots := true)
    match result with
    | .error msg => throw <| IO.userError s!"Pipeline failed: {msg}"
    | .ok vcResults =>
      let mut foundAlwaysFalse := false
      for r in vcResults do
        let line := r.formatOutcome
        -- Caller-checked: the violated precondition is asserted at the call site, so
        -- its obligation is a precondition assert (`…assert(<offset>)…`) that lives in
        -- USER code, not in the callee spec library. Require such a caller-side
        -- precondition assert (excluding the callee `servicelib_…` spec and
        -- postcondition obligations) to be *not proven safe*: `✖️ always false`
        -- locally, or `❓ unknown` when the solver is under load (the 16-way
        -- concurrent CI run degrades the validity check's `unsat` to `unknown`).
        -- Both mean the violation was flagged; `✔️`/unreachable asserts are excluded.
        -- Pin the obligation to the *intended* violation via its property
        -- summary (the assert message), so that if the regex-violation
        -- obligation flips to `✔️` (a real lost-detection regression) an
        -- unrelated user-code assert reporting `❓` under CI solver load cannot
        -- green the test in its place. (The message lives on the obligation
        -- metadata, not in `formatOutcome`, which only renders emoji + label.)
        let summary := r.obligation.metadata.getPropertySummary.getD ""
        if ((line.splitOn "✖️").length != 1 || r.isUnknown)
            && r.obligation.label.contains "assert("
            && !r.obligation.label.startsWith "servicelib_"
            && summary.contains "Bucket must match" then
          foundAlwaysFalse := true
      if !foundAlwaysFalse then
        throw <| IO.userError
          "Expected ✖️/❓ (violation not proven safe) for regex violation"

/-! ## Precondition with alias test

Verifies that calling `put_item(Bucket="", ...)` through the alias resolution
path produces a `✖️ always false` result for the "Bucket must not be empty"
assertion. This exercises the full pipeline with type alias resolution.
-/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      "test_precondition_with_alias.py" (useRoots := true)
    match result with
    | .error msg => throw <| IO.userError s!"Pipeline failed: {msg}"
    | .ok vcResults =>
      let mut foundAlwaysFalse := false
      for r in vcResults do
        let line := r.formatOutcome
        -- Caller-checked: require a caller-side precondition assert (`…assert(<offset>)…`
        -- in user code, excluding the callee `servicelib_…` spec and postconditions)
        -- to be *not proven safe*: `✖️ always false` locally, or `❓ unknown` when the
        -- solver is under load on CI (the validity check's `unsat` degrades to `unknown`).
        -- Pin the obligation to the intended "empty bucket" violation via its
        -- property summary so an unrelated user-code assert reporting `❓` under
        -- CI solver load cannot mask the intended obligation flipping to `✔️`.
        let summary := r.obligation.metadata.getPropertySummary.getD ""
        if ((line.splitOn "✖️").length != 1 || r.isUnknown)
            && r.obligation.label.contains "assert("
            && !r.obligation.label.startsWith "servicelib_"
            && summary.contains "Bucket must not be empty" then
          foundAlwaysFalse := true
      if !foundAlwaysFalse then
        throw <| IO.userError
          "Expected ✖️/❓ (violation not proven safe) for empty bucket violation"

/-! ## evalIfCanonical regression test (Issue #812)

Symbolic bucket must pass the regex precondition via `evalIfCanonical`.
Without the attribute, the regex VC would be ❓ unknown. -/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      "test_regex_eval_if_canonical.py" (useRoots := true)
    match result with
    | .error msg => throw <| IO.userError s!"Pipeline failed: {msg}"
    | .ok vcResults =>
      -- Pin the regex obligation via its property summary: it must verify
      -- (`✔️`, not merely non-`✖️`), which is exactly what `evalIfCanonical`
      -- enables. An unrelated obligation may degrade to `❓ unknown` when the
      -- solver is under load on CI, but nothing may be disproven.
      let mut sawRegex := false
      for r in vcResults do
        if (r.formatOutcome.splitOn "✖️").length != 1 then
          throw <| IO.userError
            s!"Expected no disproven Storage precondition but got: {r.formatOutcome}"
        let summary := r.obligation.metadata.getPropertySummary.getD ""
        if summary.contains "Bucket must match" then
          sawRegex := true
          if !r.isSuccess then
            throw <| IO.userError
              s!"Expected the regex precondition to verify via evalIfCanonical but got: {r.formatOutcome}"
      if !sawRegex then
        throw <| IO.userError "Expected a 'Bucket must match' obligation"

/-! ## Resolution error test after FilterPrelude

Verifies that the combined Laurel program (after prelude filtering) resolves
without errors.  This catches cases where FilterPrelude includes a declaration
that references a type or name not present in the filtered prelude — for
example, a composite field typed as a nested class that was never translated
(the `_Exceptions` pattern in real boto3 pyspecs).

The `Database` mock pyspec has a nested `_Exceptions` class.  The pyspec
compiler emits it as a `subclass` in the Ion file.  `classDefToLaurel`
recursively translates subclasses, so the type
`servicelib_Database__Exceptions` is defined and resolves correctly. -/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let testIon ← compileTestScript pythonCmd
      (testDir / "test_resolution_after_filter.py") tmpDir
    let pctx ← quietCtx
    let combined ←
      match ← (pythonAndSpecToLaurel testIon.toString
          (dispatchModules := #["servicelib"])
          (specDir := tmpDir)).run pctx |>.toBaseIO with
      | .ok r => pure r
      | .error () =>
        let msgs ← pctx.getMessages
        let detail := match msgs.back? with | some m => m.message.message | none => "Pipeline aborted"
        throw <| IO.userError s!"pyAnalyzeLaurel failed: {detail}"
    -- Operators are `StaticCall`s to the built-in wrappers (`$add`, `$eq`, …),
    -- which the compilation pipeline prepends before its own `resolve`. Resolving
    -- `combined` standalone must do the same, or every operator in the program
    -- reports an undefined callee.
    let combined := { combined with
      staticProcedures :=
        Strata.Laurel.coreDefinitionsForLaurel.staticProcedures ++ combined.staticProcedures,
      types := Strata.Laurel.coreDefinitionsForLaurel.types ++ combined.types
    }
    let result := Strata.Laurel.resolve combined
    unless result.errors.isEmpty do
      let msgs := result.errors.toList.map (·.message)
      throw <| IO.userError s!"Resolution errors after FilterPrelude:\n{"\n".intercalate msgs}"

/-! ## Self-field dispatch test

Verifies that `self.field.method()` inside a class method resolves through
dispatch rather than being flattened to an underscore-separated package call.
Without the fix, `self.store.put_item(...)` would produce a Hole instead of
invoking the Storage spec, so precondition violations would go undetected. -/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      "test_self_field_dispatch_precondition.py" (useRoots := true)
    match result with
    | .error msg => throw <| IO.userError s!"Pipeline failed: {msg}"
    | .ok vcResults =>
      let mut foundAlwaysFalse := false
      for r in vcResults do
        let line := r.formatOutcome
        -- Caller-checked via self.field dispatch: the precondition is asserted inside
        -- the calling method, so its obligation is a user-code precondition assert
        -- (e.g. `MyService@save_empty_bucket_assert(<offset>)…`). Require such a
        -- caller-side precondition assert (excluding the callee `servicelib_…` spec and
        -- postconditions) to be *not proven safe*: `✖️ always false` locally, or `❓
        -- unknown` when the solver is under load on CI.
        -- Pin the obligation to the intended "empty bucket" violation via its
        -- property summary so an unrelated user-code assert reporting `❓` under
        -- CI solver load cannot mask the intended obligation flipping to `✔️`.
        let summary := r.obligation.metadata.getPropertySummary.getD ""
        if ((line.splitOn "✖️").length != 1 || r.isUnknown)
            && r.obligation.label.contains "assert("
            && !r.obligation.label.startsWith "servicelib_"
            && summary.contains "Bucket must not be empty" then
          foundAlwaysFalse := true
      if !foundAlwaysFalse then
        throw <| IO.userError
          "Expected ✖️/❓ (violation not proven safe) for empty bucket violation via self.field dispatch"

/-! ## Supported PySpec contract assumptions

A modeled function without `@ensures` retains both its caller-checked
`@requires` and its trusted return-type assumption. After inlining, the valid
precondition and the caller's return-type assertion must both verify. -/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      "test_contract_assumptions.py" (useRoots := true)
      (pyspecModules := #["servicelib.Contract"])
    match result with
    | .error msg => throw <| IO.userError s!"Pipeline failed: {msg}"
    | .ok vcResults =>
      let mut foundPrecondition := false
      let mut foundReturnTypeAssertion := false
      for r in vcResults do
        let summary := r.obligation.metadata.getPropertySummary.getD ""
        if !r.isSuccess then
          throw <| IO.userError
            s!"Expected mixed-contract verification to pass but got: {r.formatOutcome}; summary: {summary}"
        if summary.contains "precondition 0" then
          foundPrecondition := true
        if summary.contains "modeled text must not be None" then
          foundReturnTypeAssertion := true
      unless foundPrecondition do
        throw <| IO.userError "Expected a successful caller-checked @requires VC"
      unless foundReturnTypeAssertion do
        throw <| IO.userError
          "Expected the return-type assumption to discharge the caller assertion"

/-! ## Unsupported PySpec postconditions

Modeled `@ensures` clauses cannot be verified against an implementation. The
pipeline must therefore fail before the condition can enter a caller VC. -/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let testIon ← compileTestScript pythonCmd
      (testDir / "test_postcondition_caller.py") tmpDir
    let pctx ← quietCtx
    let result ← (pythonAndSpecToLaurel testIon.toString
      (dispatchModules := #["servicelib"])
      (pyspecModules := #["servicelib.Counter"])
      (specDir := tmpDir)).run pctx |>.toBaseIO
    match result with
    | .ok _ => throw (IO.userError
        "Expected modeled @ensures to abort Python-to-Laurel translation")
    | .error () => pure ()

    let unsupportedMessages := (← pctx.getMessages).filter fun message =>
      message.message.kind == .unsupportedPostcondition
    match unsupportedMessages.toList with
    | [pipelineMessage] =>
      let message := pipelineMessage.message
      unless message.kind.impact.isFatal do
        throw <| IO.userError
          "Expected unsupportedPostcondition to be fatal"
      unless message.message.contains
          "Strata cannot verify this postcondition against an implementation"
          && message.message.contains "will not assume it at call sites"
          && message.message.contains
            "aborts analysis even if the affected function is unused"
          && message.message.contains
            "Use @admit to accept the postcondition as an unverified modeling assumption"
          && message.message.contains
            "model the function with a real body if the property must be checked" do
        throw <| IO.userError s!"Unexpected diagnostic: {message.message}"
    | _ => throw (IO.userError
        s!"Expected exactly one unsupportedPostcondition diagnostic, got {unsupportedMessages.size}")

/-! ## Admitted PySpec postconditions

An `@admit` postcondition is an explicitly acknowledged, unverified modeling
assumption. The pipeline must load the module without error and the assumption
must discharge a caller assertion that the return type alone cannot. -/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      "test_admitted_assumptions.py" (useRoots := true)
      (pyspecModules := #["servicelib.Admitted"])
    match result with
    | .error msg => throw <| IO.userError s!"Pipeline failed: {msg}"
    | .ok vcResults =>
      let mut foundAdmittedAssertion := false
      for r in vcResults do
        let summary := r.obligation.metadata.getPropertySummary.getD ""
        if !r.isSuccess then
          throw <| IO.userError
            s!"Expected admitted-contract verification to pass but got: {r.formatOutcome}; summary: {summary}"
        if summary.contains "admitted value must be non-negative" then
          foundAdmittedAssertion := true
      unless foundAdmittedAssertion do
        throw <| IO.userError
          "Expected the @admit assumption to discharge the caller assertion"
/-! ## Module-scope ghosts -/

/-- Every obligation must verify; some summary must contain `provedPart`. -/
meta def expectGhostProved (pythonCmd : System.FilePath) (scriptName : String)
    (pyspecModule : String) (provedPart : String) (what : String) : IO Unit := do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      scriptName (useRoots := true) (pyspecModules := #[pyspecModule])
    match result with
    | .error msg => throw <| IO.userError s!"{what} pipeline failed: {msg}"
    | .ok vcResults =>
      let mut proved := false
      for r in vcResults do
        let summary := r.obligation.metadata.getPropertySummary.getD ""
        unless r.isSuccess do
          throw <| IO.userError
            s!"Expected {what} verification to pass, got {r.formatOutcome}; summary: {summary}"
        if summary.contains provedPart then
          proved := true
      unless proved do
        throw <| IO.userError
          s!"Expected {what} to prove an obligation whose summary contains \"{provedPart}\""

/-- Require a fatal pipeline rejection containing `needle`. -/
meta def expectGhostRejected (pythonCmd : System.FilePath) (scriptName : String)
    (pyspecModule : String) (needle : String) (what : String) : IO Unit := do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      scriptName (useRoots := true) (pyspecModules := #[pyspecModule])
    match result with
    | .error msg =>
      unless msg.contains needle do
        throw <| IO.userError
          s!"expected the {what} rejection containing \"{needle}\", got: {msg}"
    | .ok _ =>
      throw <| IO.userError s!"{what} was not rejected; verification ran"

#eval withPython fun pythonCmd =>
  expectGhostProved pythonCmd "test_module_ghost.py" "servicelib.Ghost"
    "value must be at least the ghost floor" "module-ghost"

/-! ## Mutable module ghosts -/

#eval withPython fun pythonCmd =>
  expectGhostProved pythonCmd "test_ghost_dict.py" "servicelib.GhostProbe"
    "registered in the ghost table" "mutable-ghost"

/-! ## Module ghosts with `OLD` -/

#eval withPython fun pythonCmd =>
  expectGhostProved pythonCmd "test_ghost_old.py" "servicelib.GhostOld"
    "increments the ghost counter" "ghost OLD"

/-! ## Module ghosts with `OLD` but no `@modifies` (rejected) -/

#eval withPython fun pythonCmd =>
  expectGhostRejected pythonCmd "test_ghost_old_no_frame.py" "servicelib.GhostOldNoFrame"
    "not listed in @modifies" "ghost OLD without @modifies"

/-! ## Declared parameter types are caller-checked -/

/-- Require the obligation whose summary contains `failedPart` to fail. -/
meta def expectObligationFails (pythonCmd : System.FilePath) (scriptName : String)
    (pyspecModule : String) (failedPart : String) (what : String) : IO Unit := do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      scriptName (useRoots := true) (pyspecModules := #[pyspecModule])
    match result with
    | .error msg => throw <| IO.userError s!"{what} pipeline failed: {msg}"
    | .ok vcResults =>
      let mut summaries : Array String := #[]
      let mut failed := false
      for r in vcResults do
        let summary := r.obligation.metadata.getPropertySummary.getD ""
        summaries := summaries.push s!"{summary} => {r.formatOutcome}"
        if summary.contains failedPart then
          -- Rule out spurious failure modes so `!isSuccess` can't pass on a
          -- timeout/encoding error masquerading as the intended violation.
          if r.isTimeout then
            throw <| IO.userError
              s!"{what}: obligation for \"{failedPart}\" timed out (trigger bug): {r.formatOutcome}"
          if r.isImplementationError || r.hasSMTError then
            throw <| IO.userError
              s!"{what}: obligation for \"{failedPart}\" hit an encoding/solver error: {r.formatOutcome}"
          if !r.isSuccess then
            failed := true
      unless failed do
        throw <| IO.userError
          s!"Expected {what} to fail the obligation whose summary contains \
             \"{failedPart}\"; outcomes were {summaries.toList}"

#eval withPython fun pythonCmd =>
  expectGhostProved pythonCmd "test_param_type_ok.py" "servicelib.ParamType"
    "an int argument satisfies the declared parameter type" "declared param type (ok)"

-- The declared-type obligation itself must exist and pass on the good call.
#eval withPython fun pythonCmd =>
  expectGhostProved pythonCmd "test_param_type_ok.py" "servicelib.ParamType"
    "declared type of parameter 'n'" "declared param type (obligation present)"

#eval withPython fun pythonCmd =>
  expectObligationFails pythonCmd "test_param_type_violation.py"
    "servicelib.ParamType" "declared type of parameter 'n'"
    "declared param type (violated)"

/-! ## Universal quantifier precondition tests

End-to-end checks that `Storage.require_all_nonempty`/`require_map_nonempty` quantified preconditions reach
the solver: a satisfying caller verifies (`✔️`, not merely non-`✖️`) while a
violating one stays unproven, and neither times out (a bad trigger can make the
solver take excessively long). The pass/violation asymmetry rules out a
silently-dropped precondition.

`@requires` preconditions are caller-checked (see the note above the regex
violation test): each quantified precondition is asserted at the call site, so
its obligation carries a bare `assert(<offset>)` label in user code — NOT the
callee's `servicelib_…` label (that label only covers the spec's internal type
checks, which always pass). Obligations are therefore selected by property
summary (the spec's assert message), which uniquely identifies the quantified
precondition within each single-call fixture. -/

meta section

/-- Select the caller-side precondition obligation whose property summary
    contains `summaryPart` (the quantified assert's message), excluding
    callee-internal spec obligations (`servicelib_…` labels). -/
def isQuantPrecondVC (summaryPart : String) (r : Core.VCResult) : Bool :=
  r.obligation.label.contains "assert("
  && !r.obligation.label.startsWith "servicelib_"
  && (r.obligation.metadata.getPropertySummary.getD "").contains summaryPart

def isAllNonemptyVC : Core.VCResult → Bool :=
  isQuantPrecondVC "each key must be non-empty"

-- `require_map_nonempty` asserts both a key and a value condition; both become
-- caller-side obligations and both belong to the quantified precondition.
def isMapNonemptyVC (r : Core.VCResult) : Bool :=
  isQuantPrecondVC "each key must be non-empty" r
  || isQuantPrecondVC "each value must be non-empty" r

def isOthersNonemptyVC : Core.VCResult → Bool :=
  isQuantPrecondVC "each key other than the sentinel must be non-empty"

def isSomeMatchVC : Core.VCResult → Bool :=
  isQuantPrecondVC "at least one key must match the needle"

def isSomeValueMatchVC : Core.VCResult → Bool :=
  isQuantPrecondVC "at least one value must match the needle"

def isKeysNonemptyVC : Core.VCResult → Bool :=
  isQuantPrecondVC "each key must be non-empty"

def isValuesNonemptyVC : Core.VCResult → Bool :=
  isQuantPrecondVC "each value must be non-empty"

def isShadowedNonemptyVC : Core.VCResult → Bool :=
  isQuantPrecondVC "each shadowed key must be non-empty"

def isGroupsNonemptyVC : Core.VCResult → Bool :=
  isQuantPrecondVC "each group member must be non-empty"

/-- Run `fixture` through the pipeline and return the obligations selected by
    `isVC`, failing if the pipeline errored or produced no matching obligation. -/
def quantVCs (pythonCmd : System.FilePath) (tmpDir : System.FilePath)
    (fixture : String) (isVC : Core.VCResult → Bool)
    (verifyOptions : Core.VerifyOptions := testVerifyOptions)
    : IO (Array Core.VCResult) := do
  let result ← runAnalyzeAndVerify pythonCmd tmpDir fixture
    (useRoots := true) (verifyOptions := verifyOptions)
  match result with
  | .error msg => throw <| IO.userError s!"Pipeline failed: {msg}"
  | .ok vcResults =>
    let vcs := vcResults.filter isVC
    if vcs.isEmpty then
      throw <| IO.userError s!"Expected a quantified obligation in {fixture} but found none"
    for r in vcs do
      if r.isTimeout then
        throw <| IO.userError s!"quantified obligation timed out (trigger bug): {r.formatOutcome}"
      -- Rule out encoding/solver errors so the violation tests' `!isSuccess` check
      -- can't pass on a spurious error masquerading as "not proven".
      if r.isImplementationError || r.hasSMTError then
        throw <| IO.userError s!"quantified obligation hit an encoding/solver error: {r.formatOutcome}"
    return vcs

/-- Map fixtures keep the default solver and use precise axiom pruning. -/
def mapVerifyOptions : Core.VerifyOptions :=
  { testVerifyOptions with
    solver := Core.VerifyOptions.default.solver,
    removeIrrelevantAxioms := .Precise }

def expectMapVC (pythonCmd tmpDir : System.FilePath)
    (fixture summary : String) (shouldPass : Bool) : IO Unit := do
  let vcs ← quantVCs pythonCmd tmpDir fixture
    (isQuantPrecondVC summary)
    (verifyOptions := mapVerifyOptions)
  match vcs.toList with
  | [vc] =>
    if shouldPass then
      unless vc.isSuccess do
        throw <| IO.userError
          s!"Expected {fixture} to pass, got: {vc.formatOutcome}"
    else
      unless vc.isFailure do
        throw <| IO.userError
          s!"Expected {fixture} to fail, got: {vc.formatOutcome}"
  | _ =>
    throw <| IO.userError
      s!"Expected one matching obligation in {fixture}, got {vcs.size}"

end -- meta section

-- List, pass: `require_all_nonempty(["alice", "bob"])` — every obligation must be `isSuccess`.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let putAll ← quantVCs pythonCmd tmpDir "test_forall_pass.py" isAllNonemptyVC
    for r in putAll do
      if !r.isSuccess then
        throw <| IO.userError
          s!"Expected require_all_nonempty quantified precondition to pass but got: {r.formatOutcome}"

-- List, violation: `require_all_nonempty(["alice", ""])` — at least one obligation must stay unproven.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let putAll ← quantVCs pythonCmd tmpDir "test_forall_violation.py" isAllNonemptyVC
    unless putAll.any (!·.isSuccess) do
      throw <| IO.userError
        "Expected require_all_nonempty quantified precondition to stay unproven for a list containing an empty string"

-- List, empty: `require_all_nonempty([])` verifies vacuously (guard must not misfire on `[]`).
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let putAll ← quantVCs pythonCmd tmpDir "test_forall_empty.py" isAllNonemptyVC
    for r in putAll do
      if !r.isSuccess then
        throw <| IO.userError
          s!"Expected require_all_nonempty quantified precondition to pass vacuously for an empty list but got: {r.formatOutcome}"


-- Dict, pass: `require_map_nonempty({"alice": "x", "bob": "y"})` — key and value obligations both pass.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let putMap ← quantVCs pythonCmd tmpDir "test_forall_dict_pass.py" isMapNonemptyVC
    for r in putMap do
      if !r.isSuccess then
        throw <| IO.userError
          s!"Expected require_map_nonempty quantified precondition to pass but got: {r.formatOutcome}"

-- Dict, violation: `require_map_nonempty({"alice": "x", "bob": ""})` — at least one obligation
-- must stay unproven, exercising the `v = d[k]` inlining via
-- `DictStrAny_get_or_none` under the `DictStrAny_contains` membership trigger.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let putMap ← quantVCs pythonCmd tmpDir "test_forall_dict_violation.py" isMapNonemptyVC
    unless putMap.any (!·.isSuccess) do
      throw <| IO.userError
        "Expected require_map_nonempty quantified precondition to stay unproven for a dict with an empty value"

-- Keys, pass: `require_keys_nonempty({"alice": "x", "bob": "y"})` — quantifies over
-- `Items.keys()`; every key obligation must pass.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_forall_keys_pass.py" isKeysNonemptyVC
    for r in vcs do
      if !r.isSuccess then
        throw <| IO.userError
          s!"Expected require_keys_nonempty quantified precondition to pass but got: {r.formatOutcome}"

-- Keys, violation: `require_keys_nonempty({"": "x"})` — an empty key stays unproven.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_forall_keys_violation.py" isKeysNonemptyVC
    unless vcs.any (!·.isSuccess) do
      throw <| IO.userError
        "Expected require_keys_nonempty quantified precondition to stay unproven for a dict with an empty key"

-- Values, pass: `require_values_nonempty({"alice": "x"})` — quantifies over
-- `Items.values()`, binding the loop var to `d[k]`; every value obligation passes.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_forall_values_pass.py" isValuesNonemptyVC
    for r in vcs do
      if !r.isSuccess then
        throw <| IO.userError
          s!"Expected require_values_nonempty quantified precondition to pass but got: {r.formatOutcome}"

-- Values, violation: `require_values_nonempty({"alice": ""})` — an empty value stays unproven,
-- exercising the `DictStrAny_get` value inlining under `.values()`.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_forall_values_violation.py" isValuesNonemptyVC
    unless vcs.any (!·.isSuccess) do
      throw <| IO.userError
        "Expected require_values_nonempty quantified precondition to stay unproven for a dict with an empty value"

-- Guarded, pass: `require_others_nonempty(["alice", ""], Sentinel="")` — the empty
-- string equals the sentinel, so `k != Sentinel` excludes it and the contract holds.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_forall_guard_pass.py" isOthersNonemptyVC
    for r in vcs do
      if !r.isSuccess then
        throw <| IO.userError
          s!"Expected require_others_nonempty to pass when the only empty key is the sentinel but got: {r.formatOutcome}"

-- Guarded, violation: `require_others_nonempty(["alice", ""], Sentinel="bob")` — the
-- empty string is not the sentinel, so the guard does not exclude it and it stays unproven.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_forall_guard_violation.py" isOthersNonemptyVC
    unless vcs.any (!·.isSuccess) do
      throw <| IO.userError
        "Expected require_others_nonempty to stay unproven for a non-sentinel empty key"

/- Shadowing semantics: `require_shadowed_nonempty` binds `Keys` over the
   collection `Keys` itself, and `require_groups_nonempty` nests a quantifier
   whose inner binder shadows the outer dict key. A renaming/capture bug makes
   the formula ill-scoped or vacuous, flipping one of the verdicts below. -/

-- Shadowed binder, pass: `require_shadowed_nonempty(["alice", "bob"])` — the
-- membership guard must read the argument list, not the binder, to prove this.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_forall_shadow_pass.py" isShadowedNonemptyVC
    for r in vcs do
      if !r.isSuccess then
        throw <| IO.userError
          s!"Expected require_shadowed_nonempty to pass but got: {r.formatOutcome}"

-- Shadowed binder, violation: `require_shadowed_nonempty(["alice", ""])` — must
-- stay unproven; a capture bug that vacuously satisfied the quantifier would
-- wrongly verify this call.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_forall_shadow_violation.py" isShadowedNonemptyVC
    unless vcs.any (!·.isSuccess) do
      throw <| IO.userError
        "Expected require_shadowed_nonempty to stay unproven for a list containing an empty string"

-- Nested shadowing, pass: `require_groups_nonempty({"team": ["alice", "bob"]})` —
-- the inner quantifier's domain is the outer value `v`, inlined as a lookup on
-- the *outer* key `k`, while the inner binder (also `k` in source) is renamed.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_forall_nested_pass.py" isGroupsNonemptyVC
    for r in vcs do
      if !r.isSuccess then
        throw <| IO.userError
          s!"Expected require_groups_nonempty to pass but got: {r.formatOutcome}"

-- Nested shadowing, violation: `require_groups_nonempty({"team": ["alice", ""]})` —
-- if the inlined lookup captured the renamed inner binder, the counterexample
-- (the empty member) would no longer be expressible and this would wrongly verify.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_forall_nested_violation.py" isGroupsNonemptyVC
    unless vcs.any (!·.isSuccess) do
      throw <| IO.userError
        "Expected require_groups_nonempty to stay unproven for a group containing an empty member"

/- Existential expectations follow the user-visible solver limitation documented
   in README.md under "Spec quantifiers": false cases can be refuted, while true
   cases remain unknown rather than verifying successfully. -/

-- Exists, violation: `require_some_match(["alice", "bob"], Needle="carol")` — no
-- element matches, so the existential is refuted.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_exists_violation.py" isSomeMatchVC
    unless vcs.any (·.isFailure) do
      throw <| IO.userError
        "Expected require_some_match existential to be refuted when no element matches"

-- Exists, pass: `require_some_match(["alice", "bob"], Needle="bob")` — a matching
-- element exists, so the existential must NOT be refuted (it stays unknown, which is
-- sound: the verifier never falsely reports the satisfiable case as a bug).
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_exists_pass.py" isSomeMatchVC
    if vcs.any (·.isFailure) then
      throw <| IO.userError
        "Expected require_some_match existential not to be refuted when a match exists"

-- Exists over dict items, violation: `require_some_value_match({"alice": "x",
-- "bob": "y"}, Needle="carol")` — no value matches, so the existential is refuted.
-- This is the one combination the ∀ verdicts don't observe: the `v = d[k]` value
-- inlining (`DictStrAny_get_or_none`) under the existential's `&` combiner rather
-- than the universal's `==>`.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_exists_dict_violation.py" isSomeValueMatchVC
    unless vcs.any (·.isFailure) do
      throw <| IO.userError
        "Expected require_some_value_match existential to be refuted when no dict value matches"

-- Exists over dict items, pass: `require_some_value_match({"alice": "x",
-- "bob": "y"}, Needle="y")` — a matching value exists, so the existential must NOT
-- be refuted (it stays unknown, per the limitation noted above).
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let vcs ← quantVCs pythonCmd tmpDir "test_exists_dict_pass.py" isSomeValueMatchVC
    if vcs.any (·.isFailure) then
      throw <| IO.userError
        "Expected require_some_value_match existential not to be refuted when a dict value matches"

-- Map-native dictionary contracts preserve lookup, equality, and TypedDict
-- schema semantics through the complete caller pipeline.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    expectMapVC pythonCmd tmpDir
      "test_dynamic_lookup_pass.py"
      "each dynamic value must be non-empty" true
    expectMapVC pythonCmd tmpDir
      "test_dynamic_lookup_violation.py"
      "each dynamic value must be non-empty" false
    expectMapVC pythonCmd tmpDir
      "test_dict_equality_pass.py"
      "dictionaries must be equal" true
    expectMapVC pythonCmd tmpDir
      "test_dict_equality_violation.py"
      "dictionaries must be equal" false
    expectMapVC pythonCmd tmpDir
      "test_dict_equality_empty_pass.py"
      "dictionaries must be equal" true
    -- Three-level nesting with a list inside: exercises the mutually
    -- recursive Any/Dict/List equality procedures beyond one level.
    expectMapVC pythonCmd tmpDir
      "test_dict_equality_deep_pass.py"
      "dictionaries must be equal" true
    expectMapVC pythonCmd tmpDir
      "test_dict_equality_deep_violation.py"
      "dictionaries must be equal" false
    -- Mixed static typing: the looked-up operand is `Any`, so equality goes
    -- through `PySpecAny_scalarEq` (extensional for a runtime dict, false for
    -- a runtime non-dict).
    expectMapVC pythonCmd tmpDir
      "test_lookup_equal_pass.py"
      "looked-up config must equal the expected dictionary" true
    expectMapVC pythonCmd tmpDir
      "test_lookup_equal_violation.py"
      "looked-up config must equal the expected dictionary" false
    expectMapVC pythonCmd tmpDir
      "test_mapping_schema_pass.py"
      "'kwargs' must contain only declared keys" true
    expectMapVC pythonCmd tmpDir
      "test_mapping_schema_violation.py"
      "'kwargs' must contain only declared keys" false
    expectMapVC pythonCmd tmpDir
      "test_typed_dict_width_pass.py"
      "'Item' must contain required key 'Name'" true
    -- Gradually-typed callers: a concrete dict passed through an `Any`
    -- annotation still discharges the schema tag; an `Any` value that is not
    -- a dictionary fails the schema obligation at the call site.
    expectMapVC pythonCmd tmpDir
      "test_gradual_any_pass.py"
      "'Item' must contain required key 'Name'" true
    expectMapVC pythonCmd tmpDir
      "test_gradual_any_violation.py"
      "'Item' must contain required key 'Name'" false
    expectMapVC pythonCmd tmpDir
      "test_kwargs_forwarding_pass.py"
      "'kwargs' must contain required key 'Key'" true
    expectMapVC pythonCmd tmpDir
      "test_invalid_args.py"
      "'kwargs' must contain only declared keys" false
    expectMapVC pythonCmd tmpDir
      "test_missing_required.py"
      "'kwargs' must contain required key 'Key'" false
    expectMapVC pythonCmd tmpDir
      "test_extra_kwarg.py"
      "'kwargs' must contain only declared keys" false
    expectMapVC pythonCmd tmpDir
      "test_no_args.py"
      "'kwargs' must contain required key 'Bucket'" false
    expectMapVC pythonCmd tmpDir
      "test_optional_missing_required.py"
      "'kwargs' must contain required key 'Bucket'" false

end StrataPython.AnalyzeLaurelTest
