/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- The suite's helpers — `withPython` and the `V2TestUtil` runners — and the types the
-- bodies touch are re-exported to the generated children, which `#eval` those bodies.
public meta import Strata.SimpleAPI -- shake: keep
public meta import Strata.Transform.ProcedureInlining -- shake: keep
public meta import StrataLaurel.Implementation.Resolution -- shake: keep
public meta import StrataPython -- shake: keep
public meta import StrataPython.PyFactory -- shake: keep
public meta import StrataPython.PySpecPipeline -- shake: keep
public meta import StrataPythonTest.Util.Python -- shake: keep
public meta import StrataPythonTest.Util.V2Pipeline -- shake: keep
import Strata.Util.Tests

/-! ## AnalyzeV2PySpec tests (declared in one file, generated as child modules)

The V2 PySpec dispatch/resolution tests, declared here with `#test` and
generated as one child module per entry under `StrataPythonTestExtra/AnalyzeV2PySpec/Gen/`.
`testMain` runs the children concurrently, each `#eval`ing its body through `withPython`.

This is the static-declaration form of the child-module approach: the bodies are
distinct (not one-per-corpus-file), so they are written out here rather than produced
by `#test_for_each_file`. Each `#test` is named for what it checks — so a failure names
the case and the child filename is stable when a test is inserted — and carries a
comment stating the property under test. The generated child only `#eval`s that `def`
by name, and the header's imports and `open`s let the name resolve. Editing a body and
rebuilding regenerates the stale children and fails until they are committed. -/

open StrataPython
open StrataPython.V2TestUtil

-- A compliant call to a modeled precondition cannot be lowered by V2 while `Any` is not gradual.
#test "precond_compliant_passes" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_model_ok.py" #["servicelib.Contract"]

-- A violated modeled precondition cannot be lowered by V2 while `Any` is not gradual.
#test "precond_violation_unproven" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_model_violation.py" #["servicelib.Contract"]

-- A call through a PySpec alias cannot be lowered by V2 while `Any` is not gradual.
#test "precond_alias_passes" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_pyspec_alias.py" #["servicelib.Contract"]

-- An admitted postcondition proving a downstream assertion cannot be lowered by V2 while `Any` is not gradual.
#test "admitted_postcondition_proves_assert" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Admitted"]
    expectNoCore pythonCmd tmpDir "test_model_admit.py" #["servicelib.Admitted"]

-- A missing PySpec module fails prelude construction rather than proceeding silently.
#test "missing_pyspec_module_fails" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    match (← runV2 pythonCmd tmpDir "test_model_ok.py" #["servicelib.Nonexistent"]).2 with
    | .error msg =>
      unless msg.contains "PySpec prelude construction failed" do
        throw <| IO.userError s!"Unexpected missing-module error: {msg}"
    | .ok _ => throw <| IO.userError "Expected a missing PySpec module to fail"

-- Without --pyspec exactly the user assert remains, and it is inconclusive: no model
-- leaks in to prove it, and no spurious contract VC appears.
#test "modelless_assert_inconclusive" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    let results ← runAndVerify pythonCmd tmpDir "test_model_ok.py"
    -- Without --pyspec exactly the user assert remains, and it is INCONCLUSIVE: the
    -- modelless call is an unresolved hole, so nothing can prove the assert. A spurious
    -- contract VC would raise the count; a resolved outcome would signal the model leaked.
    match results with
    | #[vc] =>
      unless (vc.obligation.metadata.getPropertySummary.getD vc.obligation.label).contains "assert" do
        throw <| IO.userError "The surviving VC is not the user assert"
      unless vc.isUnknown do
        throw <| IO.userError
          s!"Expected the modelless assert to stay inconclusive: {vc.formatOutcome}"
      if (vc.obligation.metadata.getPropertySummary.getD "").contains "precondition 0" then
        throw <| IO.userError "A contract VC appeared without --pyspec"
    | _ =>
      throw <| IO.userError
        s!"Expected exactly the user assert VC without --pyspec, got {results.size}"

-- A dispatch-factory result binding the modeled class cannot be lowered by V2 while `Any` is not gradual.
#test "method_dispatch_binds_storage" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    expectNoCore pythonCmd tmpDir "test_method_dispatch.py" #[] (dispatchModules := #["servicelib"])

-- A dispatch-factory argument embedding a modeled call cannot be lowered by V2 while `Any` is not gradual.
#test "dispatch_arg_effects_kept" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage", "servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_dispatch_arg_effects.py" #["servicelib.Contract"] (dispatchModules := #["servicelib"])

-- An annotated dispatch binding (`client: Any = connect(...)`) cannot be lowered by V2 while `Any` is not gradual.
#test "annotated_dispatch_binding_resolves" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    expectNoCore pythonCmd tmpDir "test_annassign_dispatch.py" #[] (dispatchModules := #["servicelib"])

-- A same-name import next to a module-level binding cannot be lowered by V2 while `Any` is not gradual.
#test "import_and_binding_later_wins" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    expectNoCore pythonCmd tmpDir "test_import_shadow_local.py" #[] (dispatchModules := #["servicelib"])
    expectNoCore pythonCmd tmpDir "test_import_then_reassign.py" #[] (dispatchModules := #["servicelib"])

-- A dispatch-factory call whose result is discarded must still elaborate: the New is
-- bound to a temp instead of being emitted as a bare value statement.
#test "discarded_dispatch_elaborates" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_dispatch_discard.py" #[] "connect_discard"
      (dispatchModules := #["servicelib"])
    unless caller.contains "new servicelib_Storage_Storage" do
      throw <| IO.userError s!"Discarded dispatch call lost its allocation:\n{caller}"

-- An import nested in a top-level `try:` fallback cannot be lowered by V2 while `Any` is not gradual.
#test "conditional_import_binds" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_conditional_import.py" #["servicelib.Contract"]

-- A later import shadowing an earlier same-name binder cannot be lowered by V2 while `Any` is not gradual.
#test "later_import_shadows_binder" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_import_shadows_assign.py" #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_forloop_shadow.py" #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_annotation_only_import.py" #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_def_between_import_and_reassign.py" #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_valid_then_unresolved.py" #["servicelib.Contract"]

-- A conditional reassignment after an import cannot be lowered by V2 while `Any` is not gradual.
#test "conditional_reassign_elaborates" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_conditional_reassign.py" #["servicelib.Contract"]

-- A dispatch module reached through a local alias cannot be lowered by V2 while `Any` is not gradual.
#test "dispatch_via_alias_param_shadows" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    expectNoCore pythonCmd tmpDir "test_module_via_alias.py" #[] (dispatchModules := #["servicelib"])
    expectNoCore pythonCmd tmpDir "test_annassign_alias.py" #[] (dispatchModules := #["servicelib"])

-- Rebinding the module NAME shadows dispatch too: to data (`servicelib: int = 42`),
-- as a `with ... as` target, and as a nested `def`/`class` declared inside an `if` body.
-- The for-loop, nested for-loop and `match` capture rebinds cannot be lowered by V2
-- while `Any` is not gradual.
#test "module_name_rebind_shadows_dispatch" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    for script in ["test_module_rebound.py", "test_with_rebinds_module.py",
                   "test_def_in_if_rebinds_module.py", "test_class_in_if_rebinds_module.py"] do
      let caller ← dumpProcChunk pythonCmd tmpDir script #[] "use_it"
        (dispatchModules := #["servicelib"])
      if caller.contains "new servicelib_Storage_Storage" then
        throw <| IO.userError s!"{script}: rebound module name still dispatched:\n{caller}"
    for script in ["test_forloop_rebinds_module.py", "test_for_in_if_rebinds_module.py",
                   "test_match_pattern_rebinds_module.py"] do
      expectNoCore pythonCmd tmpDir script #[] (dispatchModules := #["servicelib"])

-- A discarded class construction and a bare name mid-block must both elaborate.
#test "discarded_classnew_elaborates" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_bare_classnew_midblock.py" #[] "use_it"
      (dispatchModules := #["servicelib"])
    unless caller.contains "Registry@__init__(" do
      throw <| IO.userError s!"Discarded class construction lost its init call:\n{caller}"

-- A bare import followed by a same-name assignment cannot be lowered by V2 while `Any` is not gradual.
#test "bare_import_then_assign_wins" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    expectNoCore pythonCmd tmpDir "test_bare_import_then_assign.py" #[] (dispatchModules := #["servicelib"])

-- `connect(...)` on a user object cannot be lowered by V2 while `Any` is not gradual.
#test "unrelated_connect_not_dispatch" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    expectNoCore pythonCmd tmpDir "test_unrelated_connect.py" #[] (dispatchModules := #["servicelib"])

-- A genuine dispatch call with the wrong keyword argument fails with V1's diagnostic.
#test "wrong_kwarg_dispatch_fails" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    match (← runV2 pythonCmd tmpDir "test_wrong_kwarg_dispatch_v2.py"
        (dispatchModules := #["servicelib"])).2 with
    | .error msg =>
      unless msg.contains "wrong keyword argument" do
        throw <| IO.userError s!"Unexpected wrong-kwarg error: {msg}"
    | .ok _ => throw <| IO.userError "Expected a wrong dispatch keyword to fail"

-- A dispatch call whose argument is a VARIABLE (not a string literal) falls back to the
-- regular resolution path: no dispatch allocation, the call lowers to a havoc.
#test "variable_dispatch_arg_falls_back" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_keyword_dispatch_variable.py" #[]
      "keyword_dispatch_variable" (dispatchModules := #["servicelib"])
    unless !caller.contains "new servicelib" && caller.contains "havoc" do
      throw <| IO.userError s!"Variable dispatch arg did not fall back:\n{caller}"

-- A dispatch call with an unknown string literal must fail with the known-services
-- diagnostic instead of silently falling back to the regular call path.
#test "invalid_service_string_fails" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    match (← runV2 pythonCmd tmpDir "test_invalid_service.py"
        (dispatchModules := #["servicelib"])).2 with
    | .error msg =>
      unless msg.contains "unknown string" do
        throw <| IO.userError s!"Unexpected invalid-service error: {msg}"
    | .ok _ => throw <| IO.userError "Expected an unknown dispatch string to fail"

-- A bare `connect(...)` that was never imported is a Python NameError, never a
-- dispatch: no allocation is emitted for it.
#test "unimported_connect_not_dispatch" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_unimported_connect.py" #[] "user_call"
      (dispatchModules := #["servicelib"])
    if caller.contains "new servicelib" then
      throw <| IO.userError s!"Unimported bare connect was treated as dispatch:\n{caller}"

-- Rebinding an imported modeled function under an `if` cannot be lowered by V2 while `Any` is not gradual.
#test "modeled_fn_rebound_in_if_drops_contract" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    expectNoCore pythonCmd tmpDir "test_modeled_fn_rebound_in_if.py" #["servicelib.Contract"]

-- Direct rebinds drop the model too: a walrus in an assignment RHS, and a user
-- `def` that redefines the imported name (which V2 cannot lower while `Any` is not gradual).
#test "direct_rebinds_drop_model" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_walrus_rebinds_model.py" #["servicelib.Contract"] "use_it"
    if caller.contains "servicelib_Contract_modeled_text(" then
      throw <| IO.userError s!"test_walrus_rebinds_model.py: rebound modeled function kept its stale contract:\n{caller}"
    expectNoCore pythonCmd tmpDir "test_def_rebinds_model.py" #["servicelib.Contract"]

-- A `connect` imported from an UNRELATED module must not pick up the dispatch
-- table by name: no dispatch allocation for it. Same when the unrelated import
-- SHADOWS an earlier dispatch-module import of the name.
#test "unrelated_import_connect_not_dispatch" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    for script in ["test_unrelated_import_connect.py", "test_reimport_revokes_dispatch.py"] do
      let caller ← dumpProcChunk pythonCmd tmpDir script #[]
        "user_call" (dispatchModules := #["servicelib"])
      if caller.contains "new servicelib" then
        throw <| IO.userError s!"{script}: connect was treated as dispatch:\n{caller}"

-- A walrus rebind in a with-item, a class base, or an annotation must not bind the stale
-- model contract. The same-expression and subscript-target walruses cannot be lowered by V2
-- while `Any` is not gradual.
#test "walrus_rebind_takes_effect_same_expr" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    for script in ["test_with_walrus_rebinds_model.py", "test_class_base_walrus_rebinds_model.py",
                   "test_annotation_walrus_rebinds_model.py"] do
      let caller ← dumpProcChunk pythonCmd tmpDir script #["servicelib.Contract"] "use_it"
      if caller.contains "servicelib_Contract_modeled_text(" then
        throw <| IO.userError s!"{script}: walrus rebind kept the stale contract:\n{caller}"
    for script in ["test_walrus_then_call_same_expr.py", "test_subscript_walrus_rebinds_model.py"] do
      expectNoCore pythonCmd tmpDir script #["servicelib.Contract"]

-- A walrus in an except-handler TYPE cannot leak a stale contract either: V2
-- rejects non-catch-all handlers outright (fail closed), pinned here so a future
-- handler-type implementation must revisit the rebind semantics deliberately.
#test "except_handler_walrus_rejected" => withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    match (← runV2 pythonCmd tmpDir "test_except_walrus_rebinds_model.py"
        #["servicelib.Contract"]).2 with
    | .error msg =>
      unless msg.contains "except" do
        throw <| IO.userError s!"Unexpected rejection for handler-type walrus: {msg}"
    | .ok (some _, diags) =>
      unless diags.any (·.message.contains "except") do
        throw <| IO.userError
          "Handler-type walrus was neither rejected nor diagnosed; check rebind semantics"
    | .ok (none, diags) =>
      unless diags.any (·.message.contains "except") do
        let msgs := String.intercalate "; " (diags.map (·.message))
        throw <| IO.userError s!"Expected the except-clause rejection, got: {msgs}"

#run_tests_as_modules "StrataPythonTestExtra/AnalyzeV2PySpec/Gen"
