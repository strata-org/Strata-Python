/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import StrataPython.PySpecPipeline
meta import StrataLaurel.Implementation.Resolution
meta import Strata.Transform.ProcedureInlining
meta import StrataPython.PyFactory
meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Util.V2Pipeline
meta import StrataPython

namespace StrataPython.AnalyzeV2PySpecTest

open StrataPython.V2TestUtil

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    let vc ← precondVC pythonCmd tmpDir "test_model_ok.py" #["servicelib.Contract"]
    unless vc.isSuccess do
      throw <| IO.userError s!"Expected the compliant precondition to pass: {vc.formatOutcome}"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    let vc ← precondVC pythonCmd tmpDir "test_model_violation.py" #["servicelib.Contract"]
    if vc.isSuccess then
      throw <| IO.userError "Expected the violated precondition to stay unproven"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    let vc ← precondVC pythonCmd tmpDir "test_pyspec_alias.py" #["servicelib.Contract"]
    unless vc.isSuccess do
      throw <| IO.userError s!"Expected the aliased call to pass: {vc.formatOutcome}"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Admitted"]
    let results ← runAndVerify pythonCmd tmpDir "test_model_admit.py" #["servicelib.Admitted"]
    let assertions := results.filter fun r =>
      (r.obligation.metadata.getPropertySummary.getD r.obligation.label).contains "assert("
    match assertions with
    | #[vc] =>
      let .ok outcome := vc.outcome
        | throw <| IO.userError s!"Assertion VC errored: {vc.formatOutcome}"
      -- Pin the outcome: validity proven and not vacuous, so a pass on
      -- unreachable code cannot silently satisfy this test.
      unless outcome.isPass && !outcome.unreachable do
        throw <| IO.userError
          s!"Expected the admitted postcondition to prove the assertion: {vc.formatOutcome}"
    | _ => throw <| IO.userError s!"Expected one assertion VC, got {assertions.size}"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    match (← runV2 pythonCmd tmpDir "test_model_ok.py" #["servicelib.Nonexistent"]).2 with
    | .error msg =>
      unless msg.contains "PySpec prelude construction failed" do
        throw <| IO.userError s!"Unexpected missing-module error: {msg}"
    | .ok _ => throw <| IO.userError "Expected a missing PySpec module to fail"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    let results ← runAndVerify pythonCmd tmpDir "test_model_ok.py"
    -- Without --pyspec exactly the user assert remains, and it is INCONCLUSIVE: the
    -- modelless call is an unresolved hole, so nothing can prove the assert. A spurious
    -- contract VC would raise the count; a resolved outcome would signal the model leaked.
    match results with
    | #[vc] =>
      -- Primary pin: the surviving VC is the user assert (by property), and it stays
      -- inconclusive because the modelless call is an unresolved hole.
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

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_method_dispatch.py" #[] "fetch_item"
      (dispatchModules := #["servicelib"])
    unless caller.contains "servicelib_Storage_Storage@get_item(" do
      throw <| IO.userError s!"Dispatch did not bind the Storage method:\n{caller}"

-- A dispatch-factory argument embedding a modeled call inside a conditional must keep
-- that call's obligations (the argument itself is discarded by the `New` lowering).
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage", "servicelib.Contract"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_dispatch_arg_effects.py"
      #["servicelib.Contract"] "connect_with_effectful_arg"
      (dispatchModules := #["servicelib"])
    unless caller.contains "servicelib_Contract_modeled_text(" do
      throw <| IO.userError s!"Dispatch arg effects were dropped:\n{caller}"

-- An annotated binding (`client: Any = connect(...)`) must recover the dispatch return
-- type so method calls resolve against the modeled class instead of a silent havoc.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_annassign_dispatch.py" #[] "fetch_item"
      (dispatchModules := #["servicelib"])
    unless caller.contains "servicelib_Storage_Storage@get_item(" do
      throw <| IO.userError s!"Annotated dispatch binding did not resolve the method:\n{caller}"

-- A same-name import next to a module-level binding (in either order) must not abort
-- elaboration, and the LATER binding wins, matching Python: in shadow_local the import
-- follows the assignment, so the call dispatches; in import_then_reassign the integer
-- assignment follows the import, so the addition lowers to arithmetic, not a dispatch.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let useIt ← dumpProcChunk pythonCmd tmpDir "test_import_shadow_local.py" #[] "use_it"
      (dispatchModules := #["servicelib"])
    unless useIt.contains "new servicelib_Storage_Storage" do
      throw <| IO.userError s!"Import after assignment did not dispatch:\n{useIt}"
    let useInt ← dumpProcChunk pythonCmd tmpDir "test_import_then_reassign.py" #[] "use_int"
      (dispatchModules := #["servicelib"])
    unless useInt.contains "PAdd(" && !useInt.contains "new servicelib" do
      throw <| IO.userError s!"Assignment after import did not win:\n{useInt}"

-- A dispatch-factory call whose result is discarded must still elaborate: the New is
-- bound to a temp instead of being emitted as a bare value statement.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_dispatch_discard.py" #[] "connect_discard"
      (dispatchModules := #["servicelib"])
    unless caller.contains "new servicelib_Storage_Storage" do
      throw <| IO.userError s!"Discarded dispatch call lost its allocation:\n{caller}"

-- An import nested in a top-level `try:` fallback must still install its callable;
-- only genuine assignments trigger the shadowing guard.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_conditional_import.py"
      #["servicelib.Contract"] "check_conditional_import"
    unless caller.contains "servicelib_Contract_modeled_text(" do
      throw <| IO.userError s!"Conditional import did not bind:\n{caller}"

-- A later import shadows an earlier same-name binder (Python order semantics): a direct
-- assignment, a for-loop binder, and an annotation-only `x: T` (which binds nothing).
-- Conversely a def BETWEEN the import and a later reassignment still sees the import,
-- and a FAILING import never evicts an earlier resolved callable.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    for (script, proc) in [("test_import_shadows_assign.py", "use_it"),
                           ("test_forloop_shadow.py", "use_it"),
                           ("test_annotation_only_import.py", "use_it"),
                           ("test_def_between_import_and_reassign.py", "use_y"),
                           ("test_valid_then_unresolved.py", "use_it")] do
      let caller ← dumpProcChunk pythonCmd tmpDir script #["servicelib.Contract"] proc
      unless caller.contains "servicelib_Contract_modeled_text(" do
        throw <| IO.userError s!"{script}: modeled call did not bind:\n{caller}"

-- A conditional reassignment after an import elaborates: the guarded assignment to the
-- declared module variable survives in `__main__`, and the def's read of the name lowers
-- to an opaque value (the conditional rebind means it may no longer be the callable).
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    let main ← dumpProcChunk pythonCmd tmpDir "test_conditional_reassign.py"
      #["servicelib.Contract"] "__main__"
    unless main.contains "modeled_text := 42" do
      throw <| IO.userError s!"Conditional reassign lost its assignment:\n{main}"
    let useIt ← dumpProcChunk pythonCmd tmpDir "test_conditional_reassign.py"
      #["servicelib.Contract"] "use_it"
    unless useIt.contains "modeled_text := hole$0()" do
      throw <| IO.userError s!"Callable-value read changed lowering:\n{useIt}"

-- A dispatch module reached through a local alias still dispatches, whether the alias
-- is a plain (`sl = servicelib`) or an annotated (`sl: Any = servicelib`) assignment,
-- while a same-named PARAMETER in a sibling function shadows the alias and must not.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    for script in ["test_module_via_alias.py", "test_annassign_alias.py"] do
      let factory ← dumpProcChunk pythonCmd tmpDir script #[] "factory"
        (dispatchModules := #["servicelib"])
      unless factory.contains "new servicelib_Storage_Storage" do
        throw <| IO.userError s!"{script}: aliased dispatch module did not dispatch:\n{factory}"
    let userFn ← dumpProcChunk pythonCmd tmpDir "test_module_via_alias.py" #[] "user_fn"
      (dispatchModules := #["servicelib"])
    if userFn.contains "new servicelib_Storage_Storage" then
      throw <| IO.userError s!"Parameter shadowing the alias still dispatched:\n{userFn}"

-- Rebinding the module NAME shadows dispatch too: to data (`servicelib: int = 42`),
-- as a for-loop target, as a `with ... as` target, as a for-loop target nested inside
-- an `if` (the rebind must escape the enclosing block), as a nested `def`/`class`
-- declared inside an `if` body, and as a `match` case pattern capture.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    for script in ["test_module_rebound.py", "test_forloop_rebinds_module.py",
                   "test_with_rebinds_module.py", "test_for_in_if_rebinds_module.py",
                   "test_def_in_if_rebinds_module.py", "test_class_in_if_rebinds_module.py",
                   "test_match_pattern_rebinds_module.py"] do
      let caller ← dumpProcChunk pythonCmd tmpDir script #[] "use_it"
        (dispatchModules := #["servicelib"])
      if caller.contains "new servicelib_Storage_Storage" then
        throw <| IO.userError s!"{script}: rebound module name still dispatched:\n{caller}"

-- A discarded class construction and a bare name mid-block must both elaborate.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_bare_classnew_midblock.py" #[] "use_it"
      (dispatchModules := #["servicelib"])
    unless caller.contains "Registry@__init__(" do
      throw <| IO.userError s!"Discarded class construction lost its init call:\n{caller}"

-- A bare import followed by a same-name assignment keeps the variable binding.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_bare_import_then_assign.py" #[] "use_it"
      (dispatchModules := #["servicelib"])
    unless caller.contains "LaurelResult := servicelib" && !caller.contains "havoc" do
      throw <| IO.userError s!"Assignment after bare import did not win:\n{caller}"

-- `connect(...)` on a user object is NOT a dispatch call: the call lowers through the
-- regular (unresolved) path with no dispatch allocation, and analysis completes.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_unrelated_connect.py" #[] "user_call"
      (dispatchModules := #["servicelib"])
    unless !caller.contains "new servicelib" && caller.contains "havoc" do
      throw <| IO.userError s!"Unrelated connect was treated as dispatch:\n{caller}"

-- A genuine dispatch call with the wrong keyword argument fails with V1's diagnostic.
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_keyword_dispatch_variable.py" #[]
      "keyword_dispatch_variable" (dispatchModules := #["servicelib"])
    unless !caller.contains "new servicelib" && caller.contains "havoc" do
      throw <| IO.userError s!"Variable dispatch arg did not fall back:\n{caller}"

-- A dispatch call with an unknown string literal must fail with the known-services
-- diagnostic instead of silently falling back to the regular call path.
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_unimported_connect.py" #[] "user_call"
      (dispatchModules := #["servicelib"])
    if caller.contains "new servicelib" then
      throw <| IO.userError s!"Unimported bare connect was treated as dispatch:\n{caller}"

-- Rebinding an imported MODELED FUNCTION under an `if` drops its contract for
-- later calls, exactly like a module rebind: no stale StaticCall to the model.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    let caller ← dumpProcChunk pythonCmd tmpDir "test_modeled_fn_rebound_in_if.py"
      #["servicelib.Contract"] "use_it"
    if caller.contains "servicelib_Contract_modeled_text(" then
      throw <| IO.userError s!"Rebound modeled function kept its stale contract:\n{caller}"

-- Direct rebinds drop the model too: a walrus in an assignment RHS, and a user
-- `def` that redefines the imported name (which must also NOT be emitted under
-- the model's Laurel procedure name).
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    for script in ["test_walrus_rebinds_model.py", "test_def_rebinds_model.py"] do
      let caller ← dumpProcChunk pythonCmd tmpDir script #["servicelib.Contract"] "use_it"
      if caller.contains "servicelib_Contract_modeled_text(" then
        throw <| IO.userError s!"{script}: rebound modeled function kept its stale contract:\n{caller}"

-- A `connect` imported from an UNRELATED module must not pick up the dispatch
-- table by name: no dispatch allocation for it. Same when the unrelated import
-- SHADOWS an earlier dispatch-module import of the name.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib", "servicelib.Storage"]
    for script in ["test_unrelated_import_connect.py", "test_reimport_revokes_dispatch.py"] do
      let caller ← dumpProcChunk pythonCmd tmpDir script #[]
        "user_call" (dispatchModules := #["servicelib"])
      if caller.contains "new servicelib" then
        throw <| IO.userError s!"{script}: connect was treated as dispatch:\n{caller}"

-- A walrus rebind takes effect WITHIN the same expression: the call after it in
-- one tuple must not bind the stale model contract. Same for walruses in a
-- subscript assignment target, a with-item, a class base, and an except-handler type.
#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupPySpecs pythonCmd tmpDir #["servicelib.Contract"]
    let main ← dumpProcChunk pythonCmd tmpDir "test_walrus_then_call_same_expr.py"
      #["servicelib.Contract"] "__main__"
    if main.contains "servicelib_Contract_modeled_text(" then
      throw <| IO.userError s!"Walrus-then-call bound the stale contract:\n{main}"
    for script in ["test_subscript_walrus_rebinds_model.py", "test_with_walrus_rebinds_model.py",
                   "test_class_base_walrus_rebinds_model.py",
                   "test_annotation_walrus_rebinds_model.py"] do
      let caller ← dumpProcChunk pythonCmd tmpDir script #["servicelib.Contract"] "use_it"
      if caller.contains "servicelib_Contract_modeled_text(" then
        throw <| IO.userError s!"{script}: walrus rebind kept the stale contract:\n{caller}"

-- A walrus in an except-handler TYPE cannot leak a stale contract either: V2
-- rejects non-catch-all handlers outright (fail closed), pinned here so a future
-- handler-type implementation must revisit the rebind semantics deliberately.
#eval withPython fun pythonCmd => do
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

end StrataPython.AnalyzeV2PySpecTest
