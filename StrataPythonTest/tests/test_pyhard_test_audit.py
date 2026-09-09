"""Independent semantic audit metadata for the focused PyHard test suite."""

from __future__ import annotations


TEST_AUDIT: dict[str, dict[str, str]] = {
    "DispatchManifestTests.test_nested_attribute_prefixes_are_distinct_ordered_sites": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "Correctly proves that x.a, x.a.b, and x.a.b.ping are separate, "
            "ordered lookup sites. It checks site construction, not each row."
        ),
    },
    "DispatchManifestTests.test_mixed_lookup_chain_feeds_each_intermediate_result_forward": {
        "classification": "semantic",
        "verdict": "Exact end-to-end case",
        "assessment": (
            "Checks all five ordered residuals in x.a.b + d['key'].field, "
            "including each intermediate result tag, required-key totality, "
            "and the final exact int/int addition row."
        ),
    },
    "DispatchManifestTests.test_mro_member_field_property_and_missing_rows": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The inherited method owner, declared field, property getter, and "
            "missing-member AttributeError agree with the admitted MRO rules."
        ),
    },
    "DispatchManifestTests.test_generated_mro_owner_agrees_with_cpython": {
        "classification": "semantic",
        "verdict": "Differentially checked",
        "assessment": (
            "Compares the generated owner with CPython's actual MRO and "
            "inspect.getattr_static. Scope is the admitted single-inheritance case."
        ),
    },
    "DispatchManifestTests.test_builtin_attribute_resolution_uses_static_descriptor_lookup": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "Correctly resolves list.append directly to its builtin procedure "
            "and None result without constructing a bound method object."
        ),
    },
    "DispatchManifestTests.test_direct_invocation_records_binding_plan_without_method_value": {
        "classification": "representation",
        "verdict": "Exact on this case",
        "assessment": (
            "A direct method call resolves to one instance-bound procedure row "
            "without introducing a callable value into the tag domain."
        ),
    },
    "MultipleDispatchTests.test_strict_right_subclass_reflected_method_runs_first": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The B.__radd__ then A.__add__ order matches CPython's strict "
            "right-subclass reflected-method priority."
        ),
    },
    "MultipleDispatchTests.test_equal_types_do_not_get_reflected_second_attempt": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "Correctly suppresses a second reflected attempt for equal runtime "
            "types and retains the terminal TypeError."
        ),
    },
    "MultipleDispatchTests.test_exact_builtin_pairs_and_mixed_error_plan": {
        "classification": "semantic",
        "verdict": "Exact but narrow",
        "assessment": (
            "int+int, str+str, and int+str are correct. This test says nothing "
            "about arithmetic errors such as division by zero."
        ),
    },
    "MultipleDispatchTests.test_candidate_contract_prunes_unreachable_binary_fallback": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "A certified reflected method returning only int makes the forward "
            "fallback and terminal TypeError unreachable."
        ),
    },
    "MultipleDispatchTests.test_subscription_and_membership_have_operation_specific_rows": {
        "classification": "semantic",
        "verdict": "Corrected during audit",
        "assessment": (
            "The global rows now retain TypeError for an unhashable operand, "
            "while str-key residual rows remove it and dynamic rows retain it."
        ),
    },
    "BindingAnalysisTests.test_conditional_assignment_marks_read_maybe_unbound": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The join has one bound and one unbound predecessor, so the read is "
            "maybe-bound and can raise UnboundLocalError."
        ),
    },
    "BindingAnalysisTests.test_assignment_on_both_branches_is_definitely_bound": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "Both reachable predecessors bind value, so the post-diamond read "
            "is definitely bound."
        ),
    },
    "BindingAnalysisTests.test_delete_removes_binding": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The delete first reads a definitely bound slot and then makes the "
            "following read definitely unbound."
        ),
    },
    "BindingAnalysisTests.test_flow_locations_expose_the_three_point_binding_domain": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "Confirms the location state exposes maybe-bound independently from "
            "the int value tag."
        ),
    },
    "ValueSetAnalysisTests.test_strong_assignment_kills_old_tag": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The second assignment kills NoneType; only A reaches the method site."
        ),
    },
    "ValueSetAnalysisTests.test_repeated_condition_uses_systematically_joined_state": {
        "classification": "precision policy",
        "verdict": "Sound conservative result",
        "assessment": (
            "Systematic joining intentionally forgets the A/B correlation. "
            "Both receiver rows remain for Laurel to prune."
        ),
    },
    "ValueSetAnalysisTests.test_correlated_binary_claim_uses_marginal_product_after_join": {
        "classification": "precision policy",
        "verdict": "Sound conservative result",
        "assessment": (
            "Pointwise union creates the full marginal Cartesian product, "
            "including two semantically unreachable TypeError candidates."
        ),
    },
    "ValueSetAnalysisTests.test_reassigned_guard_does_not_reuse_historical_predicate": {
        "classification": "semantic",
        "verdict": "Sound conservative result",
        "assessment": (
            "The new static definition of flag cannot reuse Truth(flag) from "
            "before the assignment; without a relational not-fact, both A and "
            "B remain possible on each new branch."
        ),
    },
    "ValueSetAnalysisTests.test_assignment_to_other_name_does_not_retain_join_partition": {
        "classification": "precision policy",
        "verdict": "Sound conservative result",
        "assessment": (
            "Even though flag is unchanged, the systematic join policy does "
            "not retain historical partitions across the earlier diamond."
        ),
    },
    "ValueSetAnalysisTests.test_dead_overwrite_coalesces_identical_partitions": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The common strong update kills the joined int/str difference "
            "before the later int addition."
        ),
    },
    "ValueSetAnalysisTests.test_loop_definition_versions_are_static_and_finite": {
        "classification": "semantic",
        "verdict": "Finite conservative result",
        "assessment": (
            "Loop iterations reuse one assignment-site definition ID; the "
            "header fixpoint contains a finite entry/site definition set."
        ),
    },
    "ValueSetAnalysisTests.test_prefix_result_tags_feed_the_next_attribute_site": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "Each normal prefix result becomes the next receiver tag in Python "
            "evaluation order."
        ),
    },
    "ValueSetAnalysisTests.test_caught_dispatch_error_does_not_escape_function": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The Missing row raises AttributeError, the Present row binds the "
            "method, and the matching handler removes the error from escapes."
        ),
    },
    "ValueSetAnalysisTests.test_possible_unbound_read_enters_escape_summary": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The function retains a normal int return and an independently "
            "feasible UnboundLocalError escape."
        ),
    },
    "ValueSetAnalysisTests.test_undeclared_attribute_write_fails_closed_when_live": {
        "classification": "policy",
        "verdict": "Intentional restriction",
        "assessment": (
            "Correctly rejects a live write that would create an undeclared "
            "instance field and invalidate the fixed shape."
        ),
    },
    "ValueSetAnalysisTests.test_builtin_protocol_claim_uses_the_argument_tags": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "len(values) dispatches on the argument's list tag, rather than on "
            "the builtin function object."
        ),
    },
    "ValueSetAnalysisTests.test_exact_builtin_truth_has_no_spurious_escape": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "bool truth conversion is total and contributes no exception arm."
        ),
    },
    "ValueSetAnalysisTests.test_generic_subscripts_refine_residual_results_and_errors": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "Recursive contracts produce the right element tags; literal tuple "
            "indexing is total, while list and dict retain feasible bounds/key errors."
        ),
    },
    "ValueSetAnalysisTests.test_impossible_narrowed_branch_is_bottom": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "After the checked int boundary contract, value is None has no "
            "reachable true state and the body is absent from flow locations."
        ),
    },
    "ValueSetAnalysisTests.test_comprehension_target_does_not_overwrite_outer_binding": {
        "classification": "semantic",
        "verdict": "Exact but narrow",
        "assessment": (
            "Correctly preserves an existing outer str binding across the "
            "comprehension scope. It does not test the initially-unbound spelling."
        ),
    },
    "ValueSetAnalysisTests.test_loop_fixpoint_tracks_maybe_bound_and_escaping_error": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The zero-iteration path leaves value unbound and the one-iteration "
            "path returns int; the finite loop fixpoint retains both."
        ),
    },
    "TypeExpressionTests.test_recursive_container_types_are_preserved_but_erased_for_dispatch": {
        "classification": "partial",
        "verdict": "Obligation only",
        "assessment": (
            "Correctly preserves recursive syntax and outer-tag erasure, but "
            "the static result does not decide list[int|str] versus list[int]. "
            "The generated runtime contract now checks elements."
        ),
    },
    "TypeExpressionTests.test_open_or_unknown_recursive_contracts_fail_closed": {
        "classification": "policy",
        "verdict": "Intentional restriction",
        "assessment": (
            "Correctly rejects Any and unknown tags so the runtime tag universe "
            "remains closed."
        ),
    },
    "ExceptionHierarchyTests.test_builtin_and_user_exception_mros_drive_handler_selection": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The generated LocalFileError MRO matches CPython and OSError "
            "consumes the raised subclass."
        ),
    },
    "ExceptionHierarchyTests.test_exception_raised_by_handler_leaks": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "KeyError is consumed by LookupError; the handler's ValueError is a "
            "new escaping completion and no normal return remains."
        ),
    },
    "ExceptionHierarchyTests.test_finally_transforms_all_pending_completions_exactly": {
        "classification": "semantic",
        "verdict": "Exact completion transformer",
        "assessment": (
            "Covers normal resumption and abrupt override for pending return, "
            "raise, and break routes. It also checks that handler cleanup "
            "removes the caught exception before a bare raise in finally, "
            "which therefore escapes as RuntimeError."
        ),
    },
    "ExceptionHierarchyTests.test_non_exception_handler_is_rejected": {
        "classification": "policy",
        "verdict": "Conservative admission",
        "assessment": (
            "Python parses except int and raises TypeError only during matching. "
            "PyHard intentionally rejects it earlier."
        ),
    },
    "TypedDictTests.test_shape_tag_uses_dict_dispatch_with_field_precision": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "The static Movie tag retains dict behavior, requiredness, literal "
            "field precision, and checked shape-preserving mutations."
        ),
    },
    "TypedDictTests.test_optional_get_result_and_required_get_result": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "Required title excludes the default; optional rating includes "
            "None until presence is established."
        ),
    },
    "TypedDictTests.test_checked_write_makes_optional_key_definitely_present": {
        "classification": "semantic",
        "verdict": "Exact on this case",
        "assessment": (
            "A checked direct update establishes rating presence, removing both "
            "the get default and the subscript KeyError."
        ),
    },
    "TypedDictTests.test_shape_destroying_mutations_become_checked_obligations": {
        "classification": "policy",
        "verdict": "Checked invariant",
        "assessment": (
            "Unknown/dynamic writes and clear remain dict operations but emit "
            "shape-preservation obligations. Subscript deletion is still deferred."
        ),
    },
    "TypedDictTests.test_typeddict_runtime_instance_check_is_rejected": {
        "classification": "policy",
        "verdict": "Intentional restriction",
        "assessment": (
            "Correctly rejects a runtime TypedDict isinstance test, which Python "
            "itself does not support as a shape test."
        ),
    },
    "TypedDictTests.test_typeddict_exposes_dict_interface_with_shape_effects": {
        "classification": "representation",
        "verdict": "Interface catalogued",
        "assessment": (
            "TypedDict resolves ordinary dict selectors while retaining its "
            "ghost shape tag; mutators carry explicit checked shape effects."
        ),
    },
    "AnalysisLogTests.test_serialized_log_is_the_input_to_both_renderers": {
        "classification": "plumbing",
        "verdict": "End-to-end checked",
        "assessment": (
            "Verifies JSON round-trip, both presentation views, embedded log "
            "identity, executable assert/assume instrumentation, and exit-0 assume."
        ),
    },
    "AnalysisLogTests.test_property_setter_is_preserved_in_serialized_residual_row": {
        "classification": "plumbing",
        "verdict": "Exact serialization",
        "assessment": (
            "Confirms the selected property-setter label survives into the "
            "canonical residual-row event."
        ),
    },
    "AnalysisLogTests.test_global_residual_and_out_states_are_structured_tables": {
        "classification": "presentation",
        "verdict": "Structurally checked",
        "assessment": (
            "The log contains global dispatch and normal/return OUT phases; "
            "HTML renders global, residual, and OUT tables."
        ),
    },
    "AdmissionTests.test_exception_target_must_be_fresh_in_its_scope": {
        "classification": "policy",
        "verdict": "Intentional restriction",
        "assessment": (
            "Implements the chosen simplification that avoids Python's automatic "
            "handler-target deletion of a pre-existing local."
        ),
    },
    "AdmissionTests.test_fresh_exception_target_is_admitted": {
        "classification": "policy",
        "verdict": "Positive policy boundary",
        "assessment": (
            "Correctly admits a fresh target. Detailed cleanup and hierarchy "
            "behavior are exercised by separate semantic tests."
        ),
    },
    "AdmissionTests.test_same_handler_spelling_in_unrelated_scopes_is_safe": {
        "classification": "policy",
        "verdict": "Exact policy scope",
        "assessment": (
            "Freshness is lexical, so identical spellings in independent "
            "functions are correctly admitted."
        ),
    },
    "AdmissionTests.test_constructor_fields_must_be_initialized_on_every_normal_path": {
        "classification": "policy",
        "verdict": "Required soundness gate",
        "assessment": (
            "Correctly rejects a normal constructor exit missing value, which "
            "would invalidate total declared-field lookup."
        ),
    },
    "AdmissionTests.test_annotation_without_constructor_does_not_initialize_field": {
        "classification": "policy",
        "verdict": "Required soundness gate",
        "assessment": (
            "A class annotation creates no instance attribute at runtime, so it "
            "cannot establish the fixed field shape by itself."
        ),
    },
    "AdmissionTests.test_dispatch_altering_constructs_are_rejected": {
        "classification": "policy",
        "verdict": "Required soundness gates",
        "assessment": (
            "Each sampled hook, class mutation, dynamic helper, deletion, class "
            "factory, and multiple-inheritance case gets its intended rejection."
        ),
    },
    "AdmissionTests.test_effectful_comprehension_body_is_rejected": {
        "classification": "policy",
        "verdict": "Conservative purity gate",
        "assessment": (
            "Correctly rejects a callee mutating its argument. The implemented "
            "effect analysis is intentionally more conservative than the full design."
        ),
    },
    "AdmissionTests.test_first_class_method_extraction_is_rejected": {
        "classification": "policy",
        "verdict": "Intentional restriction",
        "assessment": (
            "This rejection is the condition that permits direct "
            "lookup-and-invoke lowering without bound-method values."
        ),
    },
    "AdmissionTests.test_pure_comprehension_callee_is_admitted": {
        "classification": "partial",
        "verdict": "Representative tier only",
        "assessment": (
            "Now checks iteration, call argument, return/escape summaries, and "
            "the pure body. Provenance, order, and multiplicity obligations are "
            "still not generated."
        ),
    },
    "AdmissionTests.test_only_frozen_simple_dataclass_is_admitted": {
        "classification": "partial",
        "verdict": "Admission and manifest only",
        "assessment": (
            "Checks frozen fields and generated member declarations and rejects "
            "mutable dataclasses. Generated eq/hash operational contracts and "
            "hashable-field validation are not implemented."
        ),
    },
}
