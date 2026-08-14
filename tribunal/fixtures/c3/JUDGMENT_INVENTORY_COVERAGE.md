# G0-2 judgment-inventory coverage — row per Appendix-A rule (bead franken_lean-z6c, review amendment)

The review amendment: publish a row-per-Appendix-A judgment inventory
distinguishing real-module coverage, C0 positive/negative fixtures,
bounded-model coverage, and explicit unexercised blockers.
Unsupported/unobserved rows remain visible and bound the claim.

**Coverage columns.** P = Init.Prelude replay (2198/2198 accepted, 6 typed
artifact-incomplete, 0 rejected — `scripts/e2e/kernel_replay.sh`, census
receipted). S = the Std leg of the chosen set (Std.Data.HashMap.Basic: 92/92 accepted
over a 165-module closure, `chosen_set_replays_and_witnesses`, receipt
`crates/fln-conformance/evidence/g02_kernel_verdict/chosen_set_v4.32.0.jsonl`).
M = the mathlib leg (Mathlib.Order.Basic: 427/427 active module-data
declarations accepted over a 1286-module closure; the G0-1 fixture's 376 count
is its exported public-region census). C3 =
the C3 fixture pair plus the pinned-leanchecker Reference-kernel re-execution
(`scripts/tribunal/leanchecker_witness.sh`, ReferenceKernelOracle, not an
independent implementation). C0 = the
named k1_judgments/consensus fixture anchoring the rule. Model = bounded-model
suites (budget_parity, depth_stack_calibration, thread_matrix_determinism).
**not-yet-implemented** = an explicit row with a production owner and policy; it
stays visible and bounds the claim rather than being silently absent.

The status vocabulary is deliberately narrower than the evidence columns:
`implemented-and-covered` requires a named public-authority C0 or model fixture;
`structurally-enforced` requires a named compile-time or authority fixture;
`implemented-but-uncovered owner=<bead> — <policy>` records an implemented
branch whose real-module replay is not discriminating coverage; and
`not-yet-implemented owner=<bead> — <policy>` records absent production
semantics. The real-module column is the separate `externally-replayed` evidence
class. It can strengthen a covered row, but it cannot turn an uncovered row
green.

Every "accepted" below is a verdict of the one authority (`fln_kernel::check`)
over real Reference declarations. A real-module marker is a bounded end-to-end
compatibility observation with the complete K1 ruleset installed, not by itself
proof that one branch fired; named C0/model cells and construction arguments
provide rule-specific evidence. The frontier/inductive rows are admitted under
the FULL ruleset since franken_lean-8ce, and 6 typed artifact-incomplete
declarations are counted separately per FL-INV-07.

| rule | title | real-module | C0 fixture | model | status |
|---|---|---|---|---|---|
| KR-100 | Preconditions — closed terms, resource hook | P S M C3 | k1_judgments::kr100_loose_bvars_are_a_typed_rejection; k1_judgments::fl_inv_07_exhaustion_is_inconclusive_never_rejected | budget_parity::the_calibrated_budgets_callers_actually_use_are_accepted | implemented-and-covered |
| KR-101 | Bound variables are unreachable | P S M C3 (negative: every checked term is closed) | k1_judgments::kr100_loose_bvars_are_a_typed_rejection | — | structurally-enforced |
| KR-102 | Free variables | P S M C3 | k1_judgments::kr102_free_variables_are_telescope_bound_or_rejected | — | implemented-and-covered |
| KR-103 | Metavariables are rejected | P S M (negative: olean declarations carry no metas; admission refuses them) | k1_judgments::kr103_metavariables_are_a_typed_rejection | — | implemented-and-covered |
| KR-104 | Sort | P S M C3 | k1_judgments::kr104_kr972_a_sort_typed_axiom_is_admitted; k1_judgments::kr140_undefined_level_params_are_rejected | — | implemented-and-covered |
| KR-105 | Constants | P S M C3 | k1_judgments::kr105_universe_arity_is_checked; k1_judgments::kr105_unknown_constants_are_rejected; k1_judgments::kr140_undefined_level_params_are_rejected; k1_judgments::kr973_kr975_kr976_nonsafe_definitions_check_and_safe_references_are_gated | — | implemented-and-covered |
| KR-106 | Application | P S M C3 | k1_judgments::kr106_application_type_mismatch; k1_judgments::kr107_kr108_the_polymorphic_identity_function_checks | — | implemented-and-covered |
| KR-107 | Lambda | P S M C3 | k1_judgments::kr107_kr108_the_polymorphic_identity_function_checks; k1_judgments::kr107_binder_domain_that_is_not_a_type_is_rejected | — | implemented-and-covered |
| KR-108 | Dependent function types — the imax rule | P S M C3 | k1_judgments::kr107_kr108_the_polymorphic_identity_function_checks; k1_judgments::kr108_kr500_prop_impredicativity_via_imax | — | implemented-and-covered |
| KR-109 | Let | P S M C3 | k1_judgments::kr109_let_inference_zeta_substitutes_the_value_into_the_body_type | — | implemented-and-covered |
| KR-110 | Literals | P S M C3 | k1_judgments::kr110_literal_inference_maps_nat_and_string | — | implemented-and-covered |
| KR-111 | Metadata is transparent | P S M C3 | k1_judgments::kr111_kr201_mdata_is_transparent_to_typing_and_reduction | — | implemented-and-covered |
| KR-112 | Projections | P S M C3 | k1_judgments::kr112_projection_infers_the_field_type; k1_judgments::kr112_kr204_parameterized_structure_projection; k1_judgments::kr901_projection_cannot_leak_data_out_of_prop | — | implemented-and-covered |
| KR-200 | The whnf strategy | P S M C3 | k1_judgments::kr200_kr309_delta_unfolds_definitions; k1_judgments::kr200_unsafe_definitions_are_not_delta_unfolded | depth_stack_calibration::the_stack_derivation_is_sound_at_and_around_the_shipped_point | implemented-and-covered |
| KR-201 | whnf-core performs no delta | P S M C3 | k1_judgments::kr111_kr201_mdata_is_transparent_to_typing_and_reduction; k1_judgments::kr200_unsafe_definitions_are_not_delta_unfolded | — | implemented-and-covered |
| KR-202 | Beta | P S M C3 | k1_judgments::kr202_beta_and_kr203_zeta_in_defeq; k1_judgments::kr202_over_applied_lambda_beta_reduces_and_reapplies | — | implemented-and-covered |
| KR-203 | Zeta — let and let-bound fvars | P S M C3 | k1_judgments::kr202_beta_and_kr203_zeta_in_defeq; k1_judgments::kr109_let_inference_zeta_substitutes_the_value_into_the_body_type | — | implemented-and-covered |
| KR-204 | Projection reduction | P S M C3 | k1_judgments::kr204_projection_of_a_constructor_reduces_to_the_field; k1_judgments::kr112_kr204_parameterized_structure_projection; k1_judgments::kr314_projection_expands_string_literal_scrutinees | — | implemented-and-covered |
| KR-205 | Recursor dispatch | P S M C3 | k1_judgments::kr316_iota_selects_the_matching_rule_per_constructor; k1_judgments::kr317_k_conversion_refuses_a_major_whose_index_does_not_match_the_constructor; k1_judgments::kr955_quot_lift_and_ind_compute | — | implemented-and-covered |
| KR-300 | Resource hook and quick equality | P S M C3 | k1_judgments::fl_inv_07_exhaustion_is_inconclusive_never_rejected; k1_judgments::fl_inv_01_kernel_verdicts_are_deterministic | budget_parity::the_calibrated_budgets_callers_actually_use_are_accepted | implemented-and-covered |
| KR-301 | Quick structural/hash equality | P S M C3 | k1_judgments::kr301_structural_equality_closes_at_the_one_step_boundary; k1_judgments::kr301_distinct_literals_are_decisively_not_defeq | — | implemented-and-covered |
| KR-302 | Binder congruence | P S M C3 | k1_judgments::kr302_binder_congruence_compares_the_domain_not_only_the_body; k1_judgments::kr302_binder_congruence_discovered_by_delta | — | implemented-and-covered |
| KR-303 | Level equality | P S M C3 | k1_judgments::kr303_sorts_are_defeq_iff_their_levels_are_equivalent; k1_judgments::kr303_sort_equivalence_discovered_by_delta; k1_judgments::kr303_sort_equivalence_discovered_by_beta | — | implemented-and-covered |
| KR-304 | The decide shortcut | P S M C3 | k1_judgments::kr301_distinct_literals_are_decisively_not_defeq; k1_judgments::kr313_comparisons_produce_bool_constants | — | implemented-and-covered |
| KR-305 | Cheap normalization, projections deferred | P S M C3 | k1_judgments::kr303_sort_equivalence_discovered_by_beta; k1_judgments::kr310_projection_congruence_on_stuck_scrutinees | — | implemented-and-covered |
| KR-306 | Definitional proof irrelevance in Prop | P S M C3 | k1_judgments::kr306_proof_irrelevance_in_prop; k1_judgments::kr306_proof_irrelevance_does_not_leak_to_type; k1_judgments::kr306_proof_irrelevance_requires_defeq_propositions | — | implemented-and-covered |
| KR-307 | The lazy-delta ladder | P S M C3 | k1_judgments::kr303_sort_equivalence_discovered_by_delta; k1_judgments::kr313_delta_exposed_literals_decide_in_lazy_delta | — | implemented-and-covered |
| KR-308 | Nat successor offsets | P S M C3 | k1_judgments::kr313_offset_closes_literal_vs_constructor_forms | — | implemented-and-covered |
| KR-309 | Delta ordering by definitional height | P S M C3 | k1_judgments::kr200_kr309_delta_unfolds_definitions; k1_judgments::kr303_sort_equivalence_discovered_by_delta | — | implemented-and-covered |
| KR-310 | Post-delta syntactic closure | P S M C3 | k1_judgments::kr310_same_constant_defeq_iff_levels_are_equivalent; k1_judgments::kr310_projection_congruence_on_stuck_scrutinees; k1_judgments::kr313_offset_closes_literal_vs_constructor_forms | — | implemented-and-covered |
| KR-311 | Application congruence | P S M C3 | k1_judgments::kr311_application_congruence_checks_heads_and_arguments; k1_judgments::kr202_over_applied_lambda_beta_reduces_and_reapplies | — | implemented-and-covered |
| KR-312 | Eta — functions and structures | P S M C3 | k1_judgments::kr312_function_eta; k1_judgments::kr903_structure_eta_in_defeq_both_directions | — | implemented-and-covered |
| KR-313 | Nat literal acceleration — the exact operation set | P S M C3 (7 literal-family rejects triaged here 07-23, all converted by the KR-313/314 work) | k1_judgments::kr313_the_pin_operation_table_computes_literal_results; k1_judgments::kr313_comparisons_produce_bool_constants; k1_judgments::kr313_nat_zero_and_reduced_arguments_are_literal_operands; k1_judgments::kr313_pow_honors_the_reduce_pow_max_exp_cap; k1_judgments::kr313_no_nat_blt_at_this_pin; k1_judgments::kr313_dispatch_requires_bare_heads_and_exact_arity; k1_judgments::kr313_offset_closes_literal_vs_constructor_forms; k1_judgments::kr313_delta_exposed_literals_decide_in_lazy_delta | — | implemented-and-covered |
| KR-314 | String literal rules | P S M C3 | k1_judgments::kr314_string_literal_defeq_its_oflist_spine; k1_judgments::kr314_projection_expands_string_literal_scrutinees; k1_judgments::kr314_string_recursor_fires_on_a_literal_major | — | implemented-and-covered |
| KR-315 | Unit-like eta | P S M C3 | k1_judgments::kr315_unit_like_values_are_defeq_when_their_types_are | — | implemented-and-covered |
| KR-316 | Iota — recursor computation | P S M C3 (the largest triaged gap family, converted by the recursor slice fln-5p2) | k1_judgments::kr316_iota_selects_the_matching_rule_per_constructor; k1_judgments::kr316_iota_is_stuck_without_a_constructor_major_or_full_arity; k1_judgments::kr316_iota_preserves_trailing_arguments; k1_judgments::kr316_iota_applies_constructor_fields_and_the_inductive_hypothesis; k1_judgments::kr316_nat_literal_majors_convert_to_constructor_form; k1_judgments::kr316_structure_eta_coercion_fires_the_recursor_on_an_opaque_major; k1_judgments::kr316_parameterized_iota_takes_the_last_nfields_arguments | — | implemented-and-covered |
| KR-317 | K-like reduction | P S M C3 (converted by fln-5p2's KR-317 K-conversion) | k1_judgments::kr317_k_like_recursor_reduces_an_opaque_proof; k1_judgments::kr317_k_conversion_refuses_a_major_whose_index_does_not_match_the_constructor; k1_judgments::kr317_a_k_target_block_admits_with_k_true | — | implemented-and-covered |
| KR-318 | Native reduction hooks | — | — | — | not-yet-implemented owner=franken_lean-zht — `reduce_native` follow-up; omission can only under-accept, and no native-accelerated result is claimed |
| KR-400 | Inference hook | P S M C3 | k1_judgments::fl_inv_07_exhaustion_is_inconclusive_never_rejected | budget_parity::the_calibrated_budgets_callers_actually_use_are_accepted | implemented-and-covered |
| KR-401 | Normalization hook | P S M C3 | k1_judgments::fl_inv_07_iota_chain_exhaustion_is_inconclusive_never_rejected | budget_parity::the_calibrated_budgets_callers_actually_use_are_accepted | implemented-and-covered |
| KR-402 | Defeq hook | P S M C3 | k1_judgments::fl_inv_07_iota_chain_exhaustion_is_inconclusive_never_rejected | budget_parity::the_calibrated_budgets_callers_actually_use_are_accepted | implemented-and-covered |
| KR-403 | The counter mechanism | P S M C3 | k1_judgments::fl_inv_07_exhaustion_is_inconclusive_never_rejected; k1_judgments::fl_inv_07_iota_chain_exhaustion_is_inconclusive_never_rejected | budget_parity::every_budget_carries_the_measurement_it_came_from | implemented-and-covered |
| KR-404 | Diagnostics are never limits | P S M C3 (typed Inconclusive outcomes observed in the census) | k1_judgments::fl_inv_07_exhaustion_is_inconclusive_never_rejected; k1_judgments::fl_inv_07_iota_chain_exhaustion_is_inconclusive_never_rejected; k1_judgments::fl_inv_07_oversized_shift_results_are_typed_exhaustion | — | implemented-and-covered |
| KR-500 | Level normalization, including imax collapse | P S M C3 | k1_judgments::kr108_kr500_prop_impredicativity_via_imax; k1_judgments::kr303_sorts_are_defeq_iff_their_levels_are_equivalent | — | implemented-and-covered |
| KR-501 | Level equivalence | P S M C3 | k1_judgments::kr303_sorts_are_defeq_iff_their_levels_are_equivalent; k1_judgments::kr310_same_constant_defeq_iff_levels_are_equivalent | — | implemented-and-covered |
| KR-600 | Block preliminaries | P S M C3 (mutual blocks across all three legs) | k1_judgments::kr600_block_preconditions_reject_empty_and_colliding_names; k1_judgments::kr6xx_a_recursive_block_admits_with_byte_exact_recursor_regeneration | — | implemented-and-covered |
| KR-601 | Shared parameters across a mutual block | P S M C3 | k1_judgments::kr601_mutual_block_parameters_must_match | — | implemented-and-covered |
| KR-602 | One universe per mutual block | P S M C3 | k1_judgments::kr602_mutual_results_share_one_universe_and_end_in_sorts | — | implemented-and-covered |
| KR-603 | Constructor validity | P S M C3 | k1_judgments::kr603_constructor_metadata_and_return_type_are_cross_checked; k1_judgments::kr6xx_a_recursive_block_admits_with_byte_exact_recursor_regeneration | — | implemented-and-covered |
| KR-604 | Field universes — the Prop exception | P S M C3 | k1_judgments::kr604_oversized_constructor_fields_are_rejected; k1_judgments::kr6xx_a_recursive_block_admits_with_byte_exact_recursor_regeneration | — | implemented-and-covered |
| KR-605 | Valid recursive occurrence shape | P S M C3 | k1_judgments::kr605_indices_may_not_mention_the_block; k1_judgments::kr6xx_a_recursive_block_admits_with_byte_exact_recursor_regeneration | — | implemented-and-covered |
| KR-606 | Strict positivity | P S M C3 (positive: every replayed inductive validates; the mandated-mutant lane plants its skip) | k1_judgments::kr606_negative_occurrences_are_rejected; k1_judgments::kr608_positivity_is_enforced_through_the_translation | — | implemented-and-covered |
| KR-607 | Recursivity and reflexivity flags | P S M C3 | k1_judgments::kr607_decoded_flags_are_cross_checked; k1_judgments::kr700_restricted_elimination_and_kr317_k_flags_are_regenerated | — | implemented-and-covered |
| KR-608 | Nested inductives compile to mutual blocks | P S M C3 (nested blocks admitted under the FULL ruleset — franken_lean-8ce) | k1_judgments::kr608_nested_block_admits_with_byte_exact_translated_regeneration; k1_judgments::kr608_decoded_nested_recursors_are_never_trusted; k1_judgments::kr608_random_nested_shapes_agree_with_the_independent_model | — | implemented-and-covered |
| KR-700 | When elimination is restricted to Prop | P S M C3 | k1_judgments::kr700_restricted_elimination_and_kr317_k_flags_are_regenerated; k1_judgments::kr700_a_restricted_block_admits_with_prop_elimination | — | implemented-and-covered |
| KR-701 | The subsingleton criterion | P S M C3 | k1_judgments::kr701_a_single_constructor_prop_carrying_data_is_elimination_restricted; k1_judgments::kr700_a_restricted_block_admits_with_prop_elimination | — | implemented-and-covered |
| KR-702 | The elimination level | P S M C3 | k1_judgments::kr700_a_restricted_block_admits_with_prop_elimination; k1_judgments::kr317_a_k_target_block_admits_with_k_true | — | implemented-and-covered |
| KR-800 | Motives and major premise | P S M C3 | k1_judgments::kr802_decoded_recursor_arity_observables_are_cross_checked; k1_judgments::kr6xx_a_recursive_block_admits_with_byte_exact_recursor_regeneration | — | implemented-and-covered |
| KR-801 | Minor premises with induction hypotheses | P S M C3 | k1_judgments::kr316_iota_applies_constructor_fields_and_the_inductive_hypothesis | — | implemented-and-covered |
| KR-802 | The recursor type | P S M C3 | k1_judgments::kr802_decoded_recursor_arity_observables_are_cross_checked; k1_judgments::kr6xx_a_recursive_block_admits_with_byte_exact_recursor_regeneration | — | implemented-and-covered |
| KR-803 | Iota right-hand sides | P S M C3 | k1_judgments::kr316_iota_applies_constructor_fields_and_the_inductive_hypothesis; k1_judgments::kr316_iota_selects_the_matching_rule_per_constructor | — | implemented-and-covered |
| KR-900 | Projection typing | P S M C3 | k1_judgments::kr112_projection_infers_the_field_type; k1_judgments::kr112_kr204_parameterized_structure_projection | — | implemented-and-covered |
| KR-901 | No data escapes Prop through projections | P S M C3 | k1_judgments::kr901_projection_cannot_leak_data_out_of_prop; k1_judgments::kr112_projection_infers_the_field_type | — | implemented-and-covered |
| KR-902 | Projection computation | P S M C3 | k1_judgments::kr204_projection_of_a_constructor_reduces_to_the_field; k1_judgments::kr112_kr204_parameterized_structure_projection; k1_judgments::kr314_projection_expands_string_literal_scrutinees | — | implemented-and-covered |
| KR-903 | Structure eta coherence | P S M C3 (the typeclass-structure casesOn/recOn/noConfusionType family triaged to fln-d4x's KR-903 hypothesis, converted) | k1_judgments::kr903_structure_eta_in_defeq_both_directions; k1_judgments::kr316_structure_eta_coercion_fires_the_recursor_on_an_opaque_major | — | implemented-and-covered |
| KR-950 | Initialization requires Eq | P S M C3 | k1_judgments::kr95x_quotient_initialization_requires_the_exact_eq_shape; k1_judgments::kr950_quotient_init_checks_the_eq_constructor_not_only_the_eq_type | — | implemented-and-covered |
| KR-951 | Quot | P S M C3 | k1_judgments::kr951_kr952_kr953_kr954_quotient_rows_are_checked_individually | — | implemented-and-covered |
| KR-952 | Quot.mk | P S M C3 | k1_judgments::kr951_kr952_kr953_kr954_quotient_rows_are_checked_individually | — | implemented-and-covered |
| KR-953 | Quot.lift | P S M C3 | k1_judgments::kr951_kr952_kr953_kr954_quotient_rows_are_checked_individually | — | implemented-and-covered |
| KR-954 | Quot.ind | P S M C3 | k1_judgments::kr951_kr952_kr953_kr954_quotient_rows_are_checked_individually | — | implemented-and-covered |
| KR-955 | Quot computation | P S M C3 (converted by fln-5p2's KR-955) | k1_judgments::kr955_quot_lift_and_ind_compute; k1_judgments::kr955_quot_computation_preserves_trailing_args_and_requires_a_saturated_mk | — | implemented-and-covered |
| KR-970 | One name, one constant | P S M C3 (the one-name law asserted on every admission) | k1_judgments::kr970_the_one_name_one_constant_law | — | implemented-and-covered |
| KR-971 | Distinct level parameters | P S M C3 | k1_judgments::kr971_duplicate_level_params_are_rejected | — | implemented-and-covered |
| KR-972 | Well-formed constant preamble | P S M C3 | k1_judgments::kr104_kr972_a_sort_typed_axiom_is_admitted; k1_judgments::kr972_a_declaration_type_that_is_not_a_sort_is_rejected; reference_differential::kernel_verdicts_agree_with_the_pinned_reference | — | implemented-and-covered |
| KR-973 | Axioms | P S M C3 (axioms admitted by rule) | k1_judgments::kr104_kr972_a_sort_typed_axiom_is_admitted; checked_declaration_capability::an_accepted_declaration_publishes_through_its_capability | — | implemented-and-covered |
| KR-974 | Definitions, theorems, opaques | P S M C3 | k1_judgments::kr974_theorems_must_be_propositions; k1_judgments::kr974_body_type_mismatch_is_rejected; k1_judgments::kr974_opaque_declarations_check_the_body_and_stay_opaque_to_defeq | — | implemented-and-covered |
| KR-975 | The unsafe quarantine | P S M C3 (unsafe rows are oracle-unscorable skips by design) | k1_judgments::kr973_kr975_kr976_nonsafe_definitions_check_and_safe_references_are_gated | — | implemented-and-covered |
| KR-976 | The partial quarantine | — | k1_judgments::kr973_kr975_kr976_nonsafe_definitions_check_and_safe_references_are_gated | — | implemented-and-covered |
| KR-977 | Mutual definitions are unsafe-only | — | k1_judgments::kr977_mutual_definition_shape_is_nonempty_uniform_and_nonsafe; k1_judgments::kr977_mutual_definitions_predeclare_the_whole_block_and_fail_atomically | — | implemented-and-covered |
| KR-978 | The unchecked door is not a rule | P S M C3 (negative: every admitted declaration passed the one authority; nothing entered unchecked) | checked_declaration_capability::a_rejected_declaration_yields_no_capability; admission_laundering::a_forged_verdict_carries_no_authority | — | structurally-enforced |
| KR-980 | The state machine | — | checked_declaration_capability::an_accepted_declaration_publishes_through_its_capability; consensus_seat::a_unanimous_council_publishes | — | implemented-and-covered |
| KR-981 | Untrusted at the boundary | — | checked_declaration_capability::the_capability_carries_the_declaration_that_was_checked | — | implemented-and-covered |
| KR-982 | One check transition | — | checked_declaration_capability::a_rejected_declaration_yields_no_capability; checked_declaration_capability::an_accepted_declaration_publishes_through_its_capability | — | implemented-and-covered |
| KR-983 | The opaque capability | — | admission_laundering::an_external_clone_of_the_capability_does_not_compile; admission_laundering::an_external_forge_of_the_capability_does_not_compile; admission_laundering::no_serialization_path_exists_for_the_capability | — | implemented-and-covered |
| KR-984 | Publication is a council transition | — | checked_declaration_capability::publication_consumes_the_capability_exactly_once; consensus_seat::a_unanimous_council_publishes; consensus_seat::one_dissenting_seat_halts_publication_and_is_never_outvoted | — | implemented-and-covered |
| KR-985 | The consumer inventory | — | admission_laundering::a_forged_verdict_carries_no_authority; admission_laundering::no_serialization_path_exists_for_the_capability; consensus_seat::seats_cannot_overturn_a_kernel_rejection | — | implemented-and-covered |
| KR-986 | The launder-refusal fixtures | — | admission_laundering::an_external_clone_of_the_capability_does_not_compile; admission_laundering::an_external_forge_of_the_capability_does_not_compile; admission_laundering::no_serialization_path_exists_for_the_capability | — | implemented-and-covered |
| KR-987 | Non-promotion (FL-INV-07) | — | admission_laundering::starvation_mints_no_capability; checked_declaration_capability::an_exhausted_budget_yields_no_capability; checked_declaration_capability::cancellation_after_one_staged_member_exposes_no_prefix | budget_parity::a_budget_calibrated_for_another_engine_mints_no_capability | implemented-and-covered |

## What this table binds

1. **2,717 accepted declarations across three real modules** (2198 Init.Prelude
   + 92 Std + 427 mathlib, each with ReferenceKernelOracle agreement), with
   every rejection either converted by named follow-ups or triaged to a
   pre-classified family. No verdict here is implicit: each is
   `fln_kernel::check` over real Reference declarations. Leanchecker re-runs the
   same Reference implementation and is not an independent witness.
2. **Zero implemented-but-uncovered rows** remain. Eighty-five implemented rows
   name exact test functions; no prose label such as "test anchors" counts as a
   fixture. **One not-yet-implemented row** (KR-318) remains visible as a named
   production follow-up and is not reported as passing.
3. The C0 column cites the fixture files; the per-test anchors are greppable
   (`grep -n "KR-313" crates/fln-kernel/tests/k1_judgments.rs`).
