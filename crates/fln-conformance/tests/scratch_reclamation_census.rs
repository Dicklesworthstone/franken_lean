//! `scratch_reclamation_census` — the workspace-wide half of the scratch fence's
//! binding (bead `franken_lean-eir2`).
//!
//! `fln_core::scratch` is the fence: one `ScratchRoot` guard, one `is_reclaimable`
//! predicate, one `SCRATCH_FAMILIES` table. `fln-core`'s own gate proves the machinery
//! and the table's internal consistency. What it cannot prove from rank 0 is the join
//! to the rest of the workspace, which is the half that rots:
//!
//! * a producer that stops naming its constant, or invents a prefix outside the table
//!   (its roots silently stop being reclaimed — the under-report direction);
//! * a remainder row whose producer was routed or deleted (a stale row keeping a slot
//!   warm — `fln-8zsq`'s disclosure-drift shape);
//! * a NEW `std::env::temp_dir()` call site appearing anywhere in the tree, which is
//!   how every one of the seven censused leaks started.
//!
//! So this file binds every family row to its declared source in both directions, and
//! classifies every `temp_dir` call site in the workspace — routed machinery, declared
//! remainder, self-cleaning, or non-producer — with conservation and floors so neither
//! direction can drift quietly. It walks sources only.
//!
//! It also hosts the both-directions retention proofs for the two families whose
//! producer surfaces are pin-dependent (`golden_vellum.rs`, `reference_differential.rs`):
//! those surfaces ask the pinned Reference, CI installs none, and the CI-execution join
//! (fln-rgha) reads any `test:` citation into them as "evidence CI never executed" —
//! surface-granular, so a pin-independent function is invisible to it (f2t9). The proofs
//! live here, in a pin-free surface, exercising the same family constructors directly; the
//! guard-owned roots they create reclaim exactly like the producer's own fixtures.

#![forbid(unsafe_code)]

use fln_core::scratch::{REFDIFF_PREFIX, SCRATCH_FAMILIES, ScratchRoot, VDI4_PREFIX};
use std::path::{Path, PathBuf};

/// The call every scratch-root producer that bypasses the fence must make.
const NEEDLE: &str = "std::env::temp_dir()";

/// This file, excluded from its own walk: a scan whose search space contains its own
/// declaration passes by reading itself (`fln-8zsq`'s lesson), so the walk asserts the
/// exclusion matched exactly once — a renamed census file cannot silently vacate the
/// walk that is supposed to find it.
const SELF_PATH: &str = "crates/fln-conformance/tests/scratch_reclamation_census.rs";

/// The one file allowed to call the needle for root creation: the fence itself.
const MACHINERY: &[&str] = &["crates/fln-core/src/scratch.rs"];

/// Files that call the needle but remove what they made on the passing path by hand.
/// Each carries the cleanup needle the file must still contain, so a file whose
/// cleanup is deleted stops matching its class instead of staying classified.
const SELF_CLEANING: &[(&str, &str)] = &[
    ("crates/fln-conformance/src/pin.rs", "remove_dir_all"),
    // The upstream-suite scoreboard's per-run copies of the vendored suite, reclaimed by the
    // run that created them (bead fln-upstream-suite-scoreboard-n04o).
    (
        "crates/fln-cli/tests/upstream_suite_scoreboard.rs",
        "remove_dir_all",
    ),
    (
        "crates/fln-conformance/tests/agents_enforcement_census.rs",
        "remove_dir",
    ),
    ("crates/fln-rt/tests/region_engine.rs", "remove_dir_all"),
    // The G0-3 door test's per-pid plugin workdir, reclaimed on the passing path.
    ("crates/fln-unsafe-abi/src/tests.rs", "remove_dir_all"),
    // The attribute census cells' scratch vendor trees, reclaimed per cell.
    (
        "crates/fln-conformance/tests/attribute_state_census.rs",
        "remove_dir_all",
    ),
    (
        "crates/fln-olean/tests/chain_audit_cli.rs",
        "remove_dir_all",
    ),
    // The IR graph command tests' per-test directories, removed in `Drop` (bead
    // fln-ir-decoder-call-graph-sjzl; the activation of 4065cdae and e8459152).
    ("crates/fln-olean/tests/ir_archive_cli.rs", "remove_dir_all"),
    (
        "tools/structure-guard/tests/agent_anchor_cli.rs",
        "remove_dir_all",
    ),
    (
        "crates/fln-cli/tests/source_module_check.rs",
        "remove_dir_all",
    ),
    (
        "crates/fln-server/tests/lsp_client_lifecycle_params_cli.rs",
        "remove_file",
    ),
    (
        "crates/fln-server/tests/lsp_client_session_cli.rs",
        "remove_file",
    ),
    (
        "crates/fln-server/tests/lsp_correlate_cli.rs",
        "remove_file",
    ),
    ("crates/fln-server/tests/lsp_replay_cli.rs", "remove_file"),
    ("crates/fln-server/tests/lsp_timeline_cli.rs", "remove_file"),
    // The verbs/personalities tests: every root is a `TempDir` removed on drop.
    (
        "crates/fln-cli/tests/cli_personalities_and_verbs.rs",
        "remove_dir_all",
    ),
    // The lake integrity controls: every package root is a `Package` removed on drop.
    ("crates/fln-cli/tests/lake_integrity.rs", "remove_dir_all"),
    // The relation-tactic regressions: each input file is created with `create_new`
    // and removed when its `Input` guard drops.
    (
        "crates/fln-cli/tests/native_relation_tactics.rs",
        "remove_file",
    ),
    // The lake build and module-build packages: every package root is removed on drop.
    (
        "crates/fln-cli/tests/lake_build_session.rs",
        "remove_dir_all",
    ),
    (
        "crates/fln-cli/tests/lake_module_build.rs",
        "remove_dir_all",
    ),
    // The LSP completion and navigation fixtures: the one written file, then the
    // uniquely-created directory, are removed on drop.
    ("crates/fln-cli/tests/lsp_completion.rs", "remove_dir"),
    (
        "crates/fln-cli/tests/lsp_definition_navigation.rs",
        "remove_dir",
    ),
    // Classified 2026-10-05 after reading each file. The next five make one `temp_dir()`
    // call apiece, inside a guard constructor that makes a pid-and-counter-unique root;
    // every test's files, record store (`FLN_IMPORT_REUSE_DIR`) and outputs live under that
    // root, and the guard removes it on drop.
    // The build-explain packages (`0f2f535a`), removed on drop.
    ("crates/fln-cli/tests/build_explain.rs", "remove_dir_all"),
    // The lake source-module record packages (`61260daa`), removed on drop. The one
    // store outside the root, `relative/records`, is refused by the CLI as not absolute
    // and writes nothing.
    (
        "crates/fln-cli/tests/lake_module_records.rs",
        "remove_dir_all",
    ),
    // The LSP `.olean`-import projects (`d695491d`), removed on drop.
    (
        "crates/fln-cli/tests/lsp_olean_imports.rs",
        "remove_dir_all",
    ),
    // The header-pin forgery scratch (`26a58548`), removed on drop.
    ("crates/fln-cli/tests/olean_header_pin.rs", "remove_dir_all"),
    // The import-reuse scratch (`907bfdc0`), removed on drop on the passing path and kept
    // when the test panics, for diagnosis. The copied `fln-other` binary lives inside it.
    (
        "crates/fln-cli/tests/source_import_reuse.rs",
        "remove_dir_all",
    ),
    // The corrupted-closure search path (`d38870fc`): a pid-named copy of seven pinned
    // Init modules, removed by hand right after the two check-source runs and before the
    // assertions, so only a panic in the copy or the runs leaves it behind.
    (
        "crates/fln-cli/tests/source_olean_imports.rs",
        "remove_dir_all",
    ),
    // Classified 2026-11-13 after reading each file: RAII test fixture guards
    // (`Directory`, `Project`, `Scratch`, `Fixture`) remove their exclusively
    // created per-pid/counter roots in `Drop` via `remove_dir_all`.
    ("crates/fln-cli/src/lake_build.rs", "remove_dir_all"),
    (
        "crates/fln-cli/src/source_check/imports.rs",
        "remove_dir_all",
    ),
    (
        "crates/fln-cli/tests/source_module_grammar.rs",
        "remove_dir_all",
    ),
    (
        "crates/fln-cli/tests/source_module_visibility.rs",
        "remove_dir_all",
    ),
    (
        "crates/fln-cli/tests/source_public_instances.rs",
        "remove_dir_all",
    ),
    (
        "crates/fln-cli/tests/source_public_proof_instances.rs",
        "remove_dir_all",
    ),
    (
        "crates/fln-olean/src/ir_files/type_tests.rs",
        "remove_dir_all",
    ),
    ("crates/fln-olean/tests/ir_files.rs", "remove_dir_all"),
    ("crates/fln-olean/tests/ir_type_cli.rs", "remove_dir_all"),
    (
        "crates/fln/tests/source_io_presentation.rs",
        "remove_dir_all",
    ),
];

/// Unrouted CLI integration test producers (added in W5/W7/W12 batch test commits, and
/// the 2026-09 runtime, lake and LSP batches). These call `std::env::temp_dir()` directly
/// and do not yet route through `ScratchRoot` or self-clean: every run leaves its roots
/// behind. Declared here so the leak is visible, not repaired.
const UNROUTED_CLI_PRODUCERS: &[&str] = &[
    "crates/fln-cli/src/goal_traces.rs",
    "crates/fln-cli/src/imported_ir.rs",
    "crates/fln-cli/tests/check_module.rs",
    "crates/fln-cli/tests/class_def_reducibility.rs",
    "crates/fln-cli/tests/coerced_let_values.rs",
    "crates/fln-cli/tests/conv_mode.rs",
    "crates/fln-cli/tests/deprecated_constants.rs",
    "crates/fln-cli/tests/imported_ir.rs",
    "crates/fln-cli/tests/instance_dependent_outputs.rs",
    "crates/fln-cli/tests/instance_output_search.rs",
    "crates/fln-cli/tests/instance_tabling.rs",
    "crates/fln-cli/tests/instance_universe_outputs.rs",
    "crates/fln-cli/tests/instance_variants.rs",
    "crates/fln-cli/tests/lake_executable.rs",
    "crates/fln-cli/tests/lake_lean_config.rs",
    "crates/fln-cli/tests/lake_local_dependencies.rs",
    "crates/fln-cli/tests/lean_guard_msgs.rs",
    "crates/fln-cli/tests/lean_guard_spec_parity.rs",
    "crates/fln-cli/tests/lean_trace_state.rs",
    "crates/fln-cli/tests/list_append_instances.rs",
    "crates/fln-cli/tests/list_append_simp.rs",
    "crates/fln-cli/tests/lsp_project_roots.rs",
    "crates/fln-cli/tests/lsp_proof_modules.rs",
    "crates/fln-cli/tests/nested_inductives.rs",
    "crates/fln-cli/tests/outparam_results.rs",
    "crates/fln-cli/tests/runtime_conditionals.rs",
    "crates/fln-cli/tests/runtime_macro_inline.rs",
    "crates/fln-cli/tests/simp_hypothesis_placement.rs",
    "crates/fln-cli/tests/simp_suggestions.rs",
    "crates/fln-cli/tests/source_atomic_macro_rules.rs",
    "crates/fln-cli/tests/source_bool_conditions.rs",
    "crates/fln-cli/tests/source_branch_returns.rs",
    "crates/fln-cli/tests/source_calc_expected_endpoints.rs",
    "crates/fln-cli/tests/source_check.rs",
    "crates/fln-cli/tests/source_check_notations.rs",
    "crates/fln-cli/tests/source_check_optional_parameters.rs",
    "crates/fln-cli/tests/source_check_pp_options.rs",
    "crates/fln-cli/tests/source_check_section_variables.rs",
    "crates/fln-cli/tests/source_check_structure_instances.rs",
    "crates/fln-cli/tests/source_class_out_params.rs",
    "crates/fln-cli/tests/source_closure_data.rs",
    "crates/fln-cli/tests/source_collection_notation.rs",
    "crates/fln-cli/tests/source_collections.rs",
    "crates/fln-cli/tests/source_command_in.rs",
    "crates/fln-cli/tests/source_congruence.rs",
    "crates/fln-cli/tests/source_constrained_simplification.rs",
    "crates/fln-cli/tests/source_context_generalization.rs",
    "crates/fln-cli/tests/source_core_closing_tactics.rs",
    "crates/fln-cli/tests/source_default_instances.rs",
    "crates/fln-cli/tests/source_default_simp.rs",
    "crates/fln-cli/tests/source_delta_guard_expr.rs",
    "crates/fln-cli/tests/source_delta_inference.rs",
    "crates/fln-cli/tests/source_dependent_programs.rs",
    "crates/fln-cli/tests/source_deriving_repr.rs",
    "crates/fln-cli/tests/source_do_mutation.rs",
    "crates/fln-cli/tests/source_do_runtime.rs",
    "crates/fln-cli/tests/source_dsimp.rs",
    "crates/fln-cli/tests/source_ellipsis.rs",
    "crates/fln-cli/tests/source_empty_runtime.rs",
    "crates/fln-cli/tests/source_equality_decisions.rs",
    "crates/fln-cli/tests/source_equation_theorems.rs",
    "crates/fln-cli/tests/source_expression_elimination.rs",
    "crates/fln-cli/tests/source_false_or_by_contra.rs",
    "crates/fln-cli/tests/source_first_order_results.rs",
    "crates/fln-cli/tests/source_floats.rs",
    "crates/fln-cli/tests/source_fun_tuple_binders.rs",
    "crates/fln-cli/tests/source_funext.rs",
    "crates/fln-cli/tests/source_global_stages.rs",
    "crates/fln-cli/tests/source_goal_structuring_tactics.rs",
    "crates/fln-cli/tests/source_ground_projections.rs",
    "crates/fln-cli/tests/source_guard.rs",
    "crates/fln-cli/tests/source_hypothesis_rewriting.rs",
    "crates/fln-cli/tests/source_implicit_lambda.rs",
    "crates/fln-cli/tests/source_imported_execution.rs",
    "crates/fln-cli/tests/source_index_notation.rs",
    "crates/fln-cli/tests/source_indexed_function_children.rs",
    "crates/fln-cli/tests/source_indexed_runtime.rs",
    "crates/fln-cli/tests/source_indexed_smart_unfolding.rs",
    "crates/fln-cli/tests/source_instance_factories.rs",
    "crates/fln-cli/tests/source_instance_universe_holes.rs",
    "crates/fln-cli/tests/source_interleaved_runtime.rs",
    "crates/fln-cli/tests/source_layout_columns.rs",
    "crates/fln-cli/tests/source_let_equations.rs",
    "crates/fln-cli/tests/source_local_helpers.rs",
    "crates/fln-cli/tests/source_local_instance_attributes.rs",
    "crates/fln-cli/tests/source_local_lifting.rs",
    "crates/fln-cli/tests/source_local_simp_attributes.rs",
    "crates/fln-cli/tests/source_local_templates.rs",
    "crates/fln-cli/tests/source_logic.rs",
    "crates/fln-cli/tests/source_logical_rewriting.rs",
    "crates/fln-cli/tests/source_match_alternative_groups.rs",
    "crates/fln-cli/tests/source_match_discriminants.rs",
    "crates/fln-cli/tests/source_match_equations.rs",
    "crates/fln-cli/tests/source_multistage_callbacks.rs",
    "crates/fln-cli/tests/source_mutual_data.rs",
    "crates/fln-cli/tests/source_mutual_function_children.rs",
    "crates/fln-cli/tests/source_mutual_groups.rs",
    "crates/fln-cli/tests/source_mutual_indexed.rs",
    "crates/fln-cli/tests/source_nat_literal_arithmetic.rs",
    "crates/fln-cli/tests/source_nat_runtime.rs",
    "crates/fln-cli/tests/source_native_decide.rs",
    "crates/fln-cli/tests/source_nested_actions.rs",
    "crates/fln-cli/tests/source_nested_decreasing_goals.rs",
    "crates/fln-cli/tests/source_nested_lets.rs",
    "crates/fln-cli/tests/source_noncomputable.rs",
    "crates/fln-cli/tests/source_noncomputable_regressions.rs",
    "crates/fln-cli/tests/source_olean_metadata.rs",
    "crates/fln-cli/tests/source_ordinary_loops.rs",
    "crates/fln-cli/tests/source_partial_definitions.rs",
    "crates/fln-cli/tests/source_private_legacy.rs",
    "crates/fln-cli/tests/source_proof_indices.rs",
    "crates/fln-cli/tests/source_proof_runtime.rs",
    "crates/fln-cli/tests/source_protected_aliases.rs",
    "crates/fln-cli/tests/source_quoted_names.rs",
    "crates/fln-cli/tests/source_quotient_runtime.rs",
    "crates/fln-cli/tests/source_quotients.rs",
    "crates/fln-cli/tests/source_range_literals.rs",
    "crates/fln-cli/tests/source_record_diamonds.rs",
    "crates/fln-cli/tests/source_record_runtime.rs",
    "crates/fln-cli/tests/source_reduce.rs",
    "crates/fln-cli/tests/source_reducibility_attributes.rs",
    "crates/fln-cli/tests/source_rewrite_closing.rs",
    "crates/fln-cli/tests/source_rewrite_universe_metavariables.rs",
    "crates/fln-cli/tests/source_rule_application.rs",
    "crates/fln-cli/tests/source_scopes.rs",
    "crates/fln-cli/tests/source_search_config.rs",
    "crates/fln-cli/tests/source_search_congruence.rs",
    "crates/fln-cli/tests/source_search_construction.rs",
    "crates/fln-cli/tests/source_search_reflexivity.rs",
    "crates/fln-cli/tests/source_section_data.rs",
    "crates/fln-cli/tests/source_selected_search.rs",
    "crates/fln-cli/tests/source_sequence_notation.rs",
    "crates/fln-cli/tests/source_sigma_binders.rs",
    "crates/fln-cli/tests/source_simp_arith.rs",
    "crates/fln-cli/tests/source_simp_binders.rs",
    "crates/fln-cli/tests/source_simp_config.rs",
    "crates/fln-cli/tests/source_simp_explicit_lemma_keys.rs",
    "crates/fln-cli/tests/source_simp_hypotheses.rs",
    "crates/fln-cli/tests/source_simp_nat_procedures.rs",
    "crates/fln-cli/tests/source_simp_permutation.rs",
    "crates/fln-cli/tests/source_simp_quantifiers.rs",
    "crates/fln-cli/tests/source_simpa.rs",
    "crates/fln-cli/tests/source_singleton_inference.rs",
    "crates/fln-cli/tests/source_stateful_loops.rs",
    "crates/fln-cli/tests/source_syntax_worlds.rs",
    "crates/fln-cli/tests/source_tactic_match_letrec.rs",
    "crates/fln-cli/tests/source_tactic_match_numerals.rs",
    "crates/fln-cli/tests/source_term_binders.rs",
    "crates/fln-cli/tests/source_term_do_elements.rs",
    "crates/fln-cli/tests/source_transparency_tactics.rs",
    "crates/fln-cli/tests/source_unfold.rs",
    "crates/fln-cli/tests/source_unit_like.rs",
    "crates/fln-cli/tests/source_unsafe_definitions.rs",
    "crates/fln-cli/tests/source_variant_runtime.rs",
    "crates/fln-cli/tests/source_wf_tactic_macros.rs",
    "crates/fln-cli/tests/source_while_loops.rs",
    "crates/fln-cli/tests/split_tactic.rs",
    "crates/fln-cli/tests/string_extern_probes.rs",
    "crates/fln-cli/tests/structural_course_of_values.rs",
    "crates/fln-cli/tests/unused_variables_lint.rs",
    "crates/fln-lake/tests/lake_config_and_actions.rs",
    "crates/fln-parse/src/extensions/artifacts/tests/abbreviations.rs",
    "crates/fln-parse/src/lib.rs",
    "crates/fln-parse/tests/scoped_layout.rs",
    "crates/fln-server/tests/lsp_semantic_correlation.rs",
    "crates/fln-unsafe-abi/src/handle/fs/bytes/tests.rs",
    "crates/fln-unsafe-abi/src/handle/fs/directory.rs",
    "crates/fln-unsafe-abi/src/handle/fs/read/tests.rs",
    "crates/fln-unsafe-abi/src/handle/fs/tests.rs",
    "crates/fln-unsafe-abi/src/handle/stdio_input_tests.rs",
    "crates/fln-unsafe-abi/src/handle/stdio_tests.rs",
    "crates/fln-vm/tests/fs_mutations.rs",
    "crates/fln-vm/tests/fs_read_bytes.rs",
    "crates/fln-vm/tests/fs_read_line.rs",
    "crates/fln-vm/tests/fs_write.rs",
    "crates/fln-vm/tests/fs_write_bytes.rs",
    "crates/fln/src/imported_ir/native_signature/tests/levels_reference.rs",
    "crates/fln/src/imported_macros/tests/identifiers_reference.rs",
    "crates/fln/src/runtime/fs/tests.rs",
    "crates/fln/src/source_intrinsics/string_bootstrap/tests.rs",
    "crates/fln/tests/runtime_case_callbacks.rs",
    "crates/fln/tests/runtime_course_of_values.rs",
    "crates/fln/tests/runtime_dependent_nat_motives.rs",
    "crates/fln/tests/runtime_imported_partial_conditionals.rs",
    "crates/fln/tests/runtime_list_course_of_values.rs",
    "crates/fln/tests/runtime_nested_data.rs",
    "crates/fln/tests/runtime_st_authority/callable_payloads.rs",
    "crates/fln/tests/runtime_thunks.rs",
    "crates/fln/tests/source_ac_rfl.rs",
    "crates/fln/tests/source_ac_tactics.rs",
    "crates/fln/tests/source_contextual_result_hints.rs",
    "crates/fln/tests/source_course_of_values.rs",
    "crates/fln/tests/source_course_reduction.rs",
    "crates/fln/tests/source_dependent_match_context.rs",
    "crates/fln/tests/source_ellipsis.rs",
    "crates/fln/tests/source_grind.rs",
    "crates/fln/tests/source_grind/definitions.rs",
    "crates/fln/tests/source_grind/existentials.rs",
    "crates/fln/tests/source_grind/modifiers.rs",
    "crates/fln/tests/source_import_aliases.rs",
    "crates/fln/tests/source_indexed_history_conversion.rs",
    "crates/fln/tests/source_inductive_optional_fields.rs",
    "crates/fln/tests/source_module_artifacts/aliases.rs",
    "crates/fln/tests/source_mutual_ordinary.rs",
    "crates/fln/tests/source_mutual_well_founded.rs",
    "crates/fln/tests/source_predefinition_recursion.rs",
    "crates/fln/tests/source_public_stdlib.rs",
    "crates/fln/tests/source_quotation_scope.rs",
    "crates/fln/tests/source_simp_instance_matching.rs",
];

/// Files whose needle sites materialize nothing: fence probes building synthetic
/// paths to interrogate the predicate, and a doc comment plus an error-case input.
const NON_PRODUCER: &[&str] = &[
    "crates/fln-unsafe-region/src/tests.rs",
    "tools/structure-guard/src/scratch.rs",
    "tools/structure-guard/tests/common/mod.rs",
];

/// Directories the source walk refuses: build output is not source, and
/// `crates/fln-conformance/target/` is exactly where this suite's worker-refusal
/// fixtures live.
const SKIP_DIRS: &[&str] = &["target", "target_local", ".git"];

fn walk_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("walk must read {}: {error}", dir.display()));
    for entry in entries {
        let path = entry
            .unwrap_or_else(|error| panic!("walk entry under {}: {error}", dir.display()))
            .path();
        let file_type = path
            .symlink_metadata()
            .unwrap_or_else(|error| panic!("walk stat {}: {error}", path.display()))
            .file_type();
        if file_type.is_dir() {
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if !SKIP_DIRS.contains(&name) {
                walk_rs_files(&path, out);
            }
        } else if file_type.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

fn read(root: &Path, relative: &str) -> String {
    let path = root.join(relative);
    assert!(
        path.is_file(),
        "expected file is missing: {}",
        path.display()
    );
    std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("expected file is unreadable: {}: {error}", path.display()))
}

#[test]
fn every_temp_dir_call_site_is_classified() {
    let root = fln_conformance::checked_workspace_root!();
    let root = root.as_path();

    let mut files = Vec::new();
    for top in ["crates", "tools", "tribunal"] {
        walk_rs_files(&root.join(top), &mut files);
    }
    assert!(
        files.len() >= 200,
        "refusing a vacuous walk: only {} Rust files under crates/+tools/+tribunal/ \
         (262 at the census commit); a walk this small is broken, not clean",
        files.len()
    );

    let mut needle_files: Vec<String> = files
        .iter()
        .filter_map(|path| {
            let text = std::fs::read_to_string(path).ok()?;
            text.contains(NEEDLE).then(|| {
                path.strip_prefix(root)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned()
            })
        })
        .collect();
    needle_files.sort();

    // The exclusion must match exactly once, proving the walk can see this file before
    // it is trusted to see any other.
    let self_count = needle_files
        .iter()
        .filter(|f| f.as_str() == SELF_PATH)
        .count();
    assert_eq!(
        self_count, 1,
        "the walk must find this census exactly once before it is excluded; found \
         {self_count} — a renamed census file vacates the walk it asserts over"
    );
    needle_files.retain(|f| f != SELF_PATH);

    let remainder_files: Vec<&str> = SCRATCH_FAMILIES
        .iter()
        .filter(|family| !family.routed)
        .map(|family| family.producer)
        .collect();

    let mut unclassified = Vec::new();
    for found in &needle_files {
        let in_machinery = MACHINERY.contains(&found.as_str());
        let in_remainder = remainder_files.contains(&found.as_str());
        let in_self_cleaning = SELF_CLEANING.iter().any(|(path, _)| path == found);
        let in_non_producer = NON_PRODUCER.contains(&found.as_str());
        let in_unrouted_cli = UNROUTED_CLI_PRODUCERS.contains(&found.as_str());
        let classes = in_machinery as usize
            + in_remainder as usize
            + in_self_cleaning as usize
            + in_non_producer as usize
            + in_unrouted_cli as usize;
        if classes != 1 {
            unclassified.push(format!("{found} (in {classes} classes)"));
        }
    }
    assert!(
        unclassified.is_empty(),
        "every {NEEDLE} call site must be in exactly one class — machinery, declared \
         remainder, self-cleaning, non-producer, or unrouted CLI producer. An entry here is either a new \
         scratch producer bypassing the fence (route it through ScratchRoot with a new \
         SCRATCH_FAMILIES row) or a class this census has not been told about:\n{}",
        unclassified.join("\n")
    );

    // Every class member must be present in the walk, so a deleted or renamed file
    // cannot leave its classification behind as a slot for a future mismatch.
    let mut missing = Vec::new();
    for path in MACHINERY
        .iter()
        .chain(NON_PRODUCER.iter())
        .chain(remainder_files.iter())
        .chain(SELF_CLEANING.iter().map(|(path, _)| path))
        .chain(UNROUTED_CLI_PRODUCERS.iter())
    {
        if !needle_files.iter().any(|found| found == path) {
            missing.push(*path);
        }
    }
    assert!(
        missing.is_empty(),
        "these classified files no longer carry {NEEDLE}; their classes are stale and \
         must be removed in the same edit that stopped the call:\n{}",
        missing.join("\n")
    );

    // Self-cleaning is only a class while the cleanup exists.
    for (path, cleanup) in SELF_CLEANING {
        let text = read(root, path);
        assert!(
            text.contains(cleanup),
            "{path} is classified self-cleaning but no longer carries `{cleanup}`: a \
             file that stops removing its own roots is a producer, not self-cleaning"
        );
    }

    assert!(
        needle_files.len() >= 9,
        "refusing a vacuous classification: only {} needle files (expected machinery + \
         remainders + self-cleaning + non-producers); a walk this small is broken, not \
         clean",
        needle_files.len()
    );
}

#[test]
fn every_family_row_is_bound_to_its_source() {
    let root = fln_conformance::checked_workspace_root!();
    let root = root.as_path();

    let mut routed = 0usize;
    let mut remainder_prefixes = Vec::new();
    for family in SCRATCH_FAMILIES {
        let text = read(root, family.producer);
        assert!(
            text.len() > 512,
            "refusing a vacuous scan: {} is implausibly small at {} bytes",
            family.producer,
            text.len()
        );

        if family.routed {
            // The constant must be the FIRST ARGUMENT of the construction, not merely
            // present in the file: bind the call site, which is the thing that could
            // actually drift (the fence probe in tests/common/mod.rs legitimately
            // carries the literal as test input, so a blanket literal ban is a wall
            // against a correct file).
            assert!(
                text.contains(&format!("ScratchRoot::create({}", family.constant)),
                "{} is routed but never calls ScratchRoot::create({}); the declared \
                 prefix {:?} therefore has no producer binding it",
                family.producer,
                family.constant,
                family.prefix
            );
            routed += 1;
        } else {
            // A remainder cannot name the constant — its producer has no dependency on
            // the fence's crate, which is the whole reason it is a remainder — so the
            // literal is the only spelling available, and its absence means the
            // disclosure names a producer that no longer produces it.
            assert!(
                text.contains(&format!("\"{}", family.prefix)),
                "{} is a declared remainder but does not carry the literal {:?}",
                family.producer,
                family.prefix
            );
            remainder_prefixes.push(family.prefix);
        }

        let constructs_guard = text.contains("ScratchRoot::create");
        assert_eq!(
            constructs_guard, family.routed,
            "{} routed={} but constructs_guard={}: a routed producer must build a \
             ScratchRoot and a declared remainder must not",
            family.producer, family.routed, constructs_guard
        );
    }

    // Conservation and exact membership, in both directions: the remainder cannot be
    // emptied by deleting a row instead of routing its producer, and neither side can
    // grow without a deliberate edit to this census.
    assert_eq!(
        SCRATCH_FAMILIES.len(),
        18,
        "the workspace declares exactly 18 scratch families; a change here is a \
         deliberate, disclosed act"
    );
    assert_eq!(routed, 15, "exactly 15 producers route through ScratchRoot");
    remainder_prefixes.sort_unstable();
    assert_eq!(
        remainder_prefixes,
        ["fln-derive-", "fln-epoch-lab-", "fln-ownership-publisher-"],
        "the declared remainder is exactly these three rows"
    );
}

/// `franken_lean-eir2` acceptance criterion 3 for the vdi4 family: retention on failure,
/// proved in BOTH directions through the family's own constructor. Lives here rather than
/// beside the producer because `golden_vellum.rs` is a pin-dependent surface and the
/// CI-execution join reads citations into it as unexecuted (see the file header).
#[test]
fn vdi4_workspaces_reclaim_on_pass_and_retain_on_failure() {
    let passing = {
        let root = ScratchRoot::create(VDI4_PREFIX, "golden-vellum", "reclaim-pass")
            .expect("create passing workspace");
        root.path().to_path_buf()
    };
    assert!(
        !passing.exists(),
        "a passing cell's workspace must be reclaimed: {}",
        passing.display()
    );

    let observed = std::cell::RefCell::new(None);
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let root = ScratchRoot::create(VDI4_PREFIX, "golden-vellum", "reclaim-fail")
            .expect("create failing workspace");
        *observed.borrow_mut() = Some(root.path().to_path_buf());
        panic!("deliberate failure so the fixture guard drops during an unwind");
    }));
    assert!(unwound.is_err(), "the failing cell must actually unwind");
    let retained = observed
        .into_inner()
        .expect("the failing cell materialized before it panicked");
    assert!(
        retained.exists(),
        "a failing cell's workspace must be retained: {}",
        retained.display()
    );
    std::fs::remove_dir_all(&retained).expect("the probe reclaims what it retained");
}

/// `franken_lean-eir2` acceptance criterion 3 for the refdiff family: retention on
/// failure, proved in BOTH directions through the family's own constructor. Lives here
/// rather than beside the producer because `reference_differential.rs` asks the pinned
/// Reference and the CI-execution join reads citations into it as unexecuted (see the
/// file header).
#[test]
fn reference_differential_roots_reclaim_on_pass_and_retain_on_failure() {
    let passing = {
        let root = ScratchRoot::create(REFDIFF_PREFIX, "reference-differential", "reclaim-pass")
            .expect("create passing workspace");
        root.path().to_path_buf()
    };
    assert!(
        !passing.exists(),
        "a passing cell's oracle workspace must be reclaimed: {}",
        passing.display()
    );

    let observed = std::cell::RefCell::new(None);
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let root = ScratchRoot::create(REFDIFF_PREFIX, "reference-differential", "reclaim-fail")
            .expect("create failing workspace");
        *observed.borrow_mut() = Some(root.path().to_path_buf());
        panic!("deliberate failure so the fixture guard drops during an unwind");
    }));
    assert!(unwound.is_err(), "the failing cell must actually unwind");
    let retained = observed
        .into_inner()
        .expect("the failing cell materialized before it panicked");
    assert!(
        retained.exists(),
        "a failing cell's oracle workspace must be retained: {}",
        retained.display()
    );
    std::fs::remove_dir_all(&retained).expect("the probe reclaims what it retained");
}
