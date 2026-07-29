//! Closed-world G0-4 fixture manifest and provenance contract.

#![forbid(unsafe_code)]

use fln_conformance::syntax_hygiene::{
    CORPUS_COMMIT, FixtureFamily, FixtureManifest, REFERENCE_COMMIT, TRACE_CONTRACT_SCHEMA,
    fixture_digest, grammar_phase_roots, measure_contract_usage, run_budget_matrix,
    stock_trace_contract,
};

const MANIFEST: &str = include_str!("../fixtures/g04_syntax_manifest.tsv");
const REFERENCE_FIXTURE: &str = include_str!("../fixtures/g04_reference_fixture.lean");
const SEMANTIC_EVIDENCE: &str =
    include_str!("../evidence/g04_syntax_hygiene/semantic_v4.32.0.ndjson");
const TELEMETRY_EVIDENCE: &str =
    include_str!("../evidence/g04_syntax_hygiene/telemetry_v4.32.0.ndjson");
const MUTATION_EVIDENCE: &str =
    include_str!("../evidence/g04_syntax_hygiene/mutation_campaign_v4.32.0.ndjson");
const REGEN_EVIDENCE: &str = include_str!("../evidence/g04_syntax_hygiene/regen_v4.32.0.ndjson");

#[test]
fn syntax_fixture_manifest() {
    let manifest = FixtureManifest::load_embedded().expect("the embedded manifest is well formed");
    assert_eq!(manifest.rows().len(), 10);
    assert_eq!(
        manifest
            .rows()
            .iter()
            .filter(|row| row.family == FixtureFamily::C0)
            .count(),
        3
    );
    assert_eq!(
        manifest
            .rows()
            .iter()
            .filter(|row| row.family == FixtureFamily::C1)
            .count(),
        4
    );
    assert_eq!(
        manifest
            .rows()
            .iter()
            .filter(|row| row.family == FixtureFamily::C2)
            .count(),
        3
    );
    let grammar_validation = manifest.validate_grammar_roots();
    assert!(
        grammar_validation.is_ok(),
        "grammar-root validation failed: {:?}; derived={:?}",
        grammar_validation.as_ref().err(),
        grammar_phase_roots()
    );
    grammar_validation.expect("grammar-root success was asserted");
    let trace = stock_trace_contract().expect("stock G0-9 trace contract");
    assert_eq!(trace.schema, TRACE_CONTRACT_SCHEMA);
    assert_eq!(trace.elab_step_count, 261);
    assert!(trace.event_count > trace.elab_step_count);

    for row in manifest.rows() {
        assert_eq!(row.grammar_root.len(), 64);
        match row.family {
            FixtureFamily::C0 => assert_eq!(row.origin_rev, "g04-owned/1"),
            FixtureFamily::C1 => assert_eq!(row.origin_rev, REFERENCE_COMMIT),
            FixtureFamily::C2 => assert_eq!(row.origin_rev, CORPUS_COMMIT),
        }
    }

    for (line_number, fixture_id) in [
        (61, "c0_pratt_trivia"),
        (62, "c0_unicode_positions"),
        (63, "c0_missing_rhs"),
    ] {
        let line = REFERENCE_FIXTURE.lines().nth(line_number - 1);
        assert!(line.is_some(), "owned origin line {line_number} is absent");
        let line = line.expect("owned origin-line presence was asserted");
        assert!(
            line.contains(fixture_id),
            "{fixture_id} is not anchored at declared line {line_number}: {line:?}"
        );
    }
    assert!(REFERENCE_FIXTURE.contains(
        r#"run_cmd observeParse "c0_pratt_trivia" `term "1 + /- nested /- block -/ trivia -/ 2 * 3""#
    ));
    assert!(
        REFERENCE_FIXTURE
            .contains(r#"run_cmd observeParse "c0_unicode_positions" `term "α + β -- trailing\n""#)
    );
    assert!(
        REFERENCE_FIXTURE.contains(r#"syntax "call" term:max "(" sepBy1(term, ",") ")" : term"#)
    );
    assert!(
        REFERENCE_FIXTURE.contains(r#"| `(call $f ($args,*)) => `($f $args*)"#),
        "the pinned Lean C1 successful macro arm must remain exact"
    );
    assert!(REFERENCE_FIXTURE.contains(
        r#""!![" ppRealGroup(sepBy1(ppGroup(term,+,?), ";", "; ", allowTrailingSep)) "]" : term"#
    ));
    assert!(
        REFERENCE_FIXTURE.contains(r#"| `(!![$[$[$rows],*];*]) => do"#),
        "the pinned mathlib C2 successful macro arm must remain exact"
    );
}

#[test]
fn manifest_mutants_are_refused_and_cannot_borrow_the_embedded_root() {
    let baseline = FixtureManifest::parse(MANIFEST).expect("baseline manifest");

    let wrong_schema =
        MANIFEST.replacen("fln-g04-syntax-manifest/1", "fln-g04-syntax-manifest/2", 1);
    assert!(FixtureManifest::parse(&wrong_schema).is_err());

    let weakened_facets = MANIFEST.replacen(
        "tokens,tree,sourceinfo,trivia,positions,recovery",
        "tokens,tree,sourceinfo,trivia,positions",
        1,
    );
    assert!(FixtureManifest::parse(&weakened_facets).is_err());

    let duplicate_id = MANIFEST.replacen("c0_unicode_positions", "c0_pratt_trivia", 1);
    assert!(FixtureManifest::parse(&duplicate_id).is_err());

    let without_last_row = MANIFEST
        .lines()
        .take(MANIFEST.lines().count() - 1)
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    assert!(FixtureManifest::parse(&without_last_row).is_err());

    let first_root = &baseline.rows()[0].grammar_root;
    let changed_root = MANIFEST.replacen(first_root, &"0".repeat(64), 1);
    let mutant =
        FixtureManifest::parse(&changed_root).expect("a root mutant stays structurally parseable");
    assert_ne!(
        mutant.root(),
        baseline.root(),
        "the parsed bytes, not the embedded include, must determine the manifest root"
    );
    assert!(
        mutant.validate_grammar_roots().is_err(),
        "a row cannot declare an arbitrary grammar root"
    );
}

#[test]
fn committed_evidence_is_closed_world_and_semantic_telemetry_are_disjoint() {
    let fixture_ids = [
        "c0_pratt_trivia",
        "c0_unicode_positions",
        "c0_missing_rhs",
        "c1_call_before_registration",
        "c1_call_parse",
        "c1_call_expand",
        "c1_call_malformed",
        "c2_matrix_parse",
        "c2_matrix_expand",
        "c2_matrix_uneven",
    ];
    let semantic_lines = SEMANTIC_EVIDENCE.lines().collect::<Vec<_>>();
    assert_eq!(semantic_lines.len(), fixture_ids.len());
    for (sequence, (line, fixture)) in semantic_lines.iter().zip(fixture_ids).enumerate() {
        assert!(line.starts_with(r#"{"schema":"fln-g04-semantic/1","#));
        assert!(line.contains(&format!(r#""sequence":{sequence},"#)));
        assert!(line.contains(&format!(r#""step_id":"{fixture}","#)));
        assert!(line.contains(&format!(r#""fixture":"{fixture}","#)));
        assert!(line.contains(&format!(r#""parity_row":"g04:{fixture}","#)));
        assert!(line.contains(r#""process_exit":0,"signal":"none""#));
        assert!(line.ends_with(r#""final_state":"classified"}"#));
        for telemetry_only in [
            "wall_micros",
            "peak_rss_bytes",
            "monotonic_start_micros",
            r#""host":"#,
            r#""pid":"#,
        ] {
            assert!(
                !line.contains(telemetry_only),
                "semantic row {fixture} leaked telemetry field {telemetry_only}"
            );
        }
    }
    assert_eq!(
        semantic_lines
            .iter()
            .filter(|line| line.contains(r#""classification":"exact""#))
            .count(),
        2
    );
    assert_eq!(
        semantic_lines
            .iter()
            .filter(|line| line.contains(r#""classification":"contract-gap""#))
            .count(),
        8
    );
    assert_eq!(
        fixture_digest(SEMANTIC_EVIDENCE.as_bytes()),
        "989b0fc54faa664a0ff1b0f901a1ed42c4ce4546b36431559d2fd244470e308e"
    );

    let telemetry_lines = TELEMETRY_EVIDENCE.lines().collect::<Vec<_>>();
    assert_eq!(telemetry_lines.len(), 1);
    let telemetry = telemetry_lines[0];
    assert!(telemetry.starts_with(r#"{"schema":"fln-g04-telemetry/1","#));
    assert!(telemetry.contains(r#""claim":"nonsemantic-run-facts""#));
    assert!(telemetry.contains(r#""peak_rss_state":"sampled","peak_rss_bytes":"#));
    assert!(!telemetry.contains(r#""peak_rss_bytes":null"#));
    assert!(telemetry.contains(r#""reference_processes":2"#));
    assert!(telemetry.ends_with(r#""final_state":"telemetry_only"}"#));
    for semantic_only in [
        "source_root",
        "reference_root",
        "local_root",
        "grammar_root",
        "first_divergence",
        r#""classification":"#,
    ] {
        assert!(
            !telemetry.contains(semantic_only),
            "telemetry leaked semantic field {semantic_only}"
        );
    }

    let mutants = [
        (
            "stale_parser_epoch",
            "test:fln-conformance::grammar_epoch_transition_model::grammar_epoch_transition_model",
        ),
        (
            "byte_character_position_drift",
            "test:fln-conformance::g0_4_no_mock_e2e::g0_4_no_mock_e2e",
        ),
        (
            "scope_drop",
            "test:fln-conformance::hygiene_scope_capture_model::hygiene_scope_capture_model",
        ),
        (
            "scope_capture",
            "test:fln-conformance::hygiene_scope_capture_model::hygiene_scope_capture_model",
        ),
        (
            "precedence_associativity_swap",
            "test:fln-parse::pratt_precedence_model::every_observation_actually_discriminates_the_grouping",
        ),
        (
            "source_normalization",
            "test:fln-conformance::g0_4_no_mock_e2e::g0_4_no_mock_e2e",
        ),
        (
            "timing_derived_generated_name",
            "test:fln-conformance::quotation_splice_model::quotation_splice_model",
        ),
        (
            "comparison_downgrade",
            "test:fln-conformance::g0_4_no_mock_e2e::g0_4_no_mock_e2e",
        ),
        (
            "hidden_exclusion",
            "test:fln-conformance::syntax_fixture_manifest::syntax_fixture_manifest",
        ),
        (
            "second_patch_or_schema",
            "test:fln-conformance::g0_4_no_mock_e2e::g0_4_no_mock_e2e",
        ),
        (
            "partial_publication",
            "test:fln-conformance::syntax_budget_matrix::every_budget_and_cancellation_boundary_is_atomic_and_retryable",
        ),
        (
            "fake_thread_partition",
            "test:fln-conformance::syntax_budget_matrix::syntax_budget_matrix",
        ),
        (
            "terminal_newline_epilogue",
            "test:fln-syntax::attach::tests::a_terminal_token_keeps_its_final_comment_and_newline",
        ),
    ];
    let mutation_lines = MUTATION_EVIDENCE.lines().collect::<Vec<_>>();
    assert_eq!(mutation_lines.len(), mutants.len());
    for (sequence, (line, (mutant, killer))) in mutation_lines.iter().zip(mutants).enumerate() {
        assert_eq!(
            *line,
            format!(
                "{{\"schema\":\"fln-g04-mutation/1\",\"sequence\":{sequence},\
                 \"mutant\":\"{mutant}\",\"class\":\"planted-cell\",\
                 \"expected\":\"killed\",\"actual\":\"killed\",\
                 \"killer\":\"{killer}\"}}"
            )
        );
    }
    eprintln!(
        "g04-evidence-roots semantic={} telemetry={} mutation={} regen={}",
        fixture_digest(SEMANTIC_EVIDENCE.as_bytes()),
        fixture_digest(TELEMETRY_EVIDENCE.as_bytes()),
        fixture_digest(MUTATION_EVIDENCE.as_bytes()),
        fixture_digest(REGEN_EVIDENCE.as_bytes())
    );

    let regen_lines = REGEN_EVIDENCE.lines().collect::<Vec<_>>();
    assert_eq!(regen_lines.len(), 1);
    let regen = regen_lines[0];
    assert!(regen.starts_with(r#"{"schema":"fln-g04-regen/1","#));
    let manifest = FixtureManifest::load_embedded().expect("manifest");
    let trace = stock_trace_contract().expect("stock G0-9 trace");
    let budget = run_budget_matrix(&manifest, 32).expect("budget matrix");
    let usage = measure_contract_usage(&manifest).expect("contract usage");
    for (field, value) in [
        ("manifest_root", manifest.root()),
        (
            "semantic_root",
            fixture_digest(SEMANTIC_EVIDENCE.as_bytes()),
        ),
        (
            "telemetry_root",
            fixture_digest(TELEMETRY_EVIDENCE.as_bytes()),
        ),
        (
            "mutation_root",
            fixture_digest(MUTATION_EVIDENCE.as_bytes()),
        ),
        ("trace_root", trace.fixture_root),
        ("budget_root", budget.stream_root),
        ("usage_root", usage.root()),
    ] {
        assert!(
            regen.contains(&format!(r#""{field}":"{value}""#)),
            "regeneration receipt does not bind {field}={value}"
        );
    }
    assert!(regen.contains(r#""reference_processes":2,"repetitions_equal":true"#));
    assert!(regen.contains(r#""exact":2,"contract_gaps":8,"unclassified":0"#));
    assert!(regen.contains(r#""decision":"amended""#));
    assert!(!regen.contains(r#""decision":"ratified""#));
    assert!(regen.ends_with(r#""final_state":"classified"}"#));
}
