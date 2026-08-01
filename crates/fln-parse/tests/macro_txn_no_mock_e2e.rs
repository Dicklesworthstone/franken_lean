//! Real public-API no-mock evidence for W4 macro transactions.

#![forbid(unsafe_code)]

use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::{InternalFault, Outcome};
use fln_hash::domain::{Digest, Domain, hash};
use fln_parse::macro_expand::{
    HygienePolicy, MacroExpansion, MacroExpansionBudget, MacroExpansionCoordinates,
    MacroExpansionError, MacroExpansionInput, QuotationContext, QuotationTemplate, QuotedSyntax,
};
use fln_parse::macro_txn::{
    CanonicalPath, DiagnosticRetention, MacroCacheability, MacroCapabilities, MacroCapabilityEvent,
    MacroDiagnostic, MacroInvocationIdentity, MacroMemo, MacroMemoLookup, MacroMemoRefusal,
    MacroRunReport, MacroState, MacroTxnAbort, MacroTxnBudget, MacroTxnCheckpoint, MacroTxnConfig,
    MacroTxnError, MacroTxnProduct, MacroValue, expand_quotation_transactional,
    run_macro_transaction,
};
use fln_parse::registry::GrammarEpoch;
use fln_parse::state::null_kind;
use fln_syntax::hygiene::{ExpansionOrigin, ExpansionPath};
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};
use fln_syntax::tree::Syntax;
use std::fmt::Write as _;
use std::path::Path;

const SEMANTIC_SCHEMA: &str = "fln.e2e.macro-txn-semantic/1";
const TELEMETRY_SCHEMA: &str = "fln.e2e.macro-txn-telemetry/1";

fn name(value: &str) -> Name {
    Name::from_components(["Main", value])
}

fn epoch() -> GrammarEpoch {
    GrammarEpoch::from_parts(31, Digest([0x31; 32]))
}

fn identity(label: &str, mode: Mode) -> MacroInvocationIdentity {
    MacroInvocationIdentity::from_canonical_row(
        epoch(),
        mode,
        format!("fln.e2e.macro-txn/1\0{label}").into_bytes(),
    )
}

fn baseline() -> MacroState {
    let mut state = MacroState::new();
    state.insert_environment(name("present"), MacroValue::from_text("old"));
    state.insert_extension(name("base_extension"), MacroValue::from_text("enabled"));
    state.insert_option(name("trace"), MacroValue::from_text("false"));
    state.set_next_gensym(5);
    state
}

fn baseline_capabilities() -> MacroCapabilities {
    let mut capabilities = MacroCapabilities::new();
    capabilities.insert_file(
        CanonicalPath::new("/workspace/macro-input.lean").expect("canonical capability path"),
        b"def input := 1\n".to_vec(),
    );
    capabilities
}

fn complete_product<T>(report: MacroRunReport<T>) -> MacroTxnProduct<T> {
    match report.into_status() {
        Outcome::Complete(Ok(product)) => product,
        _ => panic!("expected completed macro product"),
    }
}

fn positive_product() -> (
    MacroState,
    MacroCapabilities,
    MacroInvocationIdentity,
    MacroTxnProduct<String>,
) {
    let state = baseline();
    let capabilities = baseline_capabilities();
    let identity = identity("positive", Mode::Sound);
    let input_path =
        CanonicalPath::new("/workspace/macro-input.lean").expect("canonical capability path");
    let report = run_macro_transaction(
        MacroTxnConfig::new(
            identity.clone(),
            &state,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            assert_eq!(
                txn.read_environment(&name("present"))?,
                Some(MacroValue::from_text("old"))
            );
            assert_eq!(txn.read_environment(&name("missing"))?, None);
            assert_eq!(
                txn.read_option(&name("trace"))?,
                Some(MacroValue::from_text("false"))
            );
            assert_eq!(
                txn.iterate_extensions()?,
                vec![(name("base_extension"), MacroValue::from_text("enabled"))]
            );
            assert_eq!(
                txn.read_file(&input_path)?,
                Some(MacroValue::from_text("def input := 1\n"))
            );
            txn.set_environment(name("committed"), MacroValue::from_text("root"))?;

            txn.begin_nested()?;
            txn.set_environment(name("rolled_back"), MacroValue::from_text("private"))?;
            txn.emit_diagnostic(MacroDiagnostic::new(
                "nested-visible",
                "retained across nested rollback",
                DiagnosticRetention::FailureVisible,
                None,
            ))?;
            txn.emit_diagnostic(MacroDiagnostic::new(
                "nested-private",
                "discarded with nested rollback",
                DiagnosticRetention::CommitOnly,
                None,
            ))?;
            txn.rollback_nested()?;

            txn.begin_nested()?;
            txn.set_option(name("trace"), MacroValue::from_text("true"))?;
            txn.set_extension(name("txn_extension"), MacroValue::from_text("on"))?;
            txn.commit_nested()?;
            assert_eq!(txn.fresh_gensym()?, 5);
            txn.emit_diagnostic(MacroDiagnostic::new(
                "committed",
                "published with the successful transaction",
                DiagnosticRetention::CommitOnly,
                None,
            ))?;
            Ok("expanded:old:false".to_string())
        },
    );
    assert_eq!(
        state,
        baseline(),
        "execution must leave the public state unchanged"
    );
    (state, capabilities, identity, complete_product(report))
}

fn state_root(state: &MacroState) -> String {
    state.identity().digest().to_hex()
}

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(BytePos(start), BytePos(end)).expect("forward span")
}

fn info(start: usize, end: usize) -> SourceInfo {
    SourceInfo::Synthetic {
        pos: BytePos(start),
        end_pos: BytePos(end),
        canonical: true,
    }
}

fn expansion_coordinates() -> MacroExpansionCoordinates {
    MacroExpansionCoordinates {
        grammar_epoch: epoch(),
        mode: Mode::Sound,
        expansion_path: ExpansionPath::root(
            ExpansionOrigin::new(Name::from_components(["Main", "MacroTxnE2E"]), 9),
            4,
        ),
    }
}

fn quotation() -> QuotationContext {
    QuotationContext {
        name: Name::from_components(["Main", "macroTxnE2E", "_hygCtx"]),
        macro_scope: 13,
        call_site: Some(span(100, 120)),
        canonical: true,
        hygiene: HygienePolicy::Enabled,
    }
}

fn positive_expansion_input() -> MacroExpansionInput {
    MacroExpansionInput {
        coordinates: expansion_coordinates(),
        quotation: quotation(),
        template: QuotationTemplate::Node {
            definition_info: info(0, 8),
            kind: null_kind(),
            args: vec![QuotationTemplate::GeneratedIdent {
                definition_info: info(1, 2),
                raw_val: span(1, 2),
                base: Name::from_components(["generated"]),
                preresolved: Vec::new(),
                local_ordinal: 0,
            }],
        },
    }
}

fn failing_expansion_input() -> MacroExpansionInput {
    MacroExpansionInput {
        coordinates: expansion_coordinates(),
        quotation: quotation(),
        template: QuotationTemplate::Node {
            definition_info: info(0, 8),
            kind: Name::from_components(["Lean", "Parser", "Term"]),
            args: vec![QuotationTemplate::Splice {
                hole_info: info(1, 2),
                values: vec![QuotedSyntax::from_source(Syntax::atom(info(30, 31), "x"))],
            }],
        },
    }
}

fn expansion_root(expansion: &MacroExpansion) -> String {
    let mut canonical = format!("{:?};", expansion.syntax());
    canonical.push_str(&expansion.source_map().canonical());
    for generated in expansion.generated_names() {
        canonical.push_str(&generated.path.canonical());
        canonical.push_str(&generated.stable.to_display_string());
        canonical.push(';');
        canonical.push_str(&generated.hygienic.to_display_string());
        canonical.push(';');
    }
    write!(
        canonical,
        "visited={};output={};",
        expansion.stats().visited_nodes,
        expansion.stats().output_nodes
    )
    .expect("writing into a String cannot fail");
    hash(Domain::Fixture, canonical.as_bytes()).to_hex()
}

fn json_text(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for scalar in value.chars() {
        match scalar {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            scalar if scalar.is_control() => {
                write!(out, "\\u{:04x}", scalar as u32).expect("writing into a String cannot fail");
            }
            scalar => out.push(scalar),
        }
    }
    out.push('"');
    out
}

fn json_string_array(values: &[&str]) -> String {
    let mut out = String::from("[");
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            out.push(',');
        }
        out.push_str(&json_text(value));
    }
    out.push(']');
    out
}

fn json_usize_array(values: &[usize]) -> String {
    let mut out = String::from("[");
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            out.push(',');
        }
        write!(out, "{value}").expect("writing into a String cannot fail");
    }
    out.push(']');
    out
}

fn json_object(mut fields: Vec<(&str, String)>) -> String {
    fields.sort_unstable_by(|left, right| left.0.cmp(right.0));
    let mut out = String::from("{");
    for (index, (key, value)) in fields.into_iter().enumerate() {
        if index != 0 {
            out.push(',');
        }
        out.push_str(&json_text(key));
        out.push(':');
        out.push_str(&value);
    }
    out.push('}');
    out
}

fn write_evidence(
    artifact_dir: &Path,
    semantic_rows: &[String],
    run_id: &str,
    positive_operations: u64,
) {
    let mut semantic = semantic_rows.join("\n");
    semantic.push('\n');
    std::fs::write(artifact_dir.join("semantic.ndjson"), semantic)
        .expect("semantic evidence path is writable");
    let telemetry = json_object(vec![
        ("observed_semantic_rows", semantic_rows.len().to_string()),
        ("positive_operations", positive_operations.to_string()),
        ("productive_runs", "41".to_string()),
        ("run_id", json_text(run_id)),
        ("schema", json_text(TELEMETRY_SCHEMA)),
        ("thread_counts", json_usize_array(&[1, 8, 32])),
    ]);
    std::fs::write(
        artifact_dir.join("telemetry.ndjson"),
        format!("{telemetry}\n"),
    )
    .expect("telemetry evidence path is writable");
}

#[test]
fn macro_txn_no_mock_e2e() {
    let (initial, capabilities, invocation, product) = positive_product();
    let initial_root = state_root(&initial);
    assert_eq!(product.reads().observations().len(), 9);
    assert_eq!(product.effects().len(), 4);
    assert_eq!(product.operations(), 17);
    assert_eq!(
        product
            .diagnostics()
            .iter()
            .map(MacroDiagnostic::code)
            .collect::<Vec<_>>(),
        vec!["nested-visible", "committed"]
    );
    assert_eq!(product.capability_events().len(), 1);
    assert!(matches!(
        product.cacheability(),
        MacroCacheability::Cacheable
    ));

    let mut positive_state = initial.clone();
    let positive_published = product
        .clone()
        .publish(&mut positive_state, &capabilities)
        .expect("unchanged state admits the complete transaction");
    assert_eq!(positive_published.value(), "expanded:old:false");
    assert_eq!(
        positive_state.environment(&name("committed")),
        Some(&MacroValue::from_text("root"))
    );
    assert_eq!(positive_state.environment(&name("rolled_back")), None);
    assert_eq!(
        positive_state.extension(&name("txn_extension")),
        Some(&MacroValue::from_text("on"))
    );
    assert_eq!(
        positive_state.option(&name("trace")),
        Some(&MacroValue::from_text("true"))
    );
    assert_eq!(positive_state.next_gensym(), 6);
    let positive_root = state_root(&positive_state);
    assert_ne!(positive_root, initial_root);

    let (_, _, _, fresh_product) = positive_product();
    assert_eq!(fresh_product, product);
    let mut memo = MacroMemo::new();
    memo.insert(product.clone())
        .expect("complete read set admits memoization");
    let cached = match memo.lookup(&invocation, &initial, &capabilities) {
        MacroMemoLookup::Hit(cached) => cached.clone(),
        other => panic!("exact invocation did not hit: {other:?}"),
    };
    assert_eq!(cached, fresh_product);
    let mut cached_state = initial.clone();
    let cached_published = cached
        .publish(&mut cached_state, &capabilities)
        .expect("cached journal revalidates");
    let mut fresh_state = initial.clone();
    let fresh_published = fresh_product
        .publish(&mut fresh_state, &capabilities)
        .expect("fresh journal publishes");
    assert_eq!(cached_published, fresh_published);
    assert_eq!(cached_state, fresh_state);
    assert_eq!(state_root(&cached_state), positive_root);

    let collision_identity = MacroInvocationIdentity::from_decoded(
        invocation.digest(),
        b"fln.e2e.macro-txn/1\0different-complete-row".to_vec(),
        epoch(),
        Mode::Sound,
    );
    assert!(matches!(
        memo.lookup(&collision_identity, &initial, &capabilities),
        MacroMemoLookup::CollisionMiss
    ));
    let mut stale_negative = initial.clone();
    stale_negative.insert_environment(name("missing"), MacroValue::from_text("now-present"));
    assert!(matches!(
        memo.lookup(&invocation, &stale_negative, &capabilities),
        MacroMemoLookup::StaleReadMiss
    ));
    let mut stale_file = capabilities.clone();
    stale_file.insert_file(
        CanonicalPath::new("/workspace/macro-input.lean").expect("canonical path"),
        b"def input := 2\n".to_vec(),
    );
    assert!(matches!(
        memo.lookup(&invocation, &initial, &stale_file),
        MacroMemoLookup::StaleReadMiss
    ));
    let mut stale_option = initial.clone();
    stale_option.insert_option(name("trace"), MacroValue::from_text("changed"));
    assert!(matches!(
        memo.lookup(&invocation, &stale_option, &capabilities),
        MacroMemoLookup::StaleReadMiss
    ));
    let mut stale_iteration = initial.clone();
    stale_iteration.insert_extension(name("other"), MacroValue::from_text("added"));
    assert!(matches!(
        memo.lookup(&invocation, &stale_iteration, &capabilities),
        MacroMemoLookup::StaleReadMiss
    ));

    let unknown = complete_product(run_macro_transaction(
        MacroTxnConfig::new(
            identity("unknown", Mode::Faithful),
            &initial,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            txn.mark_uninstrumented_read("host callback outside capability context")?;
            Ok(())
        },
    ));
    assert!(matches!(
        unknown.cacheability(),
        MacroCacheability::Uncacheable { .. }
    ));
    assert!(matches!(
        MacroMemo::new().insert(unknown),
        Err(MacroMemoRefusal::Uncacheable { .. })
    ));
    let clock = complete_product(run_macro_transaction(
        MacroTxnConfig::new(
            identity("clock", Mode::Faithful),
            &initial,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| txn.observe_clock(71),
    ));
    assert!(matches!(
        clock.cacheability(),
        MacroCacheability::Uncacheable { .. }
    ));
    let sound_clock = run_macro_transaction(
        MacroTxnConfig::new(
            identity("clock-denied", Mode::Sound),
            &initial,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| txn.observe_clock(71),
    );
    assert!(matches!(
        sound_clock.status(),
        Outcome::Complete(Err(failure))
            if matches!(
                failure.error(),
                MacroTxnError::CapabilityDenied {
                    capability: "clock",
                    mode: Mode::Sound
                }
            )
    ));

    let failure = run_macro_transaction(
        MacroTxnConfig::new(
            identity("failure", Mode::Sound),
            &initial,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            txn.set_environment(name("leak"), MacroValue::from_text("private"))?;
            txn.emit_diagnostic(MacroDiagnostic::new(
                "failure-visible",
                "retained refusal explanation",
                DiagnosticRetention::FailureVisible,
                None,
            ))?;
            txn.emit_diagnostic(MacroDiagnostic::new(
                "failure-private",
                "discarded speculative explanation",
                DiagnosticRetention::CommitOnly,
                None,
            ))?;
            txn.observe_clock(72)?;
            Ok(())
        },
    );
    assert!(matches!(
        failure.status(),
        Outcome::Complete(Err(failure))
            if matches!(
                failure.error(),
                MacroTxnError::CapabilityDenied {
                    capability: "clock",
                    mode: Mode::Sound
                }
            )
    ));
    assert_eq!(
        failure
            .diagnostics()
            .iter()
            .map(MacroDiagnostic::code)
            .collect::<Vec<_>>(),
        vec!["failure-visible"]
    );
    assert!(matches!(
        failure.capability_events(),
        [MacroCapabilityEvent::ClockDenied { mode: Mode::Sound }]
    ));
    assert_eq!(state_root(&initial), initial_root);

    let cancel_at_publication =
        |checkpoint| matches!(checkpoint, MacroTxnCheckpoint::BeforePublication { .. });
    let cancelled = run_macro_transaction(
        MacroTxnConfig::new(
            identity("cancelled", Mode::Sound),
            &initial,
            &capabilities,
            MacroTxnBudget::generous(),
            Some(&cancel_at_publication),
        ),
        |txn| {
            txn.set_environment(name("cancelled"), MacroValue::from_text("private"))?;
            Ok(())
        },
    );
    assert!(matches!(cancelled.status(), Outcome::Inconclusive(_)));
    assert_eq!(cancelled.initial_state().digest().to_hex(), initial_root);

    let exhausted = run_macro_transaction(
        MacroTxnConfig::new(
            identity("resource", Mode::Sound),
            &initial,
            &capabilities,
            MacroTxnBudget { max_operations: 0 },
            None,
        ),
        |txn| {
            txn.read_environment(&name("present"))?;
            Ok(())
        },
    );
    assert!(matches!(exhausted.status(), Outcome::Inconclusive(_)));
    assert_eq!(exhausted.initial_state().digest().to_hex(), initial_root);

    let faulted: MacroRunReport<()> = run_macro_transaction(
        MacroTxnConfig::new(
            identity("internal-fault", Mode::Sound),
            &initial,
            &capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            txn.set_environment(name("fault"), MacroValue::from_text("private"))?;
            Err(MacroTxnAbort::InternalFault(InternalFault::new(
                "FLN-W4-MACRO-TXN-E2E",
                "deliberate no-mock nonpublication witness",
            )))
        },
    );
    assert!(matches!(faulted.status(), Outcome::InternalFault(_)));
    assert_eq!(faulted.initial_state().digest().to_hex(), initial_root);

    let (recovery_initial, recovery_capabilities, _, recovery_product) = positive_product();
    let mut recovery_state = recovery_initial;
    let recovery_published = recovery_product
        .publish(&mut recovery_state, &recovery_capabilities)
        .expect("clean retry publishes after every negative path");
    assert_eq!(recovery_published.value(), "expanded:old:false");
    assert_eq!(state_root(&recovery_state), positive_root);

    let expansion_state = baseline();
    let expansion_capabilities = baseline_capabilities();
    let positive_expansion = complete_product(expand_quotation_transactional(
        positive_expansion_input(),
        &expansion_state,
        &expansion_capabilities,
        MacroTxnBudget::generous(),
        MacroExpansionBudget::generous(),
        None,
        None,
    ));
    assert_eq!(state_root(&expansion_state), initial_root);
    let mut published_expansion_state = expansion_state.clone();
    let published_expansion = positive_expansion
        .publish(&mut published_expansion_state, &expansion_capabilities)
        .expect("actual quotation expansion publishes through the transaction seam");
    let quotation_root = expansion_root(published_expansion.value());
    assert_eq!(state_root(&published_expansion_state), initial_root);

    let refused_expansion = expand_quotation_transactional(
        failing_expansion_input(),
        &expansion_state,
        &expansion_capabilities,
        MacroTxnBudget::generous(),
        MacroExpansionBudget::generous(),
        None,
        None,
    );
    assert!(matches!(
        refused_expansion.status(),
        Outcome::Complete(Err(failure))
            if matches!(
                failure.error(),
                MacroTxnError::Expansion(MacroExpansionError::UnexpectedSplice { .. })
            )
    ));
    assert_eq!(state_root(&expansion_state), initial_root);

    let recovered_expansion = complete_product(expand_quotation_transactional(
        positive_expansion_input(),
        &expansion_state,
        &expansion_capabilities,
        MacroTxnBudget::generous(),
        MacroExpansionBudget::generous(),
        None,
        None,
    ));
    let mut recovered_expansion_state = expansion_state.clone();
    let recovered_expansion = recovered_expansion
        .publish(&mut recovered_expansion_state, &expansion_capabilities)
        .expect("actual quotation retry publishes");
    let quotation_recovery_root = expansion_root(recovered_expansion.value());
    assert_eq!(quotation_recovery_root, quotation_root);
    assert_eq!(state_root(&recovered_expansion_state), initial_root);

    let mut thread_roots = Vec::new();
    let mut productive_runs = 0usize;
    for worker_count in [1usize, 8, 32] {
        let handles = (0..worker_count)
            .map(|_| {
                std::thread::spawn(|| {
                    let (initial, capabilities, _, product) = positive_product();
                    let mut state = initial;
                    let published = product
                        .publish(&mut state, &capabilities)
                        .expect("productive worker publishes");
                    assert_eq!(published.value(), "expanded:old:false");
                    state_root(&state)
                })
            })
            .collect::<Vec<_>>();
        let roots = handles
            .into_iter()
            .map(|handle| handle.join().expect("productive worker completes"))
            .collect::<Vec<_>>();
        productive_runs += roots.len();
        assert_eq!(roots.len(), worker_count);
        assert!(roots.iter().all(|root| root == &positive_root));
        thread_roots.push(roots[0].clone());
    }
    assert_eq!(productive_runs, 41);
    assert!(thread_roots.iter().all(|root| root == &positive_root));

    let semantic_rows = vec![
        json_object(vec![
            ("cacheability", json_text("cacheable")),
            ("capability_event_count", "1".to_string()),
            (
                "diagnostic_codes",
                json_string_array(&["nested-visible", "committed"]),
            ),
            ("effect_count", "4".to_string()),
            ("final_state", json_text(&positive_root)),
            ("initial_state", json_text(&initial_root)),
            ("published", "true".to_string()),
            ("read_count", "9".to_string()),
            ("scenario", json_text("positive")),
            ("schema", json_text(SEMANTIC_SCHEMA)),
            ("sequence", "0".to_string()),
            ("state_unchanged_before_publish", "true".to_string()),
            ("status", json_text("complete")),
            ("value", json_text("expanded:old:false")),
        ]),
        json_object(vec![
            ("cached_equals_fresh", "true".to_string()),
            ("cached_final_state", json_text(&positive_root)),
            ("collision_lookup", json_text("collision_miss")),
            ("exact_lookup", json_text("hit")),
            ("fresh_final_state", json_text(&positive_root)),
            ("published", "true".to_string()),
            ("scenario", json_text("memoization")),
            ("schema", json_text(SEMANTIC_SCHEMA)),
            ("sequence", "1".to_string()),
            ("stale_file", json_text("stale_read_miss")),
            ("stale_iteration", json_text("stale_read_miss")),
            ("stale_negative", json_text("stale_read_miss")),
            ("stale_option", json_text("stale_read_miss")),
        ]),
        json_object(vec![
            ("faithful_clock_cacheability", json_text("uncacheable")),
            ("published", "false".to_string()),
            ("scenario", json_text("opaque_reads")),
            ("schema", json_text(SEMANTIC_SCHEMA)),
            ("sequence", "2".to_string()),
            ("sound_clock_outcome", json_text("rejected")),
            ("unknown_cacheability", json_text("uncacheable")),
            ("unknown_memo_admission", json_text("refused")),
        ]),
        json_object(vec![
            ("capability_event", json_text("clock_denied_sound")),
            ("diagnostic_codes", json_string_array(&["failure-visible"])),
            ("error", json_text("capability_denied_clock_sound")),
            ("published", "false".to_string()),
            ("scenario", json_text("failure")),
            ("schema", json_text(SEMANTIC_SCHEMA)),
            ("sequence", "3".to_string()),
            ("state_unchanged", "true".to_string()),
            ("status", json_text("rejected")),
        ]),
        json_object(vec![
            ("published", "false".to_string()),
            ("scenario", json_text("cancellation")),
            ("schema", json_text(SEMANTIC_SCHEMA)),
            ("sequence", "4".to_string()),
            ("state_unchanged", "true".to_string()),
            ("status", json_text("inconclusive")),
        ]),
        json_object(vec![
            ("published", "false".to_string()),
            ("scenario", json_text("resource")),
            ("schema", json_text(SEMANTIC_SCHEMA)),
            ("sequence", "5".to_string()),
            ("state_unchanged", "true".to_string()),
            ("status", json_text("inconclusive")),
        ]),
        json_object(vec![
            ("published", "false".to_string()),
            ("scenario", json_text("internal_fault")),
            ("schema", json_text(SEMANTIC_SCHEMA)),
            ("sequence", "6".to_string()),
            ("state_unchanged", "true".to_string()),
            ("status", json_text("internal_fault")),
        ]),
        json_object(vec![
            ("final_state", json_text(&positive_root)),
            ("matches_positive", "true".to_string()),
            ("published", "true".to_string()),
            ("scenario", json_text("recovery")),
            ("schema", json_text(SEMANTIC_SCHEMA)),
            ("sequence", "7".to_string()),
            ("status", json_text("complete")),
            ("value", json_text("expanded:old:false")),
        ]),
        json_object(vec![
            ("failure_status", json_text("rejected")),
            ("positive_root", json_text(&quotation_root)),
            ("positive_status", json_text("complete")),
            ("recovery_root", json_text(&quotation_recovery_root)),
            ("recovery_status", json_text("complete")),
            ("scenario", json_text("quotation_seam")),
            ("schema", json_text(SEMANTIC_SCHEMA)),
            ("sequence", "8".to_string()),
            ("state_unchanged_before_publication", "true".to_string()),
        ]),
        json_object(vec![
            ("productive_runs", productive_runs.to_string()),
            ("published", "true".to_string()),
            ("scenario", json_text("thread_matrix")),
            ("schema", json_text(SEMANTIC_SCHEMA)),
            ("semantic_root", json_text(&positive_root)),
            ("sequence", "9".to_string()),
            ("status", json_text("complete")),
            ("thread_counts", json_usize_array(&[1, 8, 32])),
        ]),
    ];

    if let Some(artifact_dir) = std::env::var_os("FLN_MACRO_TXN_E2E_ART_DIR") {
        let artifact_dir = Path::new(&artifact_dir);
        assert!(
            artifact_dir.is_dir(),
            "artifact directory must already exist"
        );
        let run_id =
            std::env::var("FLN_MACRO_TXN_E2E_RUN_ID").expect("run id accompanies artifact path");
        write_evidence(artifact_dir, &semantic_rows, &run_id, product.operations());
    }

    println!(
        "macro-txn-no-mock status=pass semantic_root={} quotation_root={} productive_runs={}",
        positive_root, quotation_root, productive_runs
    );
}
