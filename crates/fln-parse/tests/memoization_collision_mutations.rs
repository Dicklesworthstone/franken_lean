//! Collision, omitted-read, and stale-cache mutation cells.

#![forbid(unsafe_code)]

use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::domain::{Digest, Domain, hash};
use fln_parse::macro_expand::{
    HygienePolicy, MacroExpansionBudget, MacroExpansionCoordinates, MacroExpansionInput,
    QuotationContext, QuotationTemplate,
};
use fln_parse::macro_txn::{
    CanonicalPath, MacroCapabilities, MacroInvocationIdentity, MacroMemo, MacroMemoLookup,
    MacroReadSet, MacroState, MacroTxnBudget, MacroTxnConfig, MacroValue,
    expand_quotation_transactional, run_macro_transaction, validate_read_set_perturbation,
};
use fln_parse::registry::GrammarEpoch;
use fln_syntax::hygiene::{ExpansionOrigin, ExpansionPath};
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};
use fln_syntax::tree::Syntax;

fn name(value: &str) -> Name {
    Name::from_components(["Main", value])
}

fn epoch() -> GrammarEpoch {
    GrammarEpoch::from_parts(41, Digest([0x41; 32]))
}

fn decoded_identity(digest: Digest, row: &[u8]) -> MacroInvocationIdentity {
    MacroInvocationIdentity::from_decoded(digest, row.to_vec(), epoch(), Mode::Sound)
}

fn product(
    identity: MacroInvocationIdentity,
    state: &MacroState,
    capabilities: &MacroCapabilities,
) -> fln_parse::macro_txn::MacroTxnProduct<String> {
    let report = run_macro_transaction(
        MacroTxnConfig::new(
            identity,
            state,
            capabilities,
            MacroTxnBudget::generous(),
            None,
        ),
        |txn| {
            let input = txn
                .read_environment(&name("input"))?
                .unwrap_or_else(|| MacroValue::from_text("absent"));
            let file = txn
                .read_file(&CanonicalPath::new("/fixture/config").expect("canonical path"))?
                .unwrap_or_else(|| MacroValue::from_text("no-file"));
            let output = format!(
                "{}:{}",
                String::from_utf8_lossy(input.as_bytes()),
                String::from_utf8_lossy(file.as_bytes())
            );
            txn.set_environment(name("output"), MacroValue::from_text(output.clone()))?;
            Ok(output)
        },
    );
    match report.into_status() {
        Outcome::Complete(Ok(product)) => product,
        other => panic!("memo candidate did not complete: {other:?}"),
    }
}

#[test]
fn complete_row_equality_kills_collision_and_omission_mutants() {
    let collision_digest = Digest([0xCC; 32]);
    let identity_a = decoded_identity(collision_digest, b"complete-row-a");
    let identity_b = decoded_identity(collision_digest, b"complete-row-b");
    assert_eq!(identity_a.digest(), identity_b.digest());
    assert_ne!(identity_a.canonical(), identity_b.canonical());

    let mut state = MacroState::new();
    state.insert_environment(name("input"), MacroValue::from_text("alpha"));
    let path = CanonicalPath::new("/fixture/config").expect("canonical path");
    let mut capabilities = MacroCapabilities::new();
    capabilities.insert_file(path.clone(), b"one".to_vec());

    let candidate = product(identity_a.clone(), &state, &capabilities);
    let mut memo = MacroMemo::new();
    memo.insert(candidate.clone())
        .expect("a complete candidate is cacheable");
    assert!(matches!(
        memo.lookup(&identity_a, &state, &capabilities),
        MacroMemoLookup::Hit(_)
    ));
    assert!(matches!(
        memo.lookup(&identity_b, &state, &capabilities),
        MacroMemoLookup::CollisionMiss
    ));
    assert_eq!(
        memo.len(),
        1,
        "the digest-only mutant would report a hit for row b here"
    );

    let mut negative_changed = state.clone();
    negative_changed.remove_environment(&name("input"));
    assert!(matches!(
        memo.lookup(&identity_a, &negative_changed, &capabilities),
        MacroMemoLookup::StaleReadMiss
    ));
    let mut content_changed = capabilities.clone();
    content_changed.insert_file(path, b"two".to_vec());
    assert!(matches!(
        memo.lookup(&identity_a, &state, &content_changed),
        MacroMemoLookup::StaleReadMiss
    ));

    let omitted_reads = MacroReadSet::new();
    assert!(
        validate_read_set_perturbation(
            &omitted_reads,
            &negative_changed,
            &capabilities,
            hash(Domain::Fixture, b"alpha:one"),
            hash(Domain::Fixture, b"absent:one"),
        )
        .is_err(),
        "an omission mutant must not certify a changed fresh product"
    );

    let cached = match memo.lookup(&identity_a, &state, &capabilities) {
        MacroMemoLookup::Hit(product) => product.clone(),
        _ => panic!("exact candidate must hit"),
    };
    let fresh = product(identity_a, &state, &capabilities);
    let mut cached_state = state.clone();
    let mut fresh_state = state.clone();
    let cached = cached
        .publish(&mut cached_state, &capabilities)
        .expect("cached read set remains current");
    let fresh = fresh
        .publish(&mut fresh_state, &capabilities)
        .expect("fresh read set remains current");
    assert_eq!(cached.value(), fresh.value());
    assert_eq!(cached.effects(), fresh.effects());
    assert_eq!(cached.diagnostics(), fresh.diagnostics());
    assert_eq!(cached.capability_events(), fresh.capability_events());
    assert_eq!(cached_state, fresh_state);
    assert_eq!(cached.final_state(), fresh.final_state());
}

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(BytePos(start), BytePos(end)).expect("forward span")
}

fn expansion_input(mode: Mode, scope: u64, atom: &str) -> MacroExpansionInput {
    MacroExpansionInput {
        coordinates: MacroExpansionCoordinates {
            grammar_epoch: epoch(),
            mode,
            expansion_path: ExpansionPath::root(ExpansionOrigin::new(name("Module"), 2), 3),
        },
        quotation: QuotationContext {
            name: name("Context"),
            macro_scope: scope,
            call_site: Some(span(10, 20)),
            canonical: true,
            hygiene: HygienePolicy::Enabled,
        },
        template: QuotationTemplate::Literal(Syntax::atom(
            SourceInfo::Synthetic {
                pos: BytePos(1),
                end_pos: BytePos(2),
                canonical: true,
            },
            atom,
        )),
    }
}

#[test]
fn the_real_expansion_identity_binds_mode_scope_and_syntax_before_publication() {
    let faithful =
        MacroInvocationIdentity::from_expansion_input(&expansion_input(Mode::Faithful, 7, "x"))
            .expect("bounded identity");
    let sound =
        MacroInvocationIdentity::from_expansion_input(&expansion_input(Mode::Sound, 7, "x"))
            .expect("bounded identity");
    let other_scope =
        MacroInvocationIdentity::from_expansion_input(&expansion_input(Mode::Faithful, 8, "x"))
            .expect("bounded identity");
    let other_syntax =
        MacroInvocationIdentity::from_expansion_input(&expansion_input(Mode::Faithful, 7, "y"))
            .expect("bounded identity");
    assert_ne!(faithful, sound);
    assert_ne!(faithful, other_scope);
    assert_ne!(faithful, other_syntax);

    let mut state = MacroState::new();
    let original = state.clone();
    let capabilities = MacroCapabilities::new();
    let report = expand_quotation_transactional(
        expansion_input(Mode::Faithful, 7, "x"),
        &state,
        &capabilities,
        MacroTxnBudget::generous(),
        MacroExpansionBudget::generous(),
        None,
        None,
    );
    assert_eq!(state, original);
    let product = match report.into_status() {
        Outcome::Complete(Ok(product)) => product,
        other => panic!("transactional quotation did not complete: {other:?}"),
    };
    let published = product
        .publish(&mut state, &capabilities)
        .expect("unchanged empty state admits the quotation");
    assert_eq!(
        published.value().syntax(),
        &Syntax::atom(
            SourceInfo::Synthetic {
                pos: BytePos(10),
                end_pos: BytePos(20),
                canonical: true,
            },
            "x",
        )
    );
    assert_eq!(
        state, original,
        "a read-only quotation publishes no state delta"
    );
}
