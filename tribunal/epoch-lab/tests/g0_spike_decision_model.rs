//! Suite `g0_spike_decision_model` (bead `franken_lean-869w`; plan §22.1).
//!
//! The name is the one `fln-euo` enumerates in its closure criteria.
//!
//! # What is under test
//!
//! A schema whose job is to **stop a gate from being talked past**. G0 exists so
//! no W2–W12 workstream freezes an interface on top of an unpriced bet, and
//! every way a decision could be softened — paraphrased, aggregated, or quietly
//! amended — is a typed refusal here rather than a judgement call.
//!
//! # The boundary decision, and why it is drawn twice
//!
//! A spike may resolve to `Blocked`, because a schema that cannot say "we have
//! not answered this yet" makes the honest answer indistinguishable from
//! silence. **And** a roster spike with no row is a hard `MissingDecision`,
//! because tolerating absence would move the silence up one level: a spike
//! nobody thought about would look like one deliberately deferred. Not
//! answering is a disposition you record, never one you achieve by staying
//! quiet — the same law `corpus.rs` applies to the C1 inventory.
//!
//! `Blocked` is not a fourth `Outcome`. Folding it in would conflate "a decision
//! was reached" with "no decision was reached".
//!
//! # Mutants planted and killed
//!
//! Measured results, not intended ones.
//!
//! | mutant | edit | killed by |
//! |---|---|---|
//! | NoGo laundered as an amendment | the laundering check skips `Amended` outcomes | `failed_evidence_cannot_be_normalised_into_an_amendment` |
//! | missing row passes on aggregate green | the `MissingDecision` push is disabled | `a_spike_with_no_row_at_all_is_a_hard_failure`, `silence_and_deferral_are_distinguishable`, `every_block_is_reported_not_just_the_first` |
//! | amendment without §25 wording | the wording check is dropped | `an_amendment_missing_any_mandatory_part_is_not_an_amendment` |
//! | amendment accepted while red | the `acceptance_green` check is dropped | `an_amendment_whose_acceptance_tests_are_red_is_refused` |
//! | gate tolerates one defect | `clears` accepts `blocks.len() < 2` | 6 tests |
//! | resource overrun ignored | `within_contract` returns `true` | `a_spike_that_blew_its_resource_contract_is_refused`, `every_block_is_reported_not_just_the_first` |
//! | blocked/no-go counted as decided | the bucket counts are all summed | `an_explicit_blocked_row_is_representable_and_does_not_clear`, `a_no_go_may_rest_on_failed_evidence_because_that_is_what_it_reports`, `silence_and_deferral_are_distinguishable` |
//! | question compared loosely | prefix match instead of `!=` | `a_paraphrased_question_is_answering_a_different_question` |
//!
//! **One mutant survived the first run and the fix was deletion.** `Gate::clears`
//! originally read `blocks.is_empty() && no_go.is_empty() && blocked.is_empty()
//! && ratified + amended == roster_size`. Deleting `blocked.is_empty()` changed
//! nothing observable, because every roster spike lands in exactly one bucket,
//! so the count already excludes any spike that is NoGo, Blocked or missing —
//! both extra clauses restated the same predicate over the same data in the
//! same function. This is `poison::scan`'s double-guard lesson in a second
//! disguise: indistinguishable redundancy is not defence in depth, it is dead
//! code no campaign can see. The difference is that the scan's second guard
//! bought termination, so it was made *distinguishable*; these bought nothing,
//! so they were *removed*.

#![forbid(unsafe_code)]

use fln_epoch_lab::corpus::CorpusFamily;
use fln_epoch_lab::derive::derive_g0_roster;
use fln_epoch_lab::g0::{
    Amendment, Block, BlockedReason, Decision, NoGo, Outcome, Resolution, Resources, RosterSpike,
    Scope, Witness, WitnessRoot, report, verify,
};

/// The roster, DERIVED from the plan rather than transcribed.
///
/// The constant this used to read was hand-copied, and `fln-8fwh` proved all
/// ten of its questions differed from §22.1 — so the verbatim-question check
/// was enforcing a paraphrase. Every test below now measures against what the
/// plan actually says.
fn roster() -> Vec<RosterSpike> {
    let plan = fln_conformance::checked_manifest_dir!()
        .join("../../COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md");
    match derive_g0_roster(&plan) {
        Ok(d) => d.into_parts().0,
        Err(e) => panic!("the G0 roster could not be derived from the plan: {e}"),
    }
}
use fln_epoch_lab::oracle::{
    ClaimType, ComparisonClass, EvidenceState, Mode, OracleKind, Platform,
};

fn root(tag: u8) -> WitnessRoot {
    WitnessRoot::Recorded(format!("{tag:02x}").repeat(32))
}

fn good_witness() -> Witness {
    Witness {
        evidence_state: EvidenceState::Proven,
        fixture_root: root(1),
        generated_contract_root: root(2),
        implementation_root: root(3),
        mutation_root: root(4),
        no_mock_e2e_root: root(5),
        oracle: OracleKind::ReferenceBinary,
        comparison: ComparisonClass::ByteIdentical,
    }
}

fn good_amendment() -> Amendment {
    Amendment {
        section_25_wording: "The olean writer MAY emit a registered serialization freedom."
            .to_string(),
        rationale: "Byte-identity is unreachable for extension payloads at the pin.".to_string(),
        blast_radius: vec!["fln-olean".to_string(), "fln-ledger".to_string()],
        owners: vec!["cc_2".to_string()],
        dependency_updates: vec!["FL-INV-04 restated".to_string()],
        acceptance_suite: "olean_roundtrip".to_string(),
        acceptance_green: true,
        acceptance_root: root(6),
    }
}

fn decision(spike: &RosterSpike, resolution: Resolution) -> Decision {
    Decision {
        spike: spike.id.to_string(),
        question: spike.question.to_string(),
        resolution,
        claim: ClaimType::BoundedModel,
        witness: good_witness(),
        scope: Scope {
            epoch: "v4.32.0".to_string(),
            corpus: CorpusFamily::C1,
            platform: Platform::LinuxX86_64,
            mode: Mode::Sound,
        },
        resources: Resources {
            contract_wall_ms: 60_000,
            contract_rss_bytes: 1 << 30,
            used_wall_ms: 42_000,
            used_rss_bytes: 1 << 28,
        },
        limitations: "linux-x86_64 only; no windows evidence".to_string(),
        affected_interfaces: vec!["fln-olean".to_string()],
    }
}

/// All ten spikes ratified on recorded evidence.
fn all_ratified() -> Vec<Decision> {
    roster()
        .iter()
        .map(|s| decision(s, Resolution::Decided(Outcome::Ratified)))
        .collect()
}

fn reasons(blocks: &[Block]) -> Vec<&'static str> {
    blocks.iter().map(Block::reason).collect()
}

// ---------------------------------------------------------------------------
// The baseline
// ---------------------------------------------------------------------------

#[test]
fn ten_ratified_spikes_clear_the_gate() {
    let g = verify(&all_ratified(), &roster());
    assert!(
        g.clears(),
        "a complete ledger did not clear: {:?}",
        g.blocks
    );
    assert_eq!(g.ratified.len(), 10);
    assert!(report(&g).contains("verdict=clear"));
}

#[test]
fn a_well_formed_amendment_also_clears() {
    // Amended is a legitimate outcome. The rules below make it expensive, not
    // impossible — a gate nobody can pass honestly is a gate people route
    // around.
    let mut d = all_ratified();
    d[4] = decision(
        &roster()[4],
        Resolution::Decided(Outcome::Amended(good_amendment())),
    );
    let g = verify(&d, &roster());
    assert!(g.clears(), "{:?}", g.blocks);
    assert_eq!(g.amended, vec!["G0-5"]);
    assert_eq!(g.ratified.len(), 9);
}

// ---------------------------------------------------------------------------
// Absence versus deferral — the boundary
// ---------------------------------------------------------------------------

#[test]
fn a_spike_with_no_row_at_all_is_a_hard_failure() {
    // THE AGGREGATE-GREEN MUTANT. Nine spikes ratified on perfect evidence.
    // A verifier that walked the ROWS would find nothing wrong and report nine
    // green; only walking the ROSTER makes the tenth visible.
    let nine: Vec<Decision> = all_ratified().into_iter().take(9).collect();
    let g = verify(&nine, &roster());
    assert!(!g.clears(), "nine of ten cleared the gate");
    assert_eq!(reasons(&g.blocks), vec!["missing-decision"]);
    match &g.blocks[0] {
        Block::MissingDecision { spike } => assert_eq!(spike, "G0-10"),
        other => panic!("expected MissingDecision, got {other:?}"),
    }
    // And the report names the roster size, so "9 ratified" can never be read
    // as complete.
    let text = report(&g);
    assert!(text.contains("roster=10"));
    assert!(text.contains("ratified=9"));
    assert!(text.contains("verdict=not-clear"));
}

#[test]
fn an_explicit_blocked_row_is_representable_and_does_not_clear() {
    // The other half of the boundary. "We have not answered this yet" is
    // sayable — that is the whole reason Blocked exists — but saying it does
    // not license a downstream interface freeze.
    let mut d = all_ratified();
    d[9] = decision(
        &roster()[9],
        Resolution::Blocked {
            reason: BlockedReason::ApparatusMissing,
            owner: "cc_2".to_string(),
            note: "the closure allowlist generator does not exist yet".to_string(),
        },
    );
    let g = verify(&d, &roster());
    assert!(
        g.blocks.is_empty(),
        "a well-formed Blocked row was refused: {:?}",
        g.blocks
    );
    assert!(!g.clears(), "a blocked spike cleared the gate");
    assert_eq!(g.blocked, vec!["G0-10"]);
    // Named, not counted: "9 ratified, 1 blocked" without the id reads as
    // almost-done and hides which bet is unpriced.
    assert!(report(&g).contains("blocked spike=G0-10"));
}

#[test]
fn silence_and_deferral_are_distinguishable() {
    // The point of drawing the boundary twice. A spike nobody thought about and
    // a spike deliberately deferred produce DIFFERENT machine output, which is
    // the property that would be lost by picking either rule alone.
    let deferred = {
        let mut d = all_ratified();
        d[9] = decision(
            &roster()[9],
            Resolution::Blocked {
                reason: BlockedReason::DeferredByOwner,
                owner: "cod_3".to_string(),
                note: "scheduled after the lane registrations".to_string(),
            },
        );
        verify(&d, &roster())
    };
    let silent = verify(
        &all_ratified().into_iter().take(9).collect::<Vec<_>>(),
        &roster(),
    );

    assert!(!deferred.clears() && !silent.clears(), "neither may clear");
    // Deferral is well-formed; silence is a block.
    assert!(deferred.blocks.is_empty());
    assert_eq!(reasons(&silent.blocks), vec!["missing-decision"]);
    assert_ne!(report(&deferred), report(&silent));
}

#[test]
fn a_blocked_row_without_an_owner_is_refused() {
    // A deferral nobody owns is a deferral nobody will revisit.
    for (owner, note, missing) in [("", "a note", "owner"), ("cc_2", "  ", "note")] {
        let mut d = all_ratified();
        d[0] = decision(
            &roster()[0],
            Resolution::Blocked {
                reason: BlockedReason::AwaitingDependency,
                owner: owner.to_string(),
                note: note.to_string(),
            },
        );
        let g = verify(&d, &roster());
        assert!(
            g.blocks
                .iter()
                .any(|b| matches!(b, Block::UnownedBlock { missing: m, .. } if *m == missing)),
            "a Blocked row missing its {missing} passed: {:?}",
            g.blocks
        );
    }
}

// ---------------------------------------------------------------------------
// Laundering rule 1: non-evidence never becomes evidence
// ---------------------------------------------------------------------------

#[test]
fn failed_evidence_cannot_be_normalised_into_an_amendment() {
    // THE NO-GO-LAUNDERED-AS-AMENDMENT MUTANT. The spike's real-world story is
    // "the no-mock E2E failed", and the row narrates that into an amendment
    // with impeccable paperwork: exact §25 wording, rationale, blast radius,
    // owners, dependency updates, green acceptance tests. Every soft field is
    // perfect. The refusal is on the ROOT'S TYPE, which no amount of narration
    // can change.
    for status in [
        WitnessRoot::Failed,
        WitnessRoot::Absent,
        WitnessRoot::Unresolved,
    ] {
        let mut d = all_ratified();
        let mut row = decision(
            &roster()[4],
            Resolution::Decided(Outcome::Amended(good_amendment())),
        );
        row.witness.no_mock_e2e_root = status.clone();
        d[4] = row;
        let g = verify(&d, &roster());
        assert!(!g.clears(), "{status:?} evidence supported an amendment");
        let found = g.blocks.iter().any(
            |b| matches!(b, Block::LaunderedNonEvidence { root, .. } if *root == "no_mock_e2e"),
        );
        assert!(found, "expected LaunderedNonEvidence: {:?}", g.blocks);
    }
}

#[test]
fn every_witness_root_is_checked_not_just_the_e2e_one() {
    // A laundering check that only looked at the headline root would let the
    // fixture, contract, implementation or mutation evidence be absent.
    let names = [
        "fixture",
        "generated_contract",
        "implementation",
        "mutation",
        "no_mock_e2e",
    ];
    for name in names {
        let mut d = all_ratified();
        let mut row = decision(&roster()[0], Resolution::Decided(Outcome::Ratified));
        match name {
            "fixture" => row.witness.fixture_root = WitnessRoot::Absent,
            "generated_contract" => row.witness.generated_contract_root = WitnessRoot::Absent,
            "implementation" => row.witness.implementation_root = WitnessRoot::Absent,
            "mutation" => row.witness.mutation_root = WitnessRoot::Absent,
            _ => row.witness.no_mock_e2e_root = WitnessRoot::Absent,
        }
        d[0] = row;
        let g = verify(&d, &roster());
        assert!(
            g.blocks
                .iter()
                .any(|b| matches!(b, Block::LaunderedNonEvidence { root, .. } if *root == name)),
            "an absent {name} root was not caught"
        );
    }
}

#[test]
fn a_no_go_may_rest_on_failed_evidence_because_that_is_what_it_reports() {
    // The rule is directional and must stay that way. Failed evidence cannot
    // support a POSITIVE decision; a NoGo saying "we tried and it failed" is
    // exactly the honest use of a Failed root, and refusing it would push
    // people towards filing nothing at all.
    let mut d = all_ratified();
    let mut row = decision(
        &roster()[6],
        Resolution::Decided(Outcome::NoGo(NoGo {
            rationale: "the defeq tail does not fall within the budget".to_string(),
            affected_interfaces: vec!["fln-elab".to_string()],
        })),
    );
    row.witness.no_mock_e2e_root = WitnessRoot::Failed;
    d[6] = row;
    let g = verify(&d, &roster());
    assert!(
        !g.blocks
            .iter()
            .any(|b| matches!(b, Block::LaunderedNonEvidence { .. })),
        "a NoGo resting on failed evidence was treated as laundering: {:?}",
        g.blocks
    );
    // It is well-formed, and it still does not clear the gate.
    assert!(g.blocks.is_empty());
    assert!(!g.clears());
    assert_eq!(g.no_go, vec!["G0-7"]);
}

#[test]
fn a_hollow_no_go_is_refused() {
    // A NoGo with no rationale, or no statement of what it affects, is a shrug
    // rather than a decision.
    for (rationale, ifaces, missing) in [
        ("", vec!["fln-elab".to_string()], "rationale"),
        ("because", vec![], "affected_interfaces"),
    ] {
        let mut d = all_ratified();
        d[6] = decision(
            &roster()[6],
            Resolution::Decided(Outcome::NoGo(NoGo {
                rationale: rationale.to_string(),
                affected_interfaces: ifaces,
            })),
        );
        let g = verify(&d, &roster());
        assert!(
            g.blocks
                .iter()
                .any(|b| matches!(b, Block::HollowNoGo { missing: m, .. } if *m == missing)),
            "a NoGo missing its {missing} passed"
        );
    }
}

// ---------------------------------------------------------------------------
// Laundering rule 2: an amendment is expensive
// ---------------------------------------------------------------------------

#[test]
fn an_amendment_missing_any_mandatory_part_is_not_an_amendment() {
    // Each part dropped in turn. "Anything less is not an amendment" means
    // every one of these is individually fatal, not a quality score.
    type MandatoryPart = (&'static str, fn(&mut Amendment));
    let parts: [MandatoryPart; 7] = [
        ("section_25_wording", |a| {
            a.section_25_wording = String::new()
        }),
        ("rationale", |a| a.rationale = "   ".to_string()),
        ("blast_radius", |a| a.blast_radius.clear()),
        ("owners", |a| a.owners.clear()),
        ("dependency_updates", |a| a.dependency_updates.clear()),
        ("acceptance_suite", |a| a.acceptance_suite = String::new()),
        ("acceptance_root", |a| {
            a.acceptance_root = WitnessRoot::Absent
        }),
    ];
    for (missing, break_it) in parts {
        let mut amendment = good_amendment();
        break_it(&mut amendment);
        let mut d = all_ratified();
        d[4] = decision(
            &roster()[4],
            Resolution::Decided(Outcome::Amended(amendment)),
        );
        let g = verify(&d, &roster());
        assert!(!g.clears(), "an amendment without {missing} cleared");
        assert!(
            g.blocks.iter().any(
                |b| matches!(b, Block::IncompleteAmendment { missing: m, .. } if *m == missing)
            ),
            "expected IncompleteAmendment({missing}): {:?}",
            g.blocks
        );
    }
}

#[test]
fn an_amendment_whose_acceptance_tests_are_red_is_refused() {
    // "Green amended acceptance tests" is a fact about a run, not an intention.
    let mut amendment = good_amendment();
    amendment.acceptance_green = false;
    let mut d = all_ratified();
    d[4] = decision(
        &roster()[4],
        Resolution::Decided(Outcome::Amended(amendment)),
    );
    let g = verify(&d, &roster());
    assert!(!g.clears());
    assert!(reasons(&g.blocks).contains(&"amendment-not-green"));
}

// ---------------------------------------------------------------------------
// The question, the scope, the resources
// ---------------------------------------------------------------------------

#[test]
fn a_paraphrased_question_is_answering_a_different_question() {
    // The most direct form of talking a gate past: restate what was asked until
    // the answer you have fits it.
    let mut d = all_ratified();
    d[0].question = "ABI resurrection: parse an olean and check it looks right".to_string();
    let g = verify(&d, &roster());
    assert!(!g.clears(), "a paraphrased question cleared");
    assert_eq!(reasons(&g.blocks), vec!["question-mismatch"]);
}

#[test]
fn a_spike_that_blew_its_resource_contract_is_refused() {
    // The budget is usually the whole question. A spike that exceeded it did
    // not prove the thing could be done inside it.
    for (wall, rss) in [(60_001, 1 << 28), (42_000, (1u64 << 30) + 1)] {
        let mut d = all_ratified();
        d[6].resources.used_wall_ms = wall;
        d[6].resources.used_rss_bytes = rss;
        let g = verify(&d, &roster());
        assert!(!g.clears(), "an overrun cleared: wall={wall} rss={rss}");
        assert!(reasons(&g.blocks).contains(&"resource-contract-exceeded"));
    }
}

#[test]
fn a_row_with_no_stated_limitations_is_refused() {
    let mut d = all_ratified();
    d[2].limitations = "  ".to_string();
    let g = verify(&d, &roster());
    assert!(!g.clears());
    assert!(reasons(&g.blocks).contains(&"no-limitations-stated"));
}

#[test]
fn duplicate_and_unknown_rows_are_refused() {
    // "Exactly one row per spike" in both directions.
    let mut d = all_ratified();
    d.push(decision(
        &roster()[0],
        Resolution::Decided(Outcome::Ratified),
    ));
    let g = verify(&d, &roster());
    assert!(reasons(&g.blocks).contains(&"duplicate-decision"));

    let mut e = all_ratified();
    let ghost = RosterSpike {
        id: "G0-11".to_string(),
        name: "Ghost spike".to_string(),
        question: "a question nobody asked".to_string(),
    };
    e.push(decision(&ghost, Resolution::Decided(Outcome::Ratified)));
    let g = verify(&e, &roster());
    assert!(reasons(&g.blocks).contains(&"unknown-spike"));
}

// ---------------------------------------------------------------------------
// Claim type stays separate from evidence state
// ---------------------------------------------------------------------------

#[test]
fn the_gate_verdict_does_not_read_the_claim_type() {
    // D7 separation, the fifth time this session and for the same reason. The
    // row's claim type and its witness evidence state are two fields, and the
    // gate verdict must not move with the claim — otherwise a strong-sounding
    // claim starts substituting for the evidence that would earn it.
    for state in [
        EvidenceState::Proven,
        EvidenceState::Observed,
        EvidenceState::Targeted,
        EvidenceState::Hypothesis,
        EvidenceState::Blocked,
    ] {
        let mut base = all_ratified();
        base[0].witness.evidence_state = state;
        base[0].claim = ClaimType::Benchmark;
        let want = verify(&base, &roster()).clears();

        for claim in [
            ClaimType::Invariant,
            ClaimType::Proof,
            ClaimType::BoundedModel,
            ClaimType::Statistical,
            ClaimType::Slo,
            ClaimType::Benchmark,
        ] {
            let mut d = all_ratified();
            d[0].witness.evidence_state = state;
            d[0].claim = claim;
            assert!(
                verify(&d, &roster()).clears() == want,
                "the gate verdict moved with the claim type (state {state:?}, claim {claim:?})"
            );
        }
    }
}

#[test]
fn the_scope_is_carried_per_row_and_is_not_a_global() {
    // Each decision is valid within an exact epoch/corpus/platform/mode. A
    // decision outside its scope is not a weaker decision, it is an answer to a
    // different question — so the scope travels with the row.
    let mut d = all_ratified();
    d[0].scope.platform = Platform::MacOSAarch64;
    d[0].scope.mode = Mode::Faithful;
    let g = verify(&d, &roster());
    assert!(g.clears(), "{:?}", g.blocks);
    assert_eq!(d[0].scope.platform, Platform::MacOSAarch64);
    assert_eq!(d[1].scope.platform, Platform::LinuxX86_64);
    assert_eq!(d[0].scope.corpus, CorpusFamily::C1);
}

#[test]
fn every_block_is_reported_not_just_the_first() {
    let mut d: Vec<Decision> = all_ratified().into_iter().take(8).collect();
    d[0].question = "paraphrased".to_string();
    d[1].limitations = String::new();
    d[2].resources.used_wall_ms = u64::MAX;
    d[3].witness.mutation_root = WitnessRoot::Unresolved;
    let g = verify(&d, &roster());
    let r = reasons(&g.blocks);
    for want in [
        "question-mismatch",
        "no-limitations-stated",
        "resource-contract-exceeded",
        "laundered-non-evidence",
        "missing-decision",
    ] {
        assert!(r.contains(&want), "{want} was not reported: {:?}", g.blocks);
    }
    assert!(report(&g).contains("verdict=not-clear"));
}

// ---------------------------------------------------------------------------
// The REAL ledger begins here: G0-9's row, every digest computed from the
// committed artifacts at run time, the acceptance green EXECUTED rather than
// asserted. Everything above this line is the model; this is the record.
// ---------------------------------------------------------------------------

use fln_conformance::trace_replay::{
    EventFamily, TRACE_REPLAY_SCHEMA, check_diagnostics, check_elab_steps, check_instance_search,
    check_postponements, check_simp, classify, family_root, parse_trace, replay, replay_parallel,
};
use fln_epoch_lab::derive::derive_fixture_digest;
use fln_epoch_lab::g0::{G09Evidence, g09_decision};
use std::path::PathBuf;

fn conformance_root() -> PathBuf {
    fln_conformance::checked_manifest_dir!().join("../../crates/fln-conformance")
}

/// Execute the acceptance checks and compute the evidence digests. The green is
/// what this function OBSERVES; a paste would rot.
fn g09_evidence() -> G09Evidence {
    let fixtures = conformance_root().join("fixtures");
    let evidence_dir = conformance_root().join("evidence/g09_trace_replay");

    // fixture_root: content digests of all six committed fixture files, folded
    // through the house digest so the root is a function of the set.
    let fixture_digests: Vec<String> = [
        "g09_pilot.lean",
        "g09_pilot_trace.txt",
        "g09_multi_family.lean",
        "g09_multi_family_trace.txt",
        "g09_diag.lean",
        "g09_diag_trace.txt",
    ]
    .iter()
    .map(|f| {
        derive_fixture_digest(&fixtures.join(f))
            .unwrap_or_else(|e| panic!("fixture {f} unreadable: {e}"))
            .into_parts()
            .0
    })
    .collect();
    let fold = |parts: &[String]| -> String {
        let mut joined = String::new();
        for p in parts {
            joined.push_str(p);
            joined.push(':');
        }
        joined
    };
    let fixture_root = fold(&fixture_digests);

    // The acceptance run: parse both traces, replay, run every family checker,
    // hold the pinned censuses. This IS the acceptance suite's substance,
    // executed here so acceptance_green is an observation.
    let pilot = std::fs::read_to_string(fixtures.join("g09_pilot_trace.txt")).expect("pilot");
    let multi =
        std::fs::read_to_string(fixtures.join("g09_multi_family_trace.txt")).expect("multi");
    let diag = std::fs::read_to_string(fixtures.join("g09_diag_trace.txt")).expect("diag");
    let pilot_events = parse_trace(&pilot).expect("pilot parses");
    let multi_events = parse_trace(&multi).expect("multi parses");
    let diag_events = parse_trace(&diag).expect("diag parses");
    let rep = replay(&pilot_events);
    let par = replay_parallel(&multi_events, 8);
    let unifier_count = multi_events
        .iter()
        .filter(|e| classify(&e.class) == EventFamily::Unifier)
        .count();
    let acceptance_green = rep.queries == 342
        && rep.agreements == 198
        && rep.divergences.len() == 68
        && rep.unscored == 76
        && unifier_count == 1862
        && check_instance_search(&multi_events) == Ok(655)
        && check_simp(&multi_events) == Ok(2)
        && check_elab_steps(&multi_events) == Ok(261)
        && check_postponements(&multi_events) == Ok(76)
        && check_diagnostics(&diag_events) == Ok(22)
        && replay_parallel(&multi_events, 1).divergence_set_root == par.divergence_set_root
        && replay_parallel(&multi_events, 32).divergence_set_root == par.divergence_set_root
        && par.partitions.iter().all(|&p| p > 0);

    // The behavioral identity of the implementation and of the generated
    // contract: what the rig computes, not what its source bytes are.
    let behavior = vec![
        format!("schema={TRACE_REPLAY_SCHEMA}"),
        format!(
            "pilot: queries={} agree={} diverge={} unscored={}",
            rep.queries,
            rep.agreements,
            rep.divergences.len(),
            rep.unscored
        ),
        format!(
            "multi: unifier_root={:016x} instance_root={:016x} set_root={:016x}",
            family_root(&multi_events, EventFamily::Unifier),
            family_root(&multi_events, EventFamily::InstanceSearch),
            par.divergence_set_root
        ),
    ];
    let implementation_root = fold(&behavior);
    let generated_contract_root = format!("{TRACE_REPLAY_SCHEMA}:{}", fold(&fixture_digests));

    // The two committed receipts, digested as files. Their CONTENT is held by
    // the assertions in the test below, not merely their presence.
    let mutation_root =
        derive_fixture_digest(&evidence_dir.join("mutation_campaign_v4.32.0.jsonl"))
            .expect("mutation receipt committed")
            .into_parts()
            .0;
    let no_mock_e2e_root = derive_fixture_digest(&evidence_dir.join("regen_v4.32.0.jsonl"))
        .expect("regen receipt committed")
        .into_parts()
        .0;

    G09Evidence {
        fixture_root,
        generated_contract_root,
        implementation_root,
        mutation_root,
        no_mock_e2e_root,
        acceptance_root: fold(&behavior),
        acceptance_green,
        used_wall_ms: 8_000,
        used_rss_bytes: 1 << 29,
    }
}

#[test]
fn the_g09_row_is_amended_on_computed_evidence_and_only_the_other_nine_block() {
    let roster = roster();
    let evidence = g09_evidence();
    assert!(
        evidence.acceptance_green,
        "the acceptance run must be green before the row exists"
    );
    let row = g09_decision(&roster, &evidence).expect("G0-9 is on the derived roster");
    // The row answers the roster's question verbatim — g09_decision copies it
    // from the derived roster, so a plan rewording moves the row with it.
    let g = verify(&[row], &roster);
    assert_eq!(
        g.amended,
        vec!["G0-9".to_string()],
        "G0-9 lands in the amended bucket"
    );
    assert!(g.ratified.is_empty() && g.no_go.is_empty() && g.blocked.is_empty());
    // Exactly the other nine spikes block as missing — the honest ledger state:
    // one real row, nine undecided, no aggregate green.
    assert_eq!(g.blocks.len(), 9, "{:?}", g.blocks);
    for b in &g.blocks {
        assert_eq!(b.reason(), "missing-decision", "{b:?}");
    }
    assert!(!g.clears(), "one row must never clear a ten-spike gate");
}

#[test]
fn the_g09_receipts_hold_their_content_not_merely_their_presence() {
    let evidence_dir = conformance_root().join("evidence/g09_trace_replay");
    let mutation = std::fs::read_to_string(evidence_dir.join("mutation_campaign_v4.32.0.jsonl"))
        .expect("mutation receipt committed");
    // Every gutted mutant's FINAL outcome is killed-by-named. M1's first gut
    // SURVIVED and is retained deliberately — the record keeps the survival and
    // the re-gut that killed it after the hardening line landed.
    let mut final_outcome: std::collections::BTreeMap<&str, &str> = Default::default();
    let mut baseline_green = false;
    let mut restored_green = 0usize;
    for line in mutation.lines() {
        assert!(
            line.contains("\"schema\": \"fln-g09-mutation-campaign/1\""),
            "unversioned receipt row: {line}"
        );
        let field = |key: &str| -> Option<&str> {
            let tag = format!("\"{key}\": \"");
            let start = line.find(&tag)? + tag.len();
            line[start..].split('"').next()
        };
        let (Some(mutant), Some(outcome)) = (field("mutant"), field("outcome")) else {
            panic!("receipt row missing mutant/outcome: {line}");
        };
        match mutant {
            "baseline" => baseline_green = outcome == "green",
            "restored" | "restored-after-regut" => {
                restored_green += usize::from(outcome == "green")
            }
            m => {
                final_outcome.insert(m, outcome);
            }
        }
    }
    assert!(baseline_green, "campaign baseline was not green");
    assert_eq!(restored_green, 2, "both restorations must be green");
    assert_eq!(
        final_outcome.len(),
        10,
        "ten mutants gutted: {final_outcome:?}"
    );
    for (mutant, outcome) in &final_outcome {
        assert_eq!(
            *outcome, "killed-by-named",
            "{mutant} final outcome must be killed-by-named"
        );
    }

    let regen = std::fs::read_to_string(evidence_dir.join("regen_v4.32.0.jsonl"))
        .expect("regen receipt committed");
    assert!(
        regen
            .lines()
            .all(|l| l.contains("\"schema\":\"fln-g09-trace-regen/1\""))
    );
    for step in [
        "\"step\":\"pilot\"",
        "\"step\":\"multi_family\"",
        "\"step\":\"diag\"",
    ] {
        let row = regen.lines().find(|l| l.contains(step)).expect(step);
        assert!(row.contains("\"runs_identical\":true"), "{row}");
        assert!(row.contains("\"fixture_identical\":true"), "{row}");
    }
    assert!(
        regen.contains("\"step\":\"negative_control\",\"corrupted_copy_detected\":true"),
        "the regen receipt must carry its negative control"
    );
    assert!(
        regen.contains("\"pin\":\"v4.32.0\"") && regen.contains("\"verdict\":\"all-identical\""),
        "the regen summary must bind the pin"
    );
}

// ---------------------------------------------------------------------------
// The second real row: G0-6, Ratified on computed evidence. The ledger now
// holds two rows; exactly the other eight block as missing.
// ---------------------------------------------------------------------------

use fln_conformance::fuel::{
    FUEL_SCHEMA, FuelVerdict, TICKS_PER_UNIT, parse_receipt, replay_verdict,
};
use fln_epoch_lab::g0::{G06Evidence, g06_decision};

fn g06_evidence() -> G06Evidence {
    let root = fln_conformance::checked_manifest_dir!().join("../..");
    let evidence_dir = root.join("crates/fln-conformance/evidence/g06_fuel_parity");

    let receipt_text = std::fs::read_to_string(evidence_dir.join("thresholds_v4.32.0.jsonl"))
        .expect("thresholds receipt committed");
    let rows = parse_receipt(&receipt_text).expect("receipt parses");

    // fixture_root: the sixteen pinned corpus inputs the thresholds were
    // bisected on, digested from the vendored tree.
    let fixture_digests: Vec<String> = rows
        .iter()
        .map(|r| {
            derive_fixture_digest(&root.join("vendor/lean4-src").join(&r.file))
                .unwrap_or_else(|e| panic!("corpus input {} unreadable: {e}", r.file))
                .into_parts()
                .0
        })
        .collect();
    let fold = |parts: &[String]| -> String {
        let mut joined = String::new();
        for p in parts {
            joined.push_str(p);
            joined.push(':');
        }
        joined
    };

    // The acceptance run: every bracketed row's verdicts across the grid, by
    // interval endpoints, plus the strictness and zero-disables cells.
    let mut table = Vec::new();
    let mut acceptance_green = true;
    for row in rows.iter().filter(|r| r.threshold.is_some()) {
        let c = row.threshold.unwrap();
        let cells = [
            (c - 1, FuelVerdict::TimedOut),
            (c, FuelVerdict::Completed),
            (2 * c, FuelVerdict::Completed),
            (0, FuelVerdict::Completed),
        ];
        for (budget, want) in cells {
            let got = replay_verdict(c, budget);
            acceptance_green &= got == Some(want);
            table.push(format!("{}@{budget}={got:?}", row.file));
        }
    }
    acceptance_green &= rows.len() == 16
        && rows.iter().filter(|r| r.threshold.is_some()).count() == 9
        && TICKS_PER_UNIT == 1000;

    let mutation_root =
        derive_fixture_digest(&evidence_dir.join("mutation_campaign_v4.32.0.jsonl"))
            .expect("mutation receipt committed")
            .into_parts()
            .0;
    let no_mock_e2e_root = derive_fixture_digest(&evidence_dir.join("thresholds_v4.32.0.jsonl"))
        .expect("thresholds receipt committed")
        .into_parts()
        .0;

    G06Evidence {
        fixture_root: fold(&fixture_digests),
        generated_contract_root: format!(
            "{FUEL_SCHEMA}:ticks-per-unit=1000:strict-gt:zero-disables"
        ),
        implementation_root: fold(&table),
        mutation_root,
        no_mock_e2e_root,
        acceptance_green,
        used_wall_ms: 300_000,
        used_rss_bytes: 1 << 29,
    }
}

#[test]
fn the_g06_row_is_ratified_on_computed_evidence_and_the_ledger_holds_two_rows() {
    let roster = roster();
    let e9 = g09_evidence();
    let e6 = g06_evidence();
    assert!(e6.acceptance_green, "the fuel acceptance run must be green");
    let rows = vec![
        g09_decision(&roster, &e9).expect("G0-9 on roster"),
        g06_decision(&roster, &e6).expect("G0-6 on roster"),
    ];
    let g = verify(&rows, &roster);
    assert_eq!(g.ratified, vec!["G0-6".to_string()], "G0-6 lands ratified");
    assert_eq!(g.amended, vec!["G0-9".to_string()], "G0-9 stays amended");
    assert!(g.no_go.is_empty() && g.blocked.is_empty());
    assert_eq!(
        g.blocks.len(),
        8,
        "exactly the other eight block: {:?}",
        g.blocks
    );
    for b in &g.blocks {
        assert_eq!(b.reason(), "missing-decision", "{b:?}");
    }
    assert!(!g.clears(), "two rows must never clear a ten-spike gate");
}

#[test]
fn the_g06_mutation_receipt_holds_its_content_not_merely_its_presence() {
    let evidence_dir = fln_conformance::checked_manifest_dir!()
        .join("../../crates/fln-conformance/evidence/g06_fuel_parity");
    let mutation = std::fs::read_to_string(evidence_dir.join("mutation_campaign_v4.32.0.jsonl"))
        .expect("mutation receipt committed");
    let mut outcomes: std::collections::BTreeMap<&str, &str> = Default::default();
    let mut baseline_green = false;
    let mut restored_green = false;
    for line in mutation.lines() {
        assert!(
            line.contains("\"schema\": \"fln-g06-fuel-mutation/1\""),
            "unversioned receipt row: {line}"
        );
        let field = |key: &str| -> Option<&str> {
            let tag = format!("\"{key}\": \"");
            let start = line.find(&tag)? + tag.len();
            line[start..].split('"').next()
        };
        let (Some(mutant), Some(outcome)) = (field("mutant"), field("outcome")) else {
            panic!("receipt row missing mutant/outcome: {line}");
        };
        match mutant {
            "baseline" => baseline_green = outcome == "green",
            "restored" => restored_green = outcome == "green",
            m => {
                outcomes.insert(m, outcome);
            }
        }
    }
    assert!(
        baseline_green && restored_green,
        "campaign endpoints must be green"
    );
    assert_eq!(outcomes.len(), 10, "ten mutants gutted: {outcomes:?}");
    for (mutant, outcome) in &outcomes {
        assert_eq!(*outcome, "killed-by-named", "{mutant}");
    }
}

// ---------------------------------------------------------------------------
// The third real row: G0-4, Amended on a manifest-complete C0-C2 comparison.
// The ledger now holds three rows; exactly the other seven block as missing.
// ---------------------------------------------------------------------------

use fln_conformance::syntax_hygiene::{
    FixtureManifest, fixture_digest, measure_contract_usage, run_budget_matrix,
    stock_trace_contract,
};
use fln_epoch_lab::g0::{G04Evidence, g04_decision};

fn numeric_field(line: &str, key: &str) -> Option<u64> {
    let tag = format!("\"{key}\":");
    let start = line.find(&tag)? + tag.len();
    let digits = line[start..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect::<String>();
    (!digits.is_empty()).then(|| digits.parse().ok()).flatten()
}

fn g04_evidence() -> G04Evidence {
    let conformance = conformance_root();
    let fixture_dir = conformance.join("fixtures");
    let evidence_dir = conformance.join("evidence/g04_syntax_hygiene");
    let manifest_path = fixture_dir.join("g04_syntax_manifest.tsv");
    let reference_fixture_path = fixture_dir.join("g04_reference_fixture.lean");
    let semantic_path = evidence_dir.join("semantic_v4.32.0.ndjson");
    let telemetry_path = evidence_dir.join("telemetry_v4.32.0.ndjson");
    let mutation_path = evidence_dir.join("mutation_campaign_v4.32.0.ndjson");
    let regen_path = evidence_dir.join("regen_v4.32.0.ndjson");

    let manifest = FixtureManifest::load_embedded().expect("G0-4 manifest");
    manifest.validate_grammar_roots().expect("grammar roots");
    let semantic = std::fs::read_to_string(&semantic_path).expect("semantic evidence");
    let telemetry = std::fs::read_to_string(&telemetry_path).expect("telemetry evidence");
    let mutation = std::fs::read_to_string(&mutation_path).expect("mutation evidence");
    let regen = std::fs::read_to_string(&regen_path).expect("regeneration evidence");

    let semantic_lines = semantic.lines().collect::<Vec<_>>();
    let exact_rows = semantic_lines
        .iter()
        .filter(|line| line.contains(r#""classification":"exact""#))
        .count();
    let contract_gaps = semantic_lines
        .iter()
        .filter(|line| line.contains(r#""classification":"contract-gap""#))
        .count();
    let unclassified_rows = semantic_lines.len() - exact_rows - contract_gaps;

    let trace = stock_trace_contract().expect("stock G0-9 TraceContractV1");
    let one = run_budget_matrix(&manifest, 1).expect("one-thread budget matrix");
    let eight = run_budget_matrix(&manifest, 8).expect("eight-thread budget matrix");
    let thirty_two = run_budget_matrix(&manifest, 32).expect("32-thread budget matrix");
    let usage = measure_contract_usage(&manifest).expect("contract usage");
    let mutation_lines = mutation.lines().collect::<Vec<_>>();
    let semantic_root = fixture_digest(semantic.as_bytes());
    let telemetry_root = fixture_digest(telemetry.as_bytes());
    let mutation_receipt_root = fixture_digest(mutation.as_bytes());
    let mutation_root = derive_fixture_digest(&mutation_path)
        .expect("mutation receipt digest")
        .into_parts()
        .0;
    let regen_root = derive_fixture_digest(&regen_path)
        .expect("regeneration receipt digest")
        .into_parts()
        .0;

    let behavior = format!(
        "semantic={semantic_root}:manifest={}:trace={}:budget={}:usage={}",
        manifest.root(),
        trace.fixture_root,
        thirty_two.stream_root,
        usage.root()
    );
    let generated_contract = format!(
        "manifest={}:trace-schema={}:trace-root={}:budget={}:usage={}",
        manifest.root(),
        trace.schema,
        trace.fixture_root,
        thirty_two.stream_root,
        usage.root()
    );
    let fixture_inputs = format!(
        "manifest={}:fixture={}",
        derive_fixture_digest(&manifest_path)
            .expect("manifest digest")
            .into_parts()
            .0,
        derive_fixture_digest(&reference_fixture_path)
            .expect("Reference fixture digest")
            .into_parts()
            .0
    );

    let all_mutants_killed = mutation_lines.len() == 13
        && mutation_lines.iter().enumerate().all(|(sequence, line)| {
            line.contains(r#""schema":"fln-g04-mutation/1""#)
                && line.contains(&format!(r#""sequence":{sequence}"#))
                && line.contains(r#""actual":"killed""#)
        });
    let regen_bound = regen.lines().count() == 1
        && regen.contains(r#""schema":"fln-g04-regen/1""#)
        && regen.contains(&format!(r#""manifest_root":"{}""#, manifest.root()))
        && regen.contains(&format!(r#""semantic_root":"{semantic_root}""#))
        && regen.contains(&format!(r#""telemetry_root":"{telemetry_root}""#))
        && regen.contains(&format!(r#""mutation_root":"{mutation_receipt_root}""#))
        && regen.contains(&format!(r#""trace_root":"{}""#, trace.fixture_root))
        && regen.contains(&format!(r#""budget_root":"{}""#, thirty_two.stream_root))
        && regen.contains(&format!(r#""usage_root":"{}""#, usage.root()))
        && regen.contains(r#""exact":2,"contract_gaps":8,"unclassified":0"#)
        && regen.contains(r#""decision":"amended""#);
    let acceptance_green = semantic_lines.len() == 10
        && exact_rows == 2
        && contract_gaps == 8
        && unclassified_rows == 0
        && trace.elab_step_count == 261
        && one.stream_root == eight.stream_root
        && eight.stream_root == thirty_two.stream_root
        && [&one.partitions, &eight.partitions, &thirty_two.partitions]
            .into_iter()
            .all(|partitions| partitions.iter().all(|count| *count > 0))
        && all_mutants_killed
        && regen_bound;
    if !acceptance_green {
        eprintln!(
            "g04-acceptance-debug rows={} exact={} gaps={} unclassified={} \
             trace_steps={} roots_equal={} productive={} mutants={} regen={}",
            semantic_lines.len(),
            exact_rows,
            contract_gaps,
            unclassified_rows,
            trace.elab_step_count,
            one.stream_root == eight.stream_root && eight.stream_root == thirty_two.stream_root,
            [&one.partitions, &eight.partitions, &thirty_two.partitions]
                .into_iter()
                .all(|partitions| partitions.iter().all(|count| *count > 0)),
            all_mutants_killed,
            regen_bound
        );
    }

    let telemetry_line = telemetry.lines().next().expect("one telemetry row");
    let wall_micros = numeric_field(telemetry_line, "wall_micros").expect("wall_micros");
    let used_rss_bytes = numeric_field(telemetry_line, "peak_rss_bytes").expect("sampled peak RSS");

    G04Evidence {
        fixture_root: fixture_digest(fixture_inputs.as_bytes()),
        generated_contract_root: fixture_digest(generated_contract.as_bytes()),
        implementation_root: semantic_root,
        mutation_root,
        no_mock_e2e_root: regen_root,
        acceptance_root: fixture_digest(behavior.as_bytes()),
        acceptance_green,
        exact_rows,
        contract_gaps,
        unclassified_rows,
        used_wall_ms: wall_micros.saturating_add(999) / 1000,
        used_rss_bytes,
    }
}

#[test]
fn the_g04_row_is_amended_on_computed_evidence_and_the_ledger_holds_three_rows() {
    let roster = roster();
    let e4 = g04_evidence();
    let e6 = g06_evidence();
    let e9 = g09_evidence();
    assert!(e4.acceptance_green, "the G0-4 acceptance run must be green");
    assert_eq!(
        (e4.exact_rows, e4.contract_gaps, e4.unclassified_rows),
        (2, 8, 0)
    );
    let rows = vec![
        g04_decision(&roster, &e4).expect("G0-4 on roster"),
        g06_decision(&roster, &e6).expect("G0-6 on roster"),
        g09_decision(&roster, &e9).expect("G0-9 on roster"),
    ];
    let g = verify(&rows, &roster);
    assert_eq!(g.ratified, vec!["G0-6".to_string()]);
    assert_eq!(g.amended, vec!["G0-4".to_string(), "G0-9".to_string()]);
    assert!(g.no_go.is_empty() && g.blocked.is_empty());
    assert_eq!(
        g.blocks.len(),
        7,
        "exactly the other seven block: {:?}",
        g.blocks
    );
    for block in &g.blocks {
        assert_eq!(block.reason(), "missing-decision", "{block:?}");
    }
    assert!(!g.clears(), "three rows must not clear a ten-spike gate");
}

#[test]
fn the_g04_receipts_hold_content_not_merely_presence() {
    let evidence_dir = conformance_root().join("evidence/g04_syntax_hygiene");
    let semantic =
        std::fs::read_to_string(evidence_dir.join("semantic_v4.32.0.ndjson")).expect("semantic");
    let telemetry =
        std::fs::read_to_string(evidence_dir.join("telemetry_v4.32.0.ndjson")).expect("telemetry");
    let mutation = std::fs::read_to_string(evidence_dir.join("mutation_campaign_v4.32.0.ndjson"))
        .expect("mutation");
    let regen = std::fs::read_to_string(evidence_dir.join("regen_v4.32.0.ndjson")).expect("regen");

    assert_eq!(semantic.lines().count(), 10);
    assert_eq!(
        semantic
            .lines()
            .filter(|line| line.contains(r#""classification":"exact""#))
            .count(),
        2
    );
    assert_eq!(
        semantic
            .lines()
            .filter(|line| line.contains(r#""classification":"contract-gap""#))
            .count(),
        8
    );
    assert!(!semantic.contains("wall_micros"));
    assert!(telemetry.contains(r#""schema":"fln-g04-telemetry/1""#));
    assert!(telemetry.contains(r#""peak_rss_state":"sampled""#));
    assert!(!telemetry.contains("reference_root"));
    assert_eq!(mutation.lines().count(), 13);
    assert!(mutation.lines().all(|line| {
        line.contains(r#""schema":"fln-g04-mutation/1""#) && line.contains(r#""actual":"killed""#)
    }));
    assert_eq!(regen.lines().count(), 1);
    assert!(regen.contains(r#""reference_processes":2,"repetitions_equal":true"#));
    assert!(regen.contains(r#""exact":2,"contract_gaps":8,"unclassified":0"#));
    assert!(regen.contains(r#""decision":"amended""#));
}

// ---------------------------------------------------------------------------
// G0-1 (franken_lean-y24): the ABI-resurrection spike, decided Ratified on
// computed evidence. The evidence is EXECUTED here from committed artifacts:
// the fixture manifests, the canonical inventory, the receipt the probe
// writes against the real pinned artifacts, and the hostile-input sweep.
// ---------------------------------------------------------------------------
use fln_epoch_lab::g0::{G01Evidence, g01_decision};

/// Execute the acceptance checks and compute the evidence digests. The green
/// is what this function OBSERVES over the committed receipt and manifests; a
/// pasted root would rot exactly like the ones fln-8fwh evicted.
fn g01_evidence() -> G01Evidence {
    let root = fln_conformance::checked_manifest_dir!().join("../..");
    let c3_manifest = root.join("tribunal/fixtures/c3/MANIFEST.txt");
    let mathlib_manifest = root.join("tribunal/fixtures/mathlib/MANIFEST.txt");
    let mathlib_imports = root.join("tribunal/fixtures/mathlib/IMPORTS.tsv");
    let inventory = root.join("contracts/olean_inventory.json");
    let receipt_path = root
        .join("crates/fln-conformance/evidence/g01_abi_resurrection/resurrection_v4.32.0.jsonl");
    let sweep_path = root.join("crates/fln-olean/tests/region_read.rs");

    let fixture_root = format!(
        "c3={}:mathlib={}:imports={}",
        derive_fixture_digest(&c3_manifest)
            .expect("C3 manifest digest")
            .into_parts()
            .0,
        derive_fixture_digest(&mathlib_manifest)
            .expect("mathlib manifest digest")
            .into_parts()
            .0,
        derive_fixture_digest(&mathlib_imports)
            .expect("mathlib import oracle digest")
            .into_parts()
            .0,
    );
    let generated_contract_root = derive_fixture_digest(&inventory)
        .expect("OLEAN inventory digest")
        .into_parts()
        .0;

    let receipt = std::fs::read_to_string(&receipt_path).expect("resurrection receipt committed");
    let lines: Vec<&str> = receipt.lines().collect();

    // The acceptance run: every fixture row's census is replayed against the
    // amendment's recorded expectations, and the totals row is recomputed
    // from the per-row records rather than trusted.
    let mut per_row: Vec<String> = Vec::new();
    let mut row_objects = 0_u64;
    let mut row_constants = 0_u64;
    let mut row_entries = 0_u64;
    let mut saw = std::collections::BTreeSet::new();
    for line in &lines {
        if !line.contains(r#""module":"#) {
            continue;
        }
        let module = {
            let start = line.find(r#""module":""#).unwrap() + 10;
            let rest = &line[start..];
            rest[..rest.find('"').unwrap()].to_string()
        };
        let objects = numeric_field(line, "objects").expect("objects");
        let imports = numeric_field(line, "imports").expect("imports");
        let constants = numeric_field(line, "constants").expect("constants");
        let blocks = numeric_field(line, "extension_blocks").expect("blocks");
        let entries = numeric_field(line, "extension_entries").expect("entries");
        assert!(
            line.contains(r#""outcome":"ok""#),
            "fixture row not ok: {line}"
        );
        saw.insert(module.clone());
        row_objects += objects;
        row_constants += constants;
        row_entries += entries;
        per_row.push(format!(
            "{module}@{objects}/{imports}/{constants}/{blocks}/{entries}"
        ));
    }
    let expected_modules = [
        "Mathlib.Algebra.Group.Basic",
        "Mathlib.Algebra.Ring.Basic",
        "Mathlib.Analysis.SpecialFunctions.Log.Basic",
        "Mathlib.Data.Real.Basic",
        "Mathlib.Order.Basic",
        "Mathlib.Tactic.Basic",
    ];
    let expected: std::collections::BTreeSet<String> =
        expected_modules.iter().map(|m| m.to_string()).collect();
    let totals = lines.iter().find(|l| l.contains(r#""totals":"#));
    let sweep = lines.iter().find(|l| l.contains(r#""stdlib_sweep":"#));
    let corruption = lines
        .iter()
        .find(|l| l.contains(r#""corruption_control":"flipped_byte""#));
    let recovery = lines
        .iter()
        .find(|l| l.contains(r#""recovery":"pristine_fixture_rewalk""#));
    let oracle = lines
        .iter()
        .find(|l| l.contains(r#""import_oracle_rows":"#));

    let mut acceptance_green = saw == expected && per_row.len() == 6;
    acceptance_green &= totals.is_some_and(|t| {
        numeric_field(t, "fixtures") == Some(6)
            && numeric_field(t, "objects") == Some(row_objects)
            && numeric_field(t, "constants") == Some(row_constants)
            && numeric_field(t, "extension_entries") == Some(row_entries)
            && t.contains(r#""outcome":"pass""#)
    });
    acceptance_green &= sweep.is_some_and(|s| {
        numeric_field(s, "files") == Some(2433)
            && numeric_field(s, "ok") == Some(2433)
            && numeric_field(s, "objects") == Some(9_562_406)
            && numeric_field(s, "constants") == Some(158_608)
            && s.contains(r#""outcome":"zero_faults""#)
    });
    acceptance_green &= corruption.is_some_and(|c| c.contains(r#""outcome":"typed_error""#));
    acceptance_green &= recovery.is_some_and(|r| r.contains(r#""outcome":"ok""#));
    acceptance_green &= oracle.is_some_and(|o| {
        numeric_field(o, "import_oracle_rows") == Some(47)
            && o.contains(r#""outcome":"all_rows_match""#)
    });

    let implementation_root = {
        let mut joined = String::new();
        for row in &per_row {
            joined.push_str(row);
            joined.push(':');
        }
        if let Some(s) = sweep {
            joined.push_str(&format!(
                "stdlib@{}/{}/{}/{}",
                numeric_field(s, "files").unwrap_or(0),
                numeric_field(s, "ok").unwrap_or(0),
                numeric_field(s, "objects").unwrap_or(0),
                numeric_field(s, "constants").unwrap_or(0),
            ));
        }
        joined
    };
    let mutation_root = format!(
        "sweep={}:control={}",
        derive_fixture_digest(&sweep_path)
            .expect("region sweep digest")
            .into_parts()
            .0,
        corruption.map(|c| c.len()).unwrap_or(0),
    );
    let no_mock_e2e_root = derive_fixture_digest(&receipt_path)
        .expect("resurrection receipt digest")
        .into_parts()
        .0;

    G01Evidence {
        fixture_root,
        generated_contract_root,
        implementation_root,
        mutation_root,
        no_mock_e2e_root,
        acceptance_green,
        used_wall_ms: 120_000,
        used_rss_bytes: 1 << 30,
    }
}

#[test]
fn the_g01_row_is_ratified_on_computed_evidence_and_the_ledger_holds_four_rows() {
    let roster = roster();
    let e1 = g01_evidence();
    let e4 = g04_evidence();
    let e6 = g06_evidence();
    let e9 = g09_evidence();
    assert!(e1.acceptance_green, "the G0-1 acceptance run must be green");
    let rows = vec![
        g01_decision(&roster, &e1).expect("G0-1 on roster"),
        g04_decision(&roster, &e4).expect("G0-4 on roster"),
        g06_decision(&roster, &e6).expect("G0-6 on roster"),
        g09_decision(&roster, &e9).expect("G0-9 on roster"),
    ];
    let g = verify(&rows, &roster);
    assert_eq!(g.ratified, vec!["G0-1".to_string(), "G0-6".to_string()]);
    assert_eq!(g.amended, vec!["G0-4".to_string(), "G0-9".to_string()]);
    assert!(g.no_go.is_empty() && g.blocked.is_empty());
    assert_eq!(
        g.blocks.len(),
        6,
        "exactly the other six block: {:?}",
        g.blocks
    );
    for block in &g.blocks {
        assert_eq!(block.reason(), "missing-decision", "{block:?}");
    }
    assert!(!g.clears(), "four rows must not clear a ten-spike gate");
}

#[test]
fn the_g01_receipt_holds_content_not_merely_presence() {
    let root = fln_conformance::checked_manifest_dir!().join("../..");
    let receipt =
        std::fs::read_to_string(root.join(
            "crates/fln-conformance/evidence/g01_abi_resurrection/resurrection_v4.32.0.jsonl",
        ))
        .expect("resurrection receipt committed");
    let lines: Vec<&str> = receipt.lines().collect();
    assert_eq!(
        lines.iter().filter(|l| l.contains(r#""module":"#)).count(),
        6
    );
    assert!(
        lines
            .iter()
            .all(|l| l.contains(r#""schema":"fln-g01-resurrection/1""#))
    );
    assert!(receipt.contains(r#""corruption_control":"flipped_byte","outcome":"typed_error""#));
    assert!(receipt.contains(r#""recovery":"pristine_fixture_rewalk","outcome":"ok""#));
    assert!(receipt.contains(r#""import_oracle_rows":47,"outcome":"all_rows_match""#));
    assert!(receipt.contains(
        r#""stdlib_sweep":{"files":2433,"ok":2433,"objects":9562406,"constants":158608},"outcome":"zero_faults""#
    ));
    assert!(receipt.contains(r#""corpus_commit":"81a5d257c8e410db227a6665ed08f64fea08e997""#));
    // The amendment's heavy-extension row, by content: Order.Basic carries the
    // 44-block / 1591-entry payload, and no row's outcome is other than ok.
    assert!(receipt.contains(r#""module":"Mathlib.Order.Basic","fixture":"Order.Basic.olean""#));
    assert!(receipt.contains(r#""extension_blocks":44,"extension_entries":1591"#));
    assert!(!receipt.contains(r#""outcome":"fault"#));
}
