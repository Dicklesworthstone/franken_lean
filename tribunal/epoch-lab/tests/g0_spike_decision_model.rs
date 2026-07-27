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
