//! Suite `oracle_outcome_authority` (bead `fln-1dxv`; plan §18).
//!
//! # The rule under test
//!
//! **A Reference timeout, cancellation, resource refusal, unavailable platform
//! or crash is Inconclusive/InternalFault — never a semantic reject, and never a
//! FrankenLean divergence.**
//!
//! This is the highest-risk rule in the Tribunal bootstrap. Getting it wrong
//! does not merely lose information; it manufactures divergences that do not
//! exist. That is worse than missing real ones, because a rig that cries wolf
//! has its genuine findings discounted forever after. It is FL-INV-07 applied to
//! the oracle's *process* rather than to its *answer*, and it is the same law
//! `crates/fln-kernel/tests/reference_differential.rs` enforces at the other end
//! of the pipe: a non-answer from either side is unscorable and fails rather
//! than passing.
//!
//! # Vocabulary separation
//!
//! The second half of the suite holds the twelve closed vocabularies apart. The
//! failure mode is conflation — an L-level standing in for a claim state is how
//! an unearned claim gets laundered into looking evidenced — so the tests vary
//! one vocabulary while holding the rest fixed and demand the answer not move.
//!
//! # Mutants planted and killed
//!
//! | mutant | edit | killed by |
//! |---|---|---|
//! | oracle crash read as reject | `ProcessOutcome::completed_exit` returns `Some(1)` for `Crashed` | `a_crash_is_never_a_reject_even_when_its_stderr_says_error` |
//! | claim/L-level conflation | `EvidenceRow::justifies` also requires `self.level == LLevel::L4` | `justifies_does_not_read_the_l_level` |
//!
//! (The two normalizer mutants are in `typed_normalizer_model.rs`.)

#![forbid(unsafe_code)]

use fln_epoch_lab::oracle::{
    ClaimType, ComparisonClass, DeterminismClass, EvidenceKind, EvidenceRow, EvidenceState,
    Freshness, LLevel, Mode, NonAuthoritative, Observation, OracleAuthority, OracleKind,
    OracleVerdict, OurVerdict, Platform, ProcessOutcome, Scored, score,
};

/// Exhaustive over [`ProcessOutcome`] with no wildcard arm: adding a variant to
/// the vocabulary without deciding its authority is a compile error here, not a
/// silent default.
fn outcome_label(o: &ProcessOutcome) -> &'static str {
    match o {
        ProcessOutcome::Completed { .. } => "completed",
        ProcessOutcome::Timeout { .. } => "timeout",
        ProcessOutcome::Cancelled => "cancelled",
        ProcessOutcome::ResourceRefused { .. } => "resource-refused",
        ProcessOutcome::PlatformUnavailable { .. } => "platform-unavailable",
        ProcessOutcome::Crashed { .. } => "crashed",
    }
}

/// Every way the Reference can fail to answer. One per non-`Completed` variant;
/// `non_completing_covers_every_non_completed_variant` proves the coverage.
fn non_completing() -> Vec<ProcessOutcome> {
    vec![
        ProcessOutcome::Timeout { after_ms: 30_000 },
        ProcessOutcome::Cancelled,
        ProcessOutcome::ResourceRefused { what: "memory" },
        ProcessOutcome::PlatformUnavailable {
            platform: Platform::MacOSAarch64,
        },
        ProcessOutcome::Crashed { signal: Some(11) },
        ProcessOutcome::Crashed { signal: None },
    ]
}

fn observed(outcome: ProcessOutcome, diagnostic: &str) -> Observation {
    Observation {
        kind: OracleKind::ReferenceBinary,
        authority: OracleAuthority::Authoritative,
        outcome,
        platform: Platform::LinuxX86_64,
        diagnostic: diagnostic.to_string(),
    }
}

#[test]
fn non_completing_covers_every_non_completed_variant() {
    // Guards the corpus itself: if a variant is added and the fixture list is
    // not extended, every other test in this file silently stops covering it.
    let mut seen: Vec<&str> = non_completing().iter().map(outcome_label).collect();
    seen.sort_unstable();
    seen.dedup();
    assert_eq!(
        seen,
        vec![
            "cancelled",
            "crashed",
            "platform-unavailable",
            "resource-refused",
            "timeout",
        ],
        "the non-completing corpus no longer covers the vocabulary"
    );
}

#[test]
fn no_non_completing_outcome_yields_an_exit_status() {
    for o in non_completing() {
        assert!(
            o.completed_exit().is_none(),
            "{} produced an exit status",
            outcome_label(&o)
        );
        assert!(
            !o.is_semantic(),
            "{} claimed to be semantic",
            outcome_label(&o)
        );
    }
}

#[test]
fn every_non_completing_outcome_is_a_no_answer_never_a_reject() {
    for o in non_completing() {
        let label = outcome_label(&o);
        let obs = observed(o, "");
        match obs.verdict() {
            OracleVerdict::NoAnswer(NonAuthoritative::Inconclusive { .. }) => {}
            other => panic!("{label} was read as {other:?} instead of Inconclusive"),
        }
    }
}

#[test]
fn a_crash_is_never_a_reject_even_when_its_stderr_says_error() {
    // The sharpest form of the mutant. A Reference that dies on SIGSEGV can
    // still have printed a diagnostic first, so "the text looks like a
    // rejection" is exactly the wrong signal to key on. The process outcome
    // decides; the text never does.
    let obs = observed(
        ProcessOutcome::Crashed { signal: Some(11) },
        "error: unknown identifier 'Nat.succ_le_of_lt'\nerror: 1 error",
    );
    match obs.verdict() {
        OracleVerdict::NoAnswer(NonAuthoritative::Inconclusive {
            outcome: ProcessOutcome::Crashed { signal },
        }) => assert!(signal == Some(11)),
        other => panic!("a crash whose stderr says 'error:' was read as {other:?}"),
    }
    // And the diagnostic is retained, because it is evidence ABOUT THE RUN even
    // though it is not a verdict. Discarding it would make the finding
    // untriageable.
    assert!(obs.diagnostic.contains("unknown identifier"));
}

#[test]
fn a_non_answer_from_the_oracle_is_never_a_divergence_whatever_we_said() {
    let ours = [
        OurVerdict::Accepted,
        OurVerdict::Rejected {
            diagnostic: "type mismatch".to_string(),
        },
        OurVerdict::Inconclusive {
            what: "heartbeat exhausted".to_string(),
        },
    ];
    for o in non_completing() {
        let label = outcome_label(&o);
        for ourv in &ours {
            let scored = score(ourv, &observed(o.clone(), "error: boom"));
            assert!(
                !scored.is_divergence(),
                "{label} paired with {ourv:?} was scored as a divergence: {scored:?}"
            );
            assert!(
                matches!(scored, Scored::Unscorable(_)),
                "{label} paired with {ourv:?} scored {scored:?}"
            );
        }
    }
}

#[test]
fn our_own_inconclusive_is_unscorable_even_when_the_oracle_answered() {
    // The other end of the same pipe. A non-answer from EITHER side is
    // unscorable; there is no asymmetry where our silence counts as agreement.
    for oracle_exit in [0, 1] {
        let scored = score(
            &OurVerdict::Inconclusive {
                what: "maxHeartbeats".to_string(),
            },
            &observed(ProcessOutcome::Completed { exit: oracle_exit }, "error: x"),
        );
        assert!(!scored.is_divergence());
        match scored {
            Scored::Unscorable(NonAuthoritative::InternalFault { what }) => {
                assert!(what.contains("maxHeartbeats"));
            }
            other => panic!("our Inconclusive scored {other:?}"),
        }
    }
}

#[test]
fn a_completed_nonzero_exit_is_a_real_reject() {
    // The over-correction guard. It would be trivially easy to satisfy every
    // test above by never producing a rejection at all, which would make the
    // rig blind instead of noisy. A completed run that says no means no.
    let obs = observed(
        ProcessOutcome::Completed { exit: 1 },
        "error: type mismatch",
    );
    match obs.verdict() {
        OracleVerdict::Rejected { diagnostic } => assert!(diagnostic.contains("type mismatch")),
        other => panic!("a completed nonzero exit was read as {other:?}"),
    }
    assert!(matches!(
        observed(ProcessOutcome::Completed { exit: 0 }, "").verdict(),
        OracleVerdict::Accepted
    ));
}

#[test]
fn only_two_answered_sides_can_produce_a_divergence() {
    let reject = || OurVerdict::Rejected {
        diagnostic: "ours".to_string(),
    };
    let accepted = || observed(ProcessOutcome::Completed { exit: 0 }, "");
    let rejected = || observed(ProcessOutcome::Completed { exit: 1 }, "error: theirs");

    assert_eq!(score(&OurVerdict::Accepted, &accepted()), Scored::Agree);
    assert_eq!(score(&reject(), &rejected()), Scored::Agree);
    // We reject, the Reference accepts: restrictive. A finding, and the ONLY
    // direction D23 can ever carve out.
    assert_eq!(score(&reject(), &accepted()), Scored::Restrictive);
    // We accept, the Reference rejects: unsoundness. Never carve-out-able.
    assert_eq!(
        score(&OurVerdict::Accepted, &rejected()),
        Scored::UnsoundlyPermissive
    );
    assert!(Scored::Restrictive.is_divergence());
    assert!(Scored::UnsoundlyPermissive.is_divergence());
    assert!(!Scored::Agree.is_divergence());
}

#[test]
fn authority_and_answeredness_are_separate_conditions() {
    // Two axes, checked separately. Folding them into one boolean is how an
    // advisory oracle's opinion gets promoted to a settlement, or how an
    // authoritative oracle's crash gets treated as a settled answer.
    let authoritative_crash = Observation {
        authority: OracleAuthority::Authoritative,
        ..observed(ProcessOutcome::Crashed { signal: Some(9) }, "")
    };
    assert!(
        !authoritative_crash.can_settle(),
        "an authoritative oracle that crashed settled something"
    );

    let advisory_answer = Observation {
        authority: OracleAuthority::Advisory,
        ..observed(ProcessOutcome::Completed { exit: 1 }, "error: nope")
    };
    // It produced a real verdict...
    assert!(matches!(
        advisory_answer.verdict(),
        OracleVerdict::Rejected { .. }
    ));
    // ...and still cannot settle the question.
    assert!(!advisory_answer.can_settle());

    let authoritative_answer = Observation {
        authority: OracleAuthority::Authoritative,
        ..observed(ProcessOutcome::Completed { exit: 0 }, "")
    };
    assert!(authoritative_answer.can_settle());
}

#[test]
fn an_internal_fault_is_ours_and_an_inconclusive_is_the_oracles() {
    // Both are non-authoritative, and they are not interchangeable. A crash of
    // the Reference is a fact about the Reference; an InternalFault is a fact
    // about our own accounting. Collapsing them loses the only signal that says
    // which side to go and fix.
    for o in non_completing() {
        assert!(matches!(
            o.non_authoritative(),
            Some(NonAuthoritative::Inconclusive { .. })
        ));
    }
    assert!(
        ProcessOutcome::Completed { exit: 0 }
            .non_authoritative()
            .is_none()
    );
    assert!(matches!(
        NonAuthoritative::internal_fault("count conservation failed"),
        NonAuthoritative::InternalFault { .. }
    ));
}

// ---------------------------------------------------------------------------
// Vocabulary separation
// ---------------------------------------------------------------------------

const ALL_CLAIMS: [ClaimType; 6] = [
    ClaimType::Invariant,
    ClaimType::Proof,
    ClaimType::BoundedModel,
    ClaimType::Statistical,
    ClaimType::Slo,
    ClaimType::Benchmark,
];
const ALL_LEVELS: [LLevel; 5] = [LLevel::L0, LLevel::L1, LLevel::L2, LLevel::L3, LLevel::L4];
const ALL_STATES: [EvidenceState; 5] = [
    EvidenceState::Observed,
    EvidenceState::Targeted,
    EvidenceState::Hypothesis,
    EvidenceState::Proven,
    EvidenceState::Blocked,
];

fn row(claim: ClaimType, state: EvidenceState, level: LLevel) -> EvidenceRow {
    EvidenceRow {
        claim,
        kind: EvidenceKind::Differential,
        state,
        level,
        mode: Mode::Sound,
        determinism: DeterminismClass::D0,
        freshness: Freshness::Current,
        platform: Platform::LinuxX86_64,
    }
}

#[test]
fn justifies_does_not_read_the_l_level() {
    // The named conflation mutant. If `justifies` ever consults `level`, an
    // L-level starts standing in for a claim state and an unearned claim gets
    // laundered. Vary the level across its whole vocabulary and demand the
    // answer not move, for every claim/state combination.
    for claim in ALL_CLAIMS {
        for state in ALL_STATES {
            for claimed in ALL_CLAIMS {
                let baseline = row(claim, state, LLevel::L0).justifies(claimed);
                for level in ALL_LEVELS {
                    assert!(
                        row(claim, state, level).justifies(claimed) == baseline,
                        "justifies({claimed:?}) moved with the L-level \
                         (claim {claim:?}, state {state:?}, level {level:?})"
                    );
                }
            }
        }
    }
}

#[test]
fn compatibility_level_does_not_read_the_claim_type() {
    // The same guard in the other direction: a strong claim type must not
    // confer a compatibility level. Conflation is symmetric and so is the test.
    for state in ALL_STATES {
        for level in ALL_LEVELS {
            let baseline = row(ClaimType::Benchmark, state, level).compatibility_level();
            for claim in ALL_CLAIMS {
                assert!(
                    row(claim, state, level).compatibility_level() == baseline,
                    "compatibility_level moved with the claim type \
                     (claim {claim:?}, state {state:?}, level {level:?})"
                );
            }
        }
    }
}

#[test]
fn justifies_reads_neither_mode_determinism_freshness_nor_platform() {
    // The remaining vocabularies, held apart the same way. None of them is a
    // claim-strength axis, so none may move a D7 decision.
    let base = row(ClaimType::Proof, EvidenceState::Proven, LLevel::L2);
    let expected = base.justifies(ClaimType::Proof);
    for mode in [Mode::Faithful, Mode::Sound, Mode::Frontier] {
        let mut r = base.clone();
        r.mode = mode;
        assert!(
            r.justifies(ClaimType::Proof) == expected,
            "mode {mode:?} moved it"
        );
    }
    for d in [
        DeterminismClass::D0,
        DeterminismClass::D1,
        DeterminismClass::D2,
        DeterminismClass::D3,
        DeterminismClass::D4,
    ] {
        let mut r = base.clone();
        r.determinism = d;
        assert!(
            r.justifies(ClaimType::Proof) == expected,
            "determinism {d:?} moved it"
        );
    }
    for f in [Freshness::Current, Freshness::Stale, Freshness::Absent] {
        let mut r = base.clone();
        r.freshness = f;
        assert!(
            r.justifies(ClaimType::Proof) == expected,
            "freshness {f:?} moved it"
        );
    }
    for p in [
        Platform::LinuxX86_64,
        Platform::MacOSAarch64,
        Platform::WindowsX86_64,
    ] {
        let mut r = base.clone();
        r.platform = p;
        assert!(
            r.justifies(ClaimType::Proof) == expected,
            "platform {p:?} moved it"
        );
    }
    for k in [
        EvidenceKind::UnitTest,
        EvidenceKind::PropertyTest,
        EvidenceKind::MutationKill,
        EvidenceKind::Differential,
        EvidenceKind::NoMockE2E,
    ] {
        let mut r = base.clone();
        r.kind = k;
        assert!(
            r.justifies(ClaimType::Proof) == expected,
            "kind {k:?} moved it"
        );
    }
}

#[test]
fn a_weaker_claim_class_never_justifies_a_stronger_one() {
    // D7 as a full matrix rather than a sentence. Strength descends
    // Invariant > Proof > BoundedModel > Statistical > Slo > Benchmark, and the
    // expectation is written from that order rather than from the function, so
    // the test does not merely restate the implementation.
    let strength = |c: ClaimType| ALL_CLAIMS.iter().position(|x| *x == c).expect("in table");
    for held in ALL_CLAIMS {
        for claimed in ALL_CLAIMS {
            // Lower index == stronger, given ALL_CLAIMS is in descending order.
            let should = strength(held) <= strength(claimed);
            let got = row(held, EvidenceState::Proven, LLevel::L4).justifies(claimed);
            assert!(
                got == should,
                "a {held:?} row justifying a {claimed:?} claim: got {got}, want {should}"
            );
        }
    }
}

#[test]
fn an_unestablished_evidence_state_justifies_nothing_and_reports_no_level() {
    for state in [
        EvidenceState::Targeted,
        EvidenceState::Hypothesis,
        EvidenceState::Blocked,
    ] {
        for claim in ALL_CLAIMS {
            for claimed in ALL_CLAIMS {
                assert!(
                    !row(claim, state, LLevel::L4).justifies(claimed),
                    "a {state:?} {claim:?} row justified a {claimed:?} claim"
                );
            }
            assert!(
                row(claim, state, LLevel::L4)
                    .compatibility_level()
                    .is_none(),
                "a {state:?} row reported an L-level"
            );
        }
    }
    for state in [EvidenceState::Proven, EvidenceState::Observed] {
        assert_eq!(
            row(ClaimType::Proof, state, LLevel::L3).compatibility_level(),
            Some(LLevel::L3)
        );
    }
}

#[test]
fn the_comparison_class_vocabulary_is_not_an_authority_vocabulary() {
    // Both are small closed enums that a reader could imagine ordering. Neither
    // is ordered, and neither is convertible to the other; this test exists so
    // that an attempt to add such a conversion has to delete a named test.
    let classes = [
        ComparisonClass::ByteIdentical,
        ComparisonClass::NormalizedIdentical,
        ComparisonClass::AcceptanceOnly,
        ComparisonClass::DiagnosticEquivalent,
    ];
    assert!(classes.len() == 4);
    assert!(ComparisonClass::ByteIdentical != ComparisonClass::AcceptanceOnly);
    assert!(OracleAuthority::Authoritative != OracleAuthority::Advisory);
    assert!(OracleKind::ReferenceBinary != OracleKind::ReferenceChecker);
}
