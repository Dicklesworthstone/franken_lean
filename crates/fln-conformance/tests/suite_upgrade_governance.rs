//! W1 governance proof: candidate lock changes cannot become authoritative by
//! prose, a partial join, or a waiver.

#![forbid(unsafe_code)]

use fln_conformance::suite_upgrade::{self, Candidate, LedgerState, LockChange, Waiver};

fn root() -> std::path::PathBuf {
    fln_conformance::checked_workspace_root!()
}

fn complete_candidate(change: LockChange) -> Candidate {
    Candidate {
        change,
        current_lock_root: "old-lock-root".to_string(),
        candidate_lock_root: "new-lock-root".to_string(),
        isolated: true,
        closure_delta: true,
        canonical_contract_and_census_diff: true,
        tribunal_diff: true,
        component_migration: true,
        rollback_proven: true,
        current_root_unchanged: true,
        external_evidence_identity: true,
        cancelled: false,
    }
}

#[test]
fn upstream_ledger_state_machine() {
    let text = std::fs::read_to_string(root().join("UPSTREAM_LEDGER.md")).expect("ledger exists");
    let rows = suite_upgrade::parse_ledger(&text).expect("ledger parses");
    suite_upgrade::validate_ledger(&rows).expect("all planned foundations are governed");
    assert!(LedgerState::Investigated.can_transition_to(LedgerState::UpstreamRequested));
    assert!(LedgerState::AcceptanceEvidenced.can_transition_to(LedgerState::LoadBearing));
    assert!(!LedgerState::Investigated.can_transition_to(LedgerState::LoadBearing));
    for transition in [
        (LedgerState::Proposed, LedgerState::Investigated),
        (
            LedgerState::UpstreamRequested,
            LedgerState::AcceptedUpstream,
        ),
        (LedgerState::AcceptedUpstream, LedgerState::Released),
        (LedgerState::Released, LedgerState::PinnedInSuiteLock),
        (
            LedgerState::PinnedInSuiteLock,
            LedgerState::AcceptanceEvidenced,
        ),
    ] {
        assert!(transition.0.can_transition_to(transition.1));
    }
}

#[test]
fn suite_upgrade_candidate_model() {
    for change in [
        LockChange::Addition,
        LockChange::Removal,
        LockChange::Upgrade,
        LockChange::Downgrade,
        LockChange::Retarget,
        LockChange::Nightly,
        LockChange::TargetFeature,
        LockChange::Profile,
        LockChange::Reference,
        LockChange::Corpus,
        LockChange::PathCommitTreeChecksum,
    ] {
        assert!(
            complete_candidate(change).may_publish(None),
            "complete candidate must publish"
        );
    }
    let mut partial = complete_candidate(LockChange::Upgrade);
    partial.current_root_unchanged = false;
    assert_eq!(
        partial.publication_error(),
        Some("current authoritative root changed during candidate validation")
    );
}

#[test]
fn lock_delta_contract_join() {
    let required = [
        "closure_delta",
        "canonical_contract_and_census_diff",
        "tribunal_diff",
        "component_migration",
        "rollback_proven",
        "current_root_unchanged",
        "external_evidence_identity",
    ];
    for field in required {
        let mut candidate = complete_candidate(LockChange::Reference);
        match field {
            "closure_delta" => candidate.closure_delta = false,
            "canonical_contract_and_census_diff" => {
                candidate.canonical_contract_and_census_diff = false
            }
            "tribunal_diff" => candidate.tribunal_diff = false,
            "component_migration" => candidate.component_migration = false,
            "rollback_proven" => candidate.rollback_proven = false,
            "current_root_unchanged" => candidate.current_root_unchanged = false,
            "external_evidence_identity" => candidate.external_evidence_identity = false,
            _ => unreachable!(),
        }
        assert!(
            candidate.publication_error().is_some(),
            "premature publication mutant `{field}` survived"
        );
    }
}

#[test]
fn waiver_authority_model() {
    let good = Waiver {
        owner: "W1".to_string(),
        scope: "candidate abc only".to_string(),
        rationale: "upstream unavailable".to_string(),
        expiry: "2026-08-11".to_string(),
        review_date: "2026-08-08".to_string(),
        defers_only: true,
        constitutional_or_load_bearing: false,
    };
    good.validate().expect("bounded defer-only waiver is valid");
    assert!(
        !complete_candidate(LockChange::Upgrade).may_publish(Some(&good)),
        "waiver must not promote a candidate"
    );
    let mut forbidden = good;
    forbidden.constitutional_or_load_bearing = true;
    assert!(
        forbidden.validate().is_err(),
        "constitutional waiver mutant survived"
    );
    let mut nonexpiring = forbidden;
    nonexpiring.constitutional_or_load_bearing = false;
    nonexpiring.expiry = "never".to_string();
    assert!(
        nonexpiring.validate().is_err(),
        "nonexpiring waiver mutant survived"
    );
}

#[test]
fn suite_upgrade_no_mock_e2e() {
    let authoritative = std::fs::read(root().join("SUITE.lock")).expect("real current lock exists");
    let before = authoritative.clone();
    let mut candidate = complete_candidate(LockChange::Upgrade);
    candidate.tribunal_diff = false;
    assert!(
        !candidate.may_publish(None),
        "stale Tribunal root must fail the isolated candidate"
    );
    candidate.tribunal_diff = true;
    assert!(
        candidate.may_publish(None),
        "complete isolated candidate must pass"
    );
    candidate.cancelled = true;
    assert!(
        !candidate.may_publish(None),
        "cancelled candidate must remain non-authoritative"
    );
    let after =
        std::fs::read(root().join("SUITE.lock")).expect("real current lock remains readable");
    assert_eq!(
        before, after,
        "candidate evaluation must not modify the authoritative SUITE.lock root"
    );
}
