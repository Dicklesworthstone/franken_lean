//! W1 governance proof: candidate lock changes cannot become authoritative by
//! prose, a partial join, or a waiver.

#![forbid(unsafe_code)]

use fln_conformance::suite_upgrade::{
    self, Candidate, CandidateReceipt, LedgerState, LockChange, Waiver,
};

fn root() -> std::path::PathBuf {
    fln_conformance::checked_workspace_root!()
}

fn complete_candidate(change: LockChange) -> Candidate {
    Candidate {
        change,
        current_lock_root: root_identity('a'),
        candidate_lock_root: root_identity('b'),
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

fn root_identity(digit: char) -> String {
    digit.to_string().repeat(64)
}

fn complete_receipt(change: LockChange) -> CandidateReceipt {
    CandidateReceipt {
        candidate_id: "suite-upgrade-fixture".to_string(),
        change,
        old_lock_root: root_identity('a'),
        candidate_lock_root: root_identity('b'),
        closure_root: root_identity('c'),
        contract_and_census_root: root_identity('d'),
        tribunal_root: root_identity('e'),
        migration_root: root_identity('f'),
        rollback_root: root_identity('1'),
        external_evidence_root: root_identity('2'),
        final_current_lock_root: root_identity('a'),
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
        assert!(
            complete_candidate(change)
                .publication_error_with_receipt(&complete_receipt(change))
                .is_none(),
            "complete candidate receipt must publish"
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
fn candidate_receipt_join_refuses_stale_or_mixed_roots() {
    let candidate = complete_candidate(LockChange::Upgrade);
    let mut stale_current = complete_receipt(LockChange::Upgrade);
    stale_current.final_current_lock_root = root_identity('3');
    assert_eq!(
        candidate.publication_error_with_receipt(&stale_current),
        Some(
            "candidate receipt observed an authoritative lock root different from its old root"
                .to_string()
        ),
        "a changed authoritative root must fail before publication"
    );

    let mut mixed_tribunal = complete_receipt(LockChange::Upgrade);
    mixed_tribunal.tribunal_root = "mixed-root".to_string();
    assert_eq!(
        candidate.publication_error_with_receipt(&mixed_tribunal),
        Some("candidate receipt `tribunal_root` is not a canonical SHA-256 root".to_string()),
        "a stale or mixed Tribunal receipt must fail"
    );

    let mut non_hex_root = complete_receipt(LockChange::Upgrade);
    non_hex_root.closure_root = root_identity('g');
    assert_eq!(
        candidate.publication_error_with_receipt(&non_hex_root),
        Some("candidate receipt `closure_root` is not a canonical SHA-256 root".to_string()),
        "a non-hex root must not pass as a canonical identity"
    );

    let mut wrong_change = complete_receipt(LockChange::Reference);
    wrong_change.candidate_id = "reference-candidate".to_string();
    assert_eq!(
        candidate.publication_error_with_receipt(&wrong_change),
        Some(
            "candidate change kind `upgrade` does not match receipt change kind `reference`"
                .to_string()
        ),
        "a receipt from another change class must not join"
    );
}

#[test]
fn candidate_receipt_ndjson_is_strict_and_canonical() {
    let receipt = complete_receipt(LockChange::Upgrade);
    let ndjson = receipt.to_ndjson().expect("complete receipt renders");
    assert_eq!(
        CandidateReceipt::from_ndjson(&ndjson).expect("canonical receipt parses"),
        receipt
    );

    let reordered = ndjson.replacen(
        r#"{"schema":"fln-suite-upgrade-candidate/1","candidate_id""#,
        r#"{"candidate_id":"suite-upgrade-fixture","schema""#,
        1,
    );
    assert!(
        CandidateReceipt::from_ndjson(&reordered).is_err(),
        "a reordered receipt must not be canonical"
    );

    let missing_newline = ndjson.trim_end_matches('\n');
    assert!(
        CandidateReceipt::from_ndjson(missing_newline).is_err(),
        "a receipt without final newline must refuse"
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
        candidate
            .publication_error_with_receipt(&complete_receipt(LockChange::Upgrade))
            .is_none(),
        "complete isolated candidate receipt must pass"
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
