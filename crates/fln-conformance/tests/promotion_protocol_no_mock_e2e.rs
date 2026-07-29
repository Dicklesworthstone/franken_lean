//! No-mock promotion publication protocol (bead `fln-52mc`).
//!
//! The parent launches this compiled test binary as a real child process. One child
//! appends two complete frames, a second appends only the first half of a quarantine
//! frame and exits at that process boundary, and a third appends the exact remainder.
//! Recovery must keep serving the last complete generation after the interrupted
//! append and advance exactly once the frame is complete. The tiny generated journal
//! is intentionally left in the system temporary directory; this suite never deletes
//! or overwrites a file.

#![forbid(unsafe_code)]

use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};

use fln_core::mode::{
    BuildProfileId, CgsePolicyId, ContentRoot, EpochId, Mode, ReproducibilityProfile, TargetId,
};
use fln_core::outcome::Outcome;
use fln_core::scratch::{SHADOW_PROMOTION_PREFIX, ScratchRoot};
use fln_hash::shadow::{
    CandidateResultV1, ClaimTypeV1, ComparisonClassV1, EngineVersionV1, EvidenceStateV1,
    FixtureComparisonV1, FixtureManifestV1, FixtureVerdictV1, IncidentObservationV1,
    IncidentReasonV1, MutationStatusV1, ParityRowV1, PolicyVersionV1, ProductV1,
    PromotionDecisionV1, PromotionEvidenceV1, PromotionPolicyV1, SamplingObligationV1,
    SemanticResultV1, ShadowAuthorityV1, ShadowCellSpecV1, ShadowCellV1, ShadowPublicationV1,
    ShadowScopeV1, ShadowStateV1, ShadowTelemetryV1, ValidationStatusV1, recover_journal,
};

const CHILD_MODE: &str = "FLN_SHADOW_E2E_CHILD_MODE";
const JOURNAL_PATH: &str = "FLN_SHADOW_E2E_JOURNAL_PATH";
const PARTIAL_EXIT: i32 = 86;

macro_rules! fixture_panic {
    ($($arg:tt)*) => {
        panic!(/* ubs:ignore — test-only diagnostic. */ $($arg)*)
    };
}

fn root(seed: u8) -> ContentRoot {
    ContentRoot::new([seed; 32])
}

fn baseline_engine() -> EngineVersionV1 {
    EngineVersionV1 {
        engine_id: 1_001,
        version: 3,
        binary_root: root(1),
    }
}

fn candidate_engine() -> EngineVersionV1 {
    EngineVersionV1 {
        engine_id: 1_002,
        version: 5,
        binary_root: root(2),
    }
}

fn policy_version() -> PolicyVersionV1 {
    PolicyVersionV1 {
        policy_id: CgsePolicyId::new(1_003),
        version: 7,
        policy_root: root(3),
    }
}

fn scope() -> ShadowScopeV1 {
    ShadowScopeV1 {
        workload_id: 1_004,
        workload_root: root(4),
        epoch: EpochId::new(1_005),
        epoch_root: root(5),
        mode: Mode::Sound,
        reproducibility: ReproducibilityProfile::Certified,
        build_profile: BuildProfileId::new(1_006),
        profile_root: root(6),
        target: TargetId::new(1_007),
        target_root: root(7),
    }
}

fn sampling() -> SamplingObligationV1 {
    SamplingObligationV1 {
        policy: policy_version(),
        seed_root: root(8),
        divisor: 8,
        required_initial_passes: 2,
    }
}

fn fixture_manifest() -> FixtureManifestV1 {
    FixtureManifestV1::from_fixture_ids(vec![2_001, 2_002]).expect("fixture manifest")
}

fn initial_cell() -> ShadowCellV1 {
    ShadowCellV1::new(ShadowCellSpecV1 {
        scope: scope(),
        baseline: ProductV1 {
            engine: baseline_engine(),
            product_root: root(9),
            semantic_result: SemanticResultV1::Accepted {
                result_root: root(10),
            },
        },
        candidate: CandidateResultV1::Complete(ProductV1 {
            engine: candidate_engine(),
            product_root: root(11),
            semantic_result: SemanticResultV1::Accepted {
                result_root: root(10),
            },
        }),
        comparison_class: ComparisonClassV1::ExactParity,
        fixture_manifest: fixture_manifest(),
        policy: policy_version(),
        claim_type: ClaimTypeV1::BoundedModel,
        parity_row: ParityRowV1 {
            row_id: 2_003,
            row_root: root(12),
        },
        sampling: sampling(),
    })
    .expect("initial shadow cell")
}

fn promotion_policy() -> PromotionPolicyV1 {
    PromotionPolicyV1 {
        candidate_engine: candidate_engine(),
        policy: policy_version(),
        required_claim_type: ClaimTypeV1::BoundedModel,
        required_evidence_state: EvidenceStateV1::IndependentlyValidated,
        require_kernel_validation: true,
        require_independent_validation: true,
        require_mutation_completion: true,
        minimum_fixture_count: 2,
    }
}

fn promotion_evidence(cell: &ShadowCellV1) -> PromotionEvidenceV1 {
    PromotionEvidenceV1 {
        protocol_version: 1,
        observed_generation: cell.generation(),
        observed_cell_root: cell.semantic_root(),
        scope_root: cell.scope().semantic_root(),
        candidate_engine: candidate_engine(),
        policy: policy_version(),
        fixture_manifest: fixture_manifest(),
        comparisons: vec![
            FixtureComparisonV1 {
                fixture_id: 2_001,
                reference_result_root: root(13),
                candidate_result_root: root(13),
                verdict: FixtureVerdictV1::Match,
            },
            FixtureComparisonV1 {
                fixture_id: 2_002,
                reference_result_root: root(14),
                candidate_result_root: root(14),
                verdict: FixtureVerdictV1::Match,
            },
        ],
        claim_type: ClaimTypeV1::BoundedModel,
        evidence_state: EvidenceStateV1::IndependentlyValidated,
        parity_row: cell.parity_row(),
        kernel_validation: ValidationStatusV1::Passed {
            receipt_root: root(15),
        },
        independent_validation: ValidationStatusV1::Passed {
            receipt_root: root(16),
        },
        mutation_status: MutationStatusV1::Complete {
            campaign_root: root(17),
            killed: 7,
            total: 7,
        },
        limitation_roots: vec![root(18)],
        continued_sampling: sampling(),
        revalidation_incident: None,
        publication_generation: cell.generation() + 1,
    }
}

fn telemetry() -> ShadowTelemetryV1 {
    ShadowTelemetryV1 {
        attempts: 2,
        latency_micros: 250,
        worker_count: 8,
        dropped_events: 0,
    }
}

fn complete<T: std::fmt::Debug>(outcome: Outcome<T>) -> T {
    outcome.into_complete().unwrap_or_else(|non_authoritative| {
        fixture_panic!("non-authoritative: {non_authoritative:?}")
    })
}

fn publications() -> (
    ShadowPublicationV1,
    ShadowPublicationV1,
    ShadowPublicationV1,
) {
    let initial = initial_cell();
    let initial_publication =
        ShadowPublicationV1::build(initial.clone(), telemetry()).expect("initial publication");
    let authority = ShadowAuthorityV1::new(initial.clone());
    let promotion = complete(authority.attempt_promotion(
        Outcome::Complete(promotion_evidence(&initial)),
        promotion_policy(),
        telemetry(),
    ));
    let PromotionDecisionV1::Promoted(promoted) = promotion else {
        fixture_panic!("valid evidence promotes");
    };
    let promoted_cell = complete(authority.snapshot());
    let incident = IncidentObservationV1 {
        observed_generation: promoted_cell.generation(),
        observed_cell_root: promoted_cell.semantic_root(),
        scope_root: promoted_cell.scope().semantic_root(),
        candidate_engine: candidate_engine(),
        policy: policy_version(),
        reason: IncidentReasonV1::Regression,
        evidence_root: root(19),
    };
    let quarantined = complete(authority.report_incident(
        Outcome::Complete(incident),
        ShadowTelemetryV1 {
            latency_micros: 9_999,
            ..telemetry()
        },
    ));
    (
        initial_publication,
        promoted.publication,
        quarantined.transition.publication,
    )
}

fn child_configuration() -> Option<(String, PathBuf)> {
    let mode = std::env::var(CHILD_MODE).ok()?;
    let path = PathBuf::from(std::env::var_os(JOURNAL_PATH)?);
    Some((mode, path))
}

fn append(path: &Path, bytes: &[u8], create_new: bool) {
    let mut options = OpenOptions::new();
    options.write(true);
    if create_new {
        options.create_new(true);
    } else {
        options.append(true);
    }
    let mut file = options.open(path).expect("open generated journal");
    file.write_all(bytes).expect("append publication bytes");
    file.sync_all().expect("sync publication bytes");
}

#[test]
fn publication_writer_child() {
    let Some((mode, path)) = child_configuration() else {
        return;
    };
    let (initial, promoted, quarantined) = publications();
    let quarantine_frame = quarantined.journal_frame();
    let split = quarantine_frame.len() / 2;
    let (prefix, suffix) = quarantine_frame.split_at(split);
    match mode.as_str() {
        "base" => {
            let mut bytes = initial.journal_frame();
            bytes.extend_from_slice(&promoted.journal_frame());
            append(&path, &bytes, true);
        }
        "partial" => {
            append(&path, prefix, false);
            std::process::exit(PARTIAL_EXIT);
        }
        "finish" => append(&path, suffix, false),
        other => fixture_panic!("unknown child mode {other}"),
    }
}

fn run_child(path: &Path, mode: &str) -> ExitStatus {
    Command::new(std::env::current_exe().expect("current test executable"))
        .arg("--exact")
        .arg("publication_writer_child")
        .arg("--nocapture")
        .env(CHILD_MODE, mode)
        .env(JOURNAL_PATH, path)
        .status()
        .expect("launch publication child")
}

/// One guard-owned journal root per run: the journal file lives INSIDE the guard's
/// directory, so file and root reclaim together on a pass and retain together on a
/// failure (franken_lean-eir2; the journal previously lived directly in the temp dir
/// and was never reclaimed).
fn journal_fixture() -> (ScratchRoot, PathBuf) {
    let root = ScratchRoot::create(SHADOW_PROMOTION_PREFIX, "shadow-promotion", "journal")
        .expect("journal fixture root is creatable");
    let path = root.join("shadow-promotion.journal");
    (root, path)
}

#[test]
fn promotion_protocol_no_mock_e2e() {
    if std::env::var_os(CHILD_MODE).is_some() {
        return;
    }
    let (_guard, path) = journal_fixture();
    assert!(run_child(&path, "base").success(), "base child");

    let base_bytes = std::fs::read(&path).expect("read real journal");
    let base = complete(recover_journal(&base_bytes)).expect("recover base journal");
    assert_eq!(base.complete_frames, 2);
    let promoted = base.latest.expect("promoted publication").publication;
    assert!(matches!(
        promoted.cell().state(),
        ShadowStateV1::Promoted { .. }
    ));

    let partial_status = run_child(&path, "partial");
    assert_eq!(partial_status.code(), Some(PARTIAL_EXIT));
    let partial_bytes = std::fs::read(&path).expect("read interrupted journal");
    let recovered = complete(recover_journal(&partial_bytes)).expect("recover safe generation");
    assert_eq!(recovered.complete_frames, 2);
    assert!(recovered.incomplete_tail_bytes > 0);
    assert_eq!(
        recovered
            .latest
            .expect("prior complete frame")
            .publication
            .cell()
            .semantic_root(),
        promoted.cell().semantic_root()
    );

    assert!(run_child(&path, "finish").success(), "recovery child");
    let complete_bytes = std::fs::read(&path).expect("read completed journal");
    let recovered = complete(recover_journal(&complete_bytes)).expect("recover complete journal");
    assert_eq!(recovered.complete_frames, 3);
    assert_eq!(recovered.incomplete_tail_bytes, 0);
    assert!(matches!(
        recovered
            .latest
            .expect("quarantined publication")
            .publication
            .cell()
            .state(),
        ShadowStateV1::Quarantined { .. }
    ));

    // The independently parsed semantic plane contains no operational field.
    assert!(!promoted.semantic_ndjson().contains("latency_micros"));
    assert!(!promoted.semantic_ndjson().contains("worker_count"));
    assert!(promoted.telemetry_ndjson().contains("latency_micros"));
    assert!(promoted.telemetry_ndjson().contains("worker_count"));
}

/// `franken_lean-eir2` acceptance criterion 3: retention on failure is proved in BOTH
/// directions for this family, never inferred from the passing cell — and the journal
/// file must share its root's fate in both directions, which is the point of moving
/// the file inside the guard's directory.
#[test]
fn shadow_promotion_roots_reclaim_on_pass_and_retain_on_failure() {
    let (passing_root, passing_journal) = {
        let (guard, journal) = journal_fixture();
        std::fs::write(&journal, b"journal-bytes").expect("plant a journal");
        (guard.path().to_path_buf(), journal)
    };
    assert!(
        !passing_root.exists(),
        "a passing cell's journal root must be reclaimed: {}",
        passing_root.display()
    );
    assert!(
        !passing_journal.exists(),
        "the journal inside a reclaimed root is gone with it: {}",
        passing_journal.display()
    );

    let observed = std::cell::RefCell::new(None);
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let (guard, journal) = journal_fixture();
        std::fs::write(&journal, b"journal-bytes").expect("plant a journal");
        *observed.borrow_mut() = Some((guard.path().to_path_buf(), journal));
        panic!("deliberate failure so the fixture guard drops during an unwind");
    }));
    assert!(unwound.is_err(), "the failing cell must actually unwind");
    let (retained_root, retained_journal) = observed
        .into_inner()
        .expect("the failing cell materialized before it panicked");
    assert!(
        retained_root.exists(),
        "a failing cell's journal root must be retained: {}",
        retained_root.display()
    );
    assert!(
        retained_journal.exists(),
        "the journal inside a retained root is kept with it: {}",
        retained_journal.display()
    );
    std::fs::remove_dir_all(&retained_root).expect("the probe reclaims what it retained");
}
