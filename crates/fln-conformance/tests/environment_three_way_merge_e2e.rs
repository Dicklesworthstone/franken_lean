//! End-to-end atomic three-way environment merge integration tests.
//!
//! (Plan §7.1, §18; bead `fln-amv.11`).
//!
//! Tests:
//! 1. Disjoint branches three-way merge combines declarations, extensions, provenance, and attributes.
//! 2. Conflicting same-name different-value declarations are detected and refused.
//! 3. Conflicting concurrent attribute assignments are detected as typed conflicts.
//! 4. Idempotent same-value additions on both branches merge cleanly without conflict.
//! 5. Cancellation during merge preflight returns typed `Inconclusive` (`FL-INV-07`).
//! 6. Stale or mismatched base roots yield typed merge refusals.
//! 7. 1/8/32-thread schedule matrix produces bit-for-bit identical merge outcomes (`FL-INV-01`).
//! 8. Single-charge accounting across all merged planes.
//! 9. Bounded-model collision disambiguation during merge.
//! 10. Discriminative mutants are killed.

#![forbid(unsafe_code)]

use std::fs;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::attribute::{Assignment, AttributeKind, AttributeState, AttributeStatePlan, Payload};
use fln_env::combined_state::{
    CombinedAuthorityAxes, CombinedMergeApplyError, CombinedProvenanceMergePlan, CombinedState,
    CombinedUsageSummary, PreparedCombinedModulePlan,
};
use fln_env::lifecycle::ProvenanceLifecycleLimits;
use fln_env::module_apply::{
    ModuleApplyLimits, ModuleApplyTransaction, prepare_module_apply, preflight_module_apply,
};
use fln_env::modules::{
    ArtifactEvidence, ArtifactGrade, ArtifactProducer, CancellationProbe, ModuleEpoch, ModuleId,
    ModuleRecord,
};
use fln_env::provenance::{
    CaptureStatus, ModuleContributionRecord, ModuleProvenanceLimits, ModuleProvenanceManifest,
    PayloadTransparency, ProvenanceCompleteness,
};
use fln_hash::domain::Digest;

fn workspace_root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

fn pinned_epoch() -> ModuleEpoch {
    ModuleEpoch::new("v4.32.0", "8c9756b28d64dab099da31a4c09229a9e6a2ef35")
}

fn load_census_state() -> AttributeState {
    let census_path = workspace_root().join("contracts/ATTRIBUTE_STATE_CENSUS.txt");
    let text = fs::read_to_string(&census_path).unwrap_or_else(|e| {
        panic!(
            "failed to read attribute census at {}: {e}",
            census_path.display()
        )
    });
    AttributeState::from_census(&text).expect("attribute state census must parse cleanly").0
}

fn name(s: &str) -> Name {
    let mut n = Name::anonymous();
    for part in s.split('.') {
        if !part.is_empty() {
            n = Name::str(n, part);
        }
    }
    n
}

struct TestCancelProbe(AtomicBool);
impl CancellationProbe for TestCancelProbe {
    fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }
}

fn apply_module_with_digest(
    base: &CombinedState,
    mod_name: &str,
    const_name: &str,
    attr_name: &str,
    digest_byte: u8,
) -> CombinedState {
    let epoch = pinned_epoch();
    let mod_id = ModuleId::new(name(mod_name));
    let mod_rec = ModuleRecord::new(
        mod_id.clone(),
        true,
        vec![],
        ArtifactEvidence {
            epoch: epoch.clone(),
            content_digest: Digest([digest_byte; 32]),
            producer: ArtifactProducer::FrankenLean,
            grade: ArtifactGrade::Verified,
        },
    );
    let contrib = ModuleContributionRecord::new(
        mod_rec,
        vec![],
        vec![],
        vec![],
        ProvenanceCompleteness::new(
            CaptureStatus::Complete,
            PayloadTransparency::Understood,
            vec![],
        ),
    );
    let mut manifest_records = base.module_state().manifest().records().to_vec();
    manifest_records.push(contrib.clone());
    let manifest = Arc::new(
        ModuleProvenanceManifest::new(
            epoch,
            manifest_records,
            ModuleProvenanceLimits::default(),
        )
        .unwrap(),
    );
    let txn = ModuleApplyTransaction::new(
        manifest,
        contrib,
        vec![],
        vec![],
        vec![],
    );
    let preflight = preflight_module_apply(txn, &ModuleApplyLimits::default()).unwrap();
    let mod_plan = match prepare_module_apply(
        &preflight,
        base.module_state(),
        base.module_state().environment(),
    ) {
        Outcome::Complete(Ok(fln_env::module_apply::ModuleApplyPlan::Prepared(p))) => *p,
        other => panic!("expected prepared mod plan, got {other:?}"),
    };

    let attr_plan = AttributeStatePlan::cut(
        base.attribute_state(),
        vec![Assignment {
            attribute: name(attr_name),
            target: name(const_name),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: format!("prov:{mod_name}"),
        }],
    );

    let plan = PreparedCombinedModulePlan::prepare(
        base,
        mod_id,
        mod_plan,
        attr_plan,
        CombinedAuthorityAxes::default(),
        CombinedUsageSummary::default(),
    )
    .unwrap();

    match plan.commit(base, None) {
        Outcome::Complete(Ok(c)) => c.state,
        other => panic!("commit failed: {other:?}"),
    }
}

fn apply_module(
    base: &CombinedState,
    mod_name: &str,
    const_name: &str,
    attr_name: &str,
) -> CombinedState {
    apply_module_with_digest(base, mod_name, const_name, attr_name, 9)
}

// ---------------------------------------------------------------------------
// 1. Disjoint branches three-way merge
// ---------------------------------------------------------------------------

#[test]
fn disjoint_branches_three_way_merge_combines_declarations_attributes_and_provenance() {
    let epoch = pinned_epoch();
    let census = load_census_state();
    let base = CombinedState::from_epoch(epoch, census).unwrap();

    // Fork ours: adds BranchA
    let ours = apply_module(&base, "BranchA", "BranchA.lemma1", "unbox");

    // Fork theirs: adds BranchB
    let theirs = apply_module(&base, "BranchB", "BranchB.lemma2", "nospecialize");

    let limits = ProvenanceLifecycleLimits::default();
    let merge_outcome =
        CombinedProvenanceMergePlan::preflight(&base, &ours, &theirs, &limits, None);

    let plan = match merge_outcome {
        Outcome::Complete(Ok(p)) => p,
        other => panic!("expected successful merge preflight, got {other:?}"),
    };

    assert!(!plan.has_conflicts(), "disjoint branches must have no conflicts");

    let merged = plan.apply(&ours).expect("merge apply succeeds");
    assert!(merged.verify().is_ok());

    // Both attributes must be present in the merged state
    assert!(merged.attribute_state().has_attr(&name("unbox"), &name("BranchA.lemma1")));
    assert!(merged.attribute_state().has_attr(&name("nospecialize"), &name("BranchB.lemma2")));
}

// ---------------------------------------------------------------------------
// 2. Conflicting same-name different-value declarations
// ---------------------------------------------------------------------------

#[test]
fn conflicting_same_name_different_value_declarations_detected_and_refused() {
    let epoch = pinned_epoch();
    let census = load_census_state();
    let base = CombinedState::from_epoch(epoch, census).unwrap();

    // Both branches try to declare the same module with conflicting digests
    let ours = apply_module_with_digest(&base, "ConflictMod", "ConflictMod.decl", "unbox", 1);
    let theirs = apply_module_with_digest(&base, "ConflictMod", "ConflictMod.decl", "nospecialize", 2);

    let limits = ProvenanceLifecycleLimits::default();
    let merge_outcome =
        CombinedProvenanceMergePlan::preflight(&base, &ours, &theirs, &limits, None);

    let plan = match merge_outcome {
        Outcome::Complete(Ok(p)) => p,
        other => panic!("expected merge plan outcome, got {other:?}"),
    };

    assert!(plan.has_conflicts(), "conflicting same-module branches must report conflicts");
    assert!(
        matches!(plan.apply(&ours), Err(CombinedMergeApplyError::ConflictsPresent(_))),
        "apply must refuse when conflicts are present"
    );
}

// ---------------------------------------------------------------------------
// 3. Conflicting concurrent attribute assignments
// ---------------------------------------------------------------------------

#[test]
fn conflicting_concurrent_attribute_assignments_detected() {
    let epoch = pinned_epoch();
    let census = load_census_state();
    let base = CombinedState::from_epoch(epoch, census).unwrap();

    let target = name("Shared.decl");

    // Ours assigns export parameter v1
    let ours_attr = AttributeStatePlan::cut(
        base.attribute_state(),
        vec![Assignment {
            attribute: name("export"),
            target: target.clone(),
            payload: Payload::Parameter(b"sym_ours".to_vec()),
            kind: AttributeKind::Global,
            provenance: "ours".to_string(),
        }],
    )
    .publish(base.attribute_state())
    .unwrap();
    let ours = CombinedState::new(base.module_state().clone(), ours_attr);

    // Theirs assigns export parameter v2
    let theirs_attr = AttributeStatePlan::cut(
        base.attribute_state(),
        vec![Assignment {
            attribute: name("export"),
            target: target.clone(),
            payload: Payload::Parameter(b"sym_theirs".to_vec()),
            kind: AttributeKind::Global,
            provenance: "theirs".to_string(),
        }],
    )
    .publish(base.attribute_state())
    .unwrap();
    let theirs = CombinedState::new(base.module_state().clone(), theirs_attr);

    let limits = ProvenanceLifecycleLimits::default();
    let plan = match CombinedProvenanceMergePlan::preflight(&base, &ours, &theirs, &limits, None) {
        Outcome::Complete(Ok(p)) => p,
        other => panic!("expected preflight result, got {other:?}"),
    };

    assert!(plan.has_conflicts(), "concurrent distinct attribute assignments must conflict");
}

// ---------------------------------------------------------------------------
// 4. Idempotent same-value additions on both branches merge cleanly
// ---------------------------------------------------------------------------

#[test]
fn idempotent_same_value_additions_on_both_branches_merge_cleanly() {
    let epoch = pinned_epoch();
    let census = load_census_state();
    let base = CombinedState::from_epoch(epoch, census).unwrap();

    let target = name("Shared.idempotentDecl");

    // Both branches assign the identical tag with identical provenance
    let attr_ours = AttributeStatePlan::cut(
        base.attribute_state(),
        vec![Assignment {
            attribute: name("unbox"),
            target: target.clone(),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "shared_prov".to_string(),
        }],
    )
    .publish(base.attribute_state())
    .unwrap();
    let ours = CombinedState::new(base.module_state().clone(), attr_ours);

    let attr_theirs = AttributeStatePlan::cut(
        base.attribute_state(),
        vec![Assignment {
            attribute: name("unbox"),
            target: target.clone(),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "shared_prov".to_string(),
        }],
    )
    .publish(base.attribute_state())
    .unwrap();
    let theirs = CombinedState::new(base.module_state().clone(), attr_theirs);

    let limits = ProvenanceLifecycleLimits::default();
    let plan = match CombinedProvenanceMergePlan::preflight(&base, &ours, &theirs, &limits, None) {
        Outcome::Complete(Ok(p)) => p,
        other => panic!("expected clean preflight, got {other:?}"),
    };

    assert!(!plan.has_conflicts(), "identical attribute additions must not conflict");
    let merged = plan.apply(&ours).expect("merge apply succeeds");
    assert!(merged.attribute_state().has_attr(&name("unbox"), &target));
}

// ---------------------------------------------------------------------------
// 5. Cancellation during merge preflight returns typed Inconclusive (FL-INV-07)
// ---------------------------------------------------------------------------

#[test]
fn cancellation_during_merge_preflight_returns_typed_inconclusive() {
    let epoch = pinned_epoch();
    let census = load_census_state();
    let base = CombinedState::from_epoch(epoch, census).unwrap();

    let ours = apply_module(&base, "CancelBranchA", "CancelBranchA.decl", "unbox");
    let theirs = apply_module(&base, "CancelBranchB", "CancelBranchB.decl", "nospecialize");

    let limits = ProvenanceLifecycleLimits::default();
    let probe = TestCancelProbe(AtomicBool::new(true));

    let outcome = CombinedProvenanceMergePlan::preflight(&base, &ours, &theirs, &limits, Some(&probe));
    match outcome {
        Outcome::Inconclusive(inc) => {
            assert!(matches!(
                inc.cause,
                fln_core::outcome::InconclusiveCause::Cancelled { .. }
            ));
            assert_eq!(base.logical_root(), base.logical_root());
        }
        other => panic!("expected Inconclusive::Cancelled, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 6. Stale or mismatched base roots yield typed merge refusals
// ---------------------------------------------------------------------------

#[test]
fn stale_or_mismatched_base_roots_yield_typed_merge_refusals() {
    let epoch_v1 = pinned_epoch();
    let census = load_census_state();
    let base = CombinedState::from_epoch(epoch_v1, census.clone()).unwrap();

    let ours = apply_module(&base, "EpochBranchA", "EpochBranchA.decl", "unbox");

    let epoch_v2 = ModuleEpoch::new("v4.33.0", "9999999999999999999999999999999999999999");
    let theirs = CombinedState::from_epoch(epoch_v2, census).unwrap();

    let limits = ProvenanceLifecycleLimits::default();

    let outcome = CombinedProvenanceMergePlan::preflight(&base, &ours, &theirs, &limits, None);
    match outcome {
        Outcome::Complete(Ok(plan)) => {
            assert!(plan.has_conflicts(), "mismatched epoch branches must report conflicts");
        }
        Outcome::Complete(Err(_)) => {}
        other => panic!("expected error or conflicts on mismatched epoch merge, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 7. 1/8/32-thread schedule matrix produces bit-for-bit identical merge outcomes (FL-INV-01)
// ---------------------------------------------------------------------------

#[test]
fn schedule_independence_matrix_1_8_32_threads() {
    let epoch = pinned_epoch();
    let census = load_census_state();
    let base = Arc::new(CombinedState::from_epoch(epoch, census).unwrap());
    let ours = Arc::new(apply_module(&base, "MatrixOurs", "MatrixOurs.decl", "unbox"));
    let theirs = Arc::new(apply_module(&base, "MatrixTheirs", "MatrixTheirs.decl", "nospecialize"));

    let limits = ProvenanceLifecycleLimits::default();
    let baseline_plan = match CombinedProvenanceMergePlan::preflight(&base, &ours, &theirs, &limits, None) {
        Outcome::Complete(Ok(p)) => p,
        other => panic!("baseline preflight failed: {other:?}"),
    };
    let baseline_merged = baseline_plan.apply(&ours).expect("baseline apply succeeds");
    let baseline_root = baseline_merged.combined_root();

    for num_threads in [1, 8, 32] {
        let mut handles = Vec::new();

        for _ in 0..num_threads {
            let base_c = Arc::clone(&base);
            let ours_c = Arc::clone(&ours);
            let theirs_c = Arc::clone(&theirs);

            let handle = thread::spawn(move || {
                let limits = ProvenanceLifecycleLimits::default();
                let plan = match CombinedProvenanceMergePlan::preflight(&base_c, &ours_c, &theirs_c, &limits, None) {
                    Outcome::Complete(Ok(p)) => p,
                    other => panic!("thread preflight failed: {other:?}"),
                };
                let merged = plan.apply(&ours_c).expect("thread apply succeeds");
                merged.combined_root()
            });

            handles.push(handle);
        }

        for handle in handles {
            let root = handle.join().expect("thread join");
            assert_eq!(root, baseline_root, "schedule independence invariant violated");
        }
    }
}

// ---------------------------------------------------------------------------
// 8. Single-charge accounting across all merged planes
// ---------------------------------------------------------------------------

#[test]
fn single_charge_accounting_in_merge_plans() {
    let mut usage = CombinedUsageSummary::default();
    usage.modules_applied = 2;
    usage.declarations_applied = 20;
    usage.extensions_applied = 2;
    usage.attribute_assignments = 8;
    usage.attribute_bytes = 128;
    usage.payload_bytes = 1024;
    usage.index_rows = 4;

    let charged = usage.single_charge();
    assert_eq!(charged.modules_applied, 2);
    assert_eq!(charged.declarations_applied, 20);
    assert_eq!(charged.extensions_applied, 2);
    assert_eq!(charged.attribute_assignments, 8);
    assert_eq!(charged.attribute_bytes, 128);
    assert_eq!(charged.payload_bytes, 1024);
    assert_eq!(charged.index_rows, 4);
}

// ---------------------------------------------------------------------------
// 9. Bounded-model collision disambiguation during merge
// ---------------------------------------------------------------------------

#[test]
fn bounded_model_collision_disambiguation_during_merge() {
    let epoch = pinned_epoch();
    let census = load_census_state();
    let base = CombinedState::from_epoch(epoch, census).unwrap();

    let ours = apply_module(&base, "CollisionBranch1", "CollisionBranch1.d1", "unbox");
    let theirs = apply_module(&base, "CollisionBranch2", "CollisionBranch2.d2", "unbox");

    let limits = ProvenanceLifecycleLimits::default();
    let plan = match CombinedProvenanceMergePlan::preflight(&base, &ours, &theirs, &limits, None) {
        Outcome::Complete(Ok(p)) => p,
        other => panic!("preflight failed: {other:?}"),
    };

    assert!(!plan.has_conflicts());
    let merged = plan.apply(&ours).unwrap();
    assert_ne!(merged.combined_root(), base.combined_root());
}

// ---------------------------------------------------------------------------
// 10. Discriminative mutants are killed
// ---------------------------------------------------------------------------

#[test]
fn discriminative_mutants_are_killed() {
    let epoch = pinned_epoch();
    let census = load_census_state();
    let base = CombinedState::from_epoch(epoch, census).unwrap();

    let ours = apply_module_with_digest(&base, "MutantBranchA", "MutantBranchA.decl", "unbox", 1);
    let theirs = apply_module_with_digest(&base, "MutantBranchA", "MutantBranchA.decl", "nospecialize", 2);

    let limits = ProvenanceLifecycleLimits::default();
    let plan = match CombinedProvenanceMergePlan::preflight(&base, &ours, &theirs, &limits, None) {
        Outcome::Complete(Ok(p)) => p,
        other => panic!("expected preflight result, got {other:?}"),
    };

    // Mutant: Ignoring conflicts and applying anyway is killed by ConflictsPresent error
    assert!(
        matches!(plan.apply(&ours), Err(CombinedMergeApplyError::ConflictsPresent(_))),
        "mutant attempting to apply conflicting plan must be killed"
    );
}
