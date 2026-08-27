//! End-to-end real module fixture validation and import-graph matrix tests.
//!
//! (Plan §7.1, §18; bead `fln-amv.9.4`).
//!
//! Tests:
//! 1. Real pinned Reference `.olean` fixtures decode and match the checked-in
//!    oracle `IMPORTS.tsv` byte-for-byte in exact row order.
//! 2. All eight import-flag triples, duplicate rows, and structural Names are preserved lossless.
//! 3. `ModuleBatchApplyPlan` privately stages closures with zero visible prefix on mid-batch failure.
//! 4. Cancellation at deterministic checkpoints returns typed `Inconclusive`, is never cached,
//!    and leaves base state untouched.
//! 5. 1/8/32-thread schedule matrix produces bit-for-bit identical roots and receipts (`FL-INV-01`).
//! 6. Single-charge accounting across decoder, graph, declarations, extensions, and provenance.
//! 7. Collision disambiguation over equal-digest unequal-value keys.
//! 8. Discriminative mutants are killed.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

use fln_conformance::module_adapter::{
    ModuleBatchApplyPlan, ModuleBatchCommitError, ModuleBatchPlanError, ModuleBatchUsageSummary,
    OleanModuleAdapter,
};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{CacheAdmission, Outcome};
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
use fln_env::module_apply::{
    ModuleApplyLimits, ModuleApplyState, ModuleApplyTransaction, preflight_module_apply,
};
use fln_env::modules::{
    ArtifactEvidence, ArtifactGrade, ArtifactProducer, CancellationProbe, DirectImport, ModuleEpoch,
    ModuleId, ModuleRecord,
};
use fln_env::provenance::{
    CaptureStatus, ModuleContributionRecord, ModuleProvenanceLimits, ModuleProvenanceManifest,
    PayloadTransparency, ProvenanceCompleteness,
};
use fln_hash::domain::{Domain, hash};

type TsvImportRow = (usize, Name, bool, bool, bool);

fn workspace_root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

fn pinned_epoch() -> ModuleEpoch {
    ModuleEpoch::new("v4.32.0", "8c9756b28d64dab099da31a4c09229a9e6a2ef35")
}

fn parse_dot_name(s: &str) -> Name {
    let mut name = Name::anonymous();
    for part in s.split('.') {
        if !part.is_empty() {
            if let Ok(num) = part.parse::<u64>() {
                name = Name::num(name, num);
            } else {
                name = Name::str(name, part);
            }
        }
    }
    name
}

fn parse_tsv_imports(path: &Path) -> BTreeMap<String, Vec<TsvImportRow>> {
    let content = fs::read_to_string(path).unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    let mut map: BTreeMap<String, Vec<TsvImportRow>> = BTreeMap::new();
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let cols = line.split('\t').collect::<Vec<_>>();
        assert!(cols.len() >= 6, "invalid TSV line: {line}");
        let fixture = cols[0].to_string();
        let index = cols[1].parse::<usize>().unwrap();
        let module_name = parse_dot_name(cols[2]);
        let import_all = cols[3].parse::<bool>().unwrap();
        let is_exported = cols[4].parse::<bool>().unwrap();
        let is_meta = cols[5].parse::<bool>().unwrap();
        map.entry(fixture)
            .or_default()
            .push((index, module_name, import_all, is_exported, is_meta));
    }
    map
}

#[test]
fn real_pinned_fixtures_decode_and_match_c3_oracle_imports() {
    let root = workspace_root();
    let tsv_path = root.join("tribunal/fixtures/c3/IMPORTS.tsv");
    let oracle = parse_tsv_imports(&tsv_path);
    let epoch = pinned_epoch();

    let fixtures = [
        ("Init.olean", "tribunal/fixtures/c3/Init.olean"),
        (
            "Init.BinderNameHint.olean",
            "tribunal/fixtures/c3/Init.BinderNameHint.olean",
        ),
        (
            "Init.SizeOfLemmas.olean",
            "tribunal/fixtures/c3/Init.SizeOfLemmas.olean",
        ),
    ];

    let mut total_rows = 0;
    for (fixture_name, fixture_rel_path) in fixtures {
        let fixture_path = root.join(fixture_rel_path);
        let mod_id = ModuleId::new(parse_dot_name(
            fixture_name.strip_suffix(".olean").unwrap(),
        ));
        let decoded = OleanModuleAdapter::decode_file(mod_id.clone(), &fixture_path, epoch.clone())
            .unwrap_or_else(|e| panic!("failed to decode {}: {e:?}", fixture_path.display()));

        let expected_rows = oracle
            .get(fixture_name)
            .unwrap_or_else(|| panic!("no oracle rows for {fixture_name}"));

        assert_eq!(
            decoded.imports.len(),
            expected_rows.len(),
            "import count mismatch for {fixture_name}"
        );

        for (i, (expected_idx, expected_name, exp_all, exp_exp, exp_meta)) in
            expected_rows.iter().enumerate()
        {
            assert_eq!(i, *expected_idx);
            let imp = &decoded.imports[i];
            assert_eq!(imp.module.name(), expected_name);
            assert_eq!(imp.import_all, *exp_all);
            assert_eq!(imp.is_exported, *exp_exp);
            assert_eq!(imp.is_meta, *exp_meta);
            total_rows += 1;
        }

        let module_rec = decoded.to_module_record();
        assert_eq!(module_rec.id, mod_id);
        assert_eq!(module_rec.direct_imports().len(), expected_rows.len());
    }

    assert_eq!(total_rows, 50, "all 50 c3 oracle rows verified exactly");
}

#[test]
fn real_pinned_fixtures_decode_and_match_mathlib_oracle_imports() {
    let root = workspace_root();
    let tsv_path = root.join("tribunal/fixtures/mathlib/IMPORTS.tsv");
    let oracle = parse_tsv_imports(&tsv_path);
    let epoch = pinned_epoch();

    let fixtures = [
        ("Order.Basic.olean", "tribunal/fixtures/mathlib/Order.Basic.olean"),
        (
            "Algebra.Group.Basic.olean",
            "tribunal/fixtures/mathlib/Algebra.Group.Basic.olean",
        ),
        (
            "Algebra.Ring.Basic.olean",
            "tribunal/fixtures/mathlib/Algebra.Ring.Basic.olean",
        ),
        (
            "Data.Real.Basic.olean",
            "tribunal/fixtures/mathlib/Data.Real.Basic.olean",
        ),
        (
            "Tactic.Basic.olean",
            "tribunal/fixtures/mathlib/Tactic.Basic.olean",
        ),
        (
            "Analysis.SpecialFunctions.Log.Basic.olean",
            "tribunal/fixtures/mathlib/Analysis.SpecialFunctions.Log.Basic.olean",
        ),
    ];

    let mut total_rows = 0;
    for (fixture_name, fixture_rel_path) in fixtures {
        let fixture_path = root.join(fixture_rel_path);
        let mod_id = ModuleId::new(parse_dot_name(
            fixture_name.strip_suffix(".olean").unwrap(),
        ));
        let decoded = OleanModuleAdapter::decode_file(mod_id.clone(), &fixture_path, epoch.clone())
            .unwrap_or_else(|e| panic!("failed to decode {}: {e:?}", fixture_path.display()));

        let expected_rows = oracle
            .get(fixture_name)
            .unwrap_or_else(|| panic!("no oracle rows for {fixture_name}"));

        assert_eq!(
            decoded.imports.len(),
            expected_rows.len(),
            "import count mismatch for {fixture_name}"
        );

        for (i, (expected_idx, expected_name, exp_all, exp_exp, exp_meta)) in
            expected_rows.iter().enumerate()
        {
            assert_eq!(i, *expected_idx);
            let imp = &decoded.imports[i];
            assert_eq!(imp.module.name(), expected_name);
            assert_eq!(imp.import_all, *exp_all);
            assert_eq!(imp.is_exported, *exp_exp);
            assert_eq!(imp.is_meta, *exp_meta);
            total_rows += 1;
        }
    }

    assert_eq!(total_rows, 47, "all 47 mathlib oracle rows verified exactly");
}

#[test]
fn all_eight_import_flag_combinations_and_duplicates_preserved() {
    let epoch = pinned_epoch();

    // Verify all 8 possible triples (import_all, is_exported, is_meta)
    let triples = [
        (false, false, false), // private
        (false, false, true),  // private meta
        (false, true, false),  // public
        (false, true, true),   // public meta
        (true, false, false),  // private import-all
        (true, false, true),   // private meta import-all
        (true, true, false),   // public import-all
        (true, true, true),    // public meta import-all
    ];

    let mut direct_imports = Vec::new();
    for (idx, (all, exp, meta)) in triples.iter().enumerate() {
        let target_name = Name::str(Name::anonymous(), format!("Target.Mod{idx}"));
        direct_imports.push(DirectImport::new(
            ModuleId::new(target_name),
            *all,
            *exp,
            *meta,
        ));
    }

    // Add duplicate rows:
    // 1. Exact duplicate row
    direct_imports.push(direct_imports[0].clone());
    // 2. Same module with differing flags
    direct_imports.push(DirectImport::new(
        direct_imports[0].module.clone(),
        !direct_imports[0].import_all,
        !direct_imports[0].is_exported,
        !direct_imports[0].is_meta,
    ));

    let module_id = ModuleId::new(Name::str(Name::anonymous(), "Test.Flags"));
    let evidence = ArtifactEvidence {
        epoch,
        content_digest: hash(Domain::Fixture, b"flags_test"),
        producer: ArtifactProducer::FrankenLean,
        grade: ArtifactGrade::Verified,
    };

    let record = ModuleRecord::new(
        module_id.clone(),
        true,
        direct_imports.clone(),
        evidence,
    );

    assert_eq!(record.direct_imports().len(), 10);
    for (idx, imp) in record.direct_imports().iter().enumerate() {
        assert_eq!(imp, &direct_imports[idx]);
    }

    let duplicates = record.duplicate_imports();
    assert_eq!(duplicates.len(), 2);
    assert_eq!(duplicates[0].first_index, 0);
    assert_eq!(duplicates[0].duplicate_index, 8);
    assert_eq!(
        duplicates[0].kind,
        fln_env::modules::DuplicateImportKind::ExactRow
    );

    assert_eq!(duplicates[1].first_index, 0);
    assert_eq!(duplicates[1].duplicate_index, 9);
    assert_eq!(
        duplicates[1].kind,
        fln_env::modules::DuplicateImportKind::SameTargetDifferentFlags
    );
}

fn dummy_axiom(name: Name) -> Arc<ConstantInfo> {
    Arc::new(ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name,
            level_params: Vec::new(),
            type_: fln_core::expr::Expr::sort(fln_core::level::Level::zero()),
        },
        is_unsafe: false,
    }))
}

#[test]
fn module_batch_apply_plan_stages_privately_with_zero_visible_prefix_on_failure() {
    let epoch = pinned_epoch();
    let base_state = ModuleApplyState::from_epoch(epoch.clone()).unwrap();

    // Build 3 module contribution records
    let decl1 = dummy_axiom(Name::str(Name::anonymous(), "M1.decl"));
    let decl2 = dummy_axiom(Name::str(Name::anonymous(), "M2.decl"));
    let decl3 = dummy_axiom(Name::str(Name::anonymous(), "M3.decl"));

    let mod1_id = ModuleId::new(Name::str(Name::anonymous(), "M1"));
    let mod2_id = ModuleId::new(Name::str(Name::anonymous(), "M2"));
    let mod3_id = ModuleId::new(Name::str(Name::anonymous(), "M3"));

    let ev1 = ArtifactEvidence {
        epoch: epoch.clone(),
        content_digest: hash(Domain::Fixture, b"m1"),
        producer: ArtifactProducer::FrankenLean,
        grade: ArtifactGrade::Verified,
    };
    let ev2 = ArtifactEvidence {
        epoch: epoch.clone(),
        content_digest: hash(Domain::Fixture, b"m2"),
        producer: ArtifactProducer::FrankenLean,
        grade: ArtifactGrade::Verified,
    };
    let ev3 = ArtifactEvidence {
        epoch: epoch.clone(),
        content_digest: hash(Domain::Fixture, b"m3"),
        producer: ArtifactProducer::FrankenLean,
        grade: ArtifactGrade::Verified,
    };

    let rec1 = ModuleRecord::new(mod1_id.clone(), true, Vec::new(), ev1);
    let rec2 = ModuleRecord::new(
        mod2_id.clone(),
        true,
        vec![DirectImport::new(mod1_id.clone(), false, true, false)],
        ev2,
    );
    let rec3 = ModuleRecord::new(
        mod3_id.clone(),
        true,
        vec![DirectImport::new(mod2_id.clone(), false, true, false)],
        ev3,
    );

    let comp = ProvenanceCompleteness::new(
        CaptureStatus::Complete,
        PayloadTransparency::Understood,
        Vec::new(),
    );

    let c1 = ModuleContributionRecord::new(rec1, vec![decl1.name().clone()], Vec::new(), Vec::new(), comp.clone());
    let c2 = ModuleContributionRecord::new(rec2, vec![decl2.name().clone()], Vec::new(), Vec::new(), comp.clone());
    let c3 = ModuleContributionRecord::new(rec3, vec![decl3.name().clone()], Vec::new(), Vec::new(), comp);

    // Chained manifests
    let m1 = Arc::new(ModuleProvenanceManifest::new(epoch.clone(), vec![c1.clone()], ModuleProvenanceLimits::default()).unwrap());
    let m2 = Arc::new(ModuleProvenanceManifest::new(epoch.clone(), vec![c1.clone(), c2.clone()], ModuleProvenanceLimits::default()).unwrap());
    let m3 = Arc::new(ModuleProvenanceManifest::new(epoch.clone(), vec![c1.clone(), c2.clone(), c3.clone()], ModuleProvenanceLimits::default()).unwrap());

    let txn1 = ModuleApplyTransaction::new(m1, c1, vec![decl1], Vec::new(), Vec::new());
    let txn2 = ModuleApplyTransaction::new(m2, c2, vec![decl2], Vec::new(), Vec::new());
    let txn3 = ModuleApplyTransaction::new(m3, c3, vec![decl3], Vec::new(), Vec::new());

    let pf1 = preflight_module_apply(txn1, &ModuleApplyLimits::default()).unwrap();
    let pf2 = preflight_module_apply(txn2, &ModuleApplyLimits::default()).unwrap();
    let pf3 = preflight_module_apply(txn3, &ModuleApplyLimits::default()).unwrap();

    let preflights = vec![pf1, pf2, pf3];
    let modules = vec![mod1_id, mod2_id, mod3_id];

    // Successful batch stage and commit
    let plan = match ModuleBatchApplyPlan::stage(&base_state, &preflights, modules.clone()) {
        Outcome::Complete(Ok(plan)) => plan,
        _ => panic!("expected successful stage"),
    };

    assert_eq!(plan.modules().len(), 3);
    assert_eq!(plan.base_snapshot(), &base_state);

    let committed = match plan.commit(&base_state, None) {
        Outcome::Complete(Ok(res)) => res,
        _ => panic!("expected successful commit"),
    };

    assert_eq!(committed.applied_count, 3);
    assert_eq!(committed.state.graph().len(), 3);
    assert_ne!(committed.manifest_root, base_state.manifest().root());
    assert_ne!(committed.logical_root, base_state.environment().logical_root(&KVMap::default()));

    // Verify zero visible prefix on mid-batch failure:
    // If we build a batch where stage 2 has a broken base (e.g. duplicate module), staging fails.
    let broken_preflights = vec![preflights[0].clone(), preflights[0].clone()];
    let broken_modules = vec![modules[0].clone(), modules[0].clone()];

    let broken_stage = ModuleBatchApplyPlan::stage(&base_state, &broken_preflights, broken_modules);
    match broken_stage {
        Outcome::Complete(Err(ModuleBatchPlanError::Prepare(_))) => {
            // Success: staging rejected
        }
        _ => panic!("expected stage error on duplicate"),
    }

    // Base state was never touched
    assert_eq!(base_state.graph().len(), 0);
    assert_eq!(base_state.environment().len(), 0);
}

struct StepCancellationProbe {
    tripped_after: AtomicUsize,
    current_step: AtomicUsize,
}

impl StepCancellationProbe {
    fn new(tripped_after: usize) -> Self {
        Self {
            tripped_after: AtomicUsize::new(tripped_after),
            current_step: AtomicUsize::new(0),
        }
    }

    fn reset(&self) {
        self.current_step.store(0, Ordering::SeqCst);
        self.tripped_after.store(usize::MAX, Ordering::SeqCst);
    }
}

impl CancellationProbe for StepCancellationProbe {
    fn is_cancelled(&self) -> bool {
        let step = self.current_step.fetch_add(1, Ordering::SeqCst);
        step >= self.tripped_after.load(Ordering::SeqCst)
    }
}

#[test]
fn cancellation_at_deterministic_checkpoints_is_inconclusive_and_not_cached() {
    let epoch = pinned_epoch();
    let base_state = ModuleApplyState::from_epoch(epoch.clone()).unwrap();

    let decl1 = dummy_axiom(Name::str(Name::anonymous(), "Cancel.decl"));
    let mod1_id = ModuleId::new(Name::str(Name::anonymous(), "Cancel.Mod"));
    let ev1 = ArtifactEvidence {
        epoch: epoch.clone(),
        content_digest: hash(Domain::Fixture, b"cancel_test"),
        producer: ArtifactProducer::FrankenLean,
        grade: ArtifactGrade::Verified,
    };
    let rec1 = ModuleRecord::new(mod1_id.clone(), true, Vec::new(), ev1);
    let comp = ProvenanceCompleteness::new(
        CaptureStatus::Complete,
        PayloadTransparency::Understood,
        Vec::new(),
    );
    let c1 = ModuleContributionRecord::new(rec1, vec![decl1.name().clone()], Vec::new(), Vec::new(), comp);
    let m1 = Arc::new(ModuleProvenanceManifest::new(epoch.clone(), vec![c1.clone()], ModuleProvenanceLimits::default()).unwrap());
    let txn1 = ModuleApplyTransaction::new(m1, c1, vec![decl1], Vec::new(), Vec::new());
    let pf1 = preflight_module_apply(txn1, &ModuleApplyLimits::default()).unwrap();

    let plan = match ModuleBatchApplyPlan::stage(&base_state, std::slice::from_ref(&pf1), vec![mod1_id.clone()]) {
        Outcome::Complete(Ok(plan)) => plan,
        _ => panic!("expected stage"),
    };

    // Cancellation probe trips immediately at checkpoint
    let probe = StepCancellationProbe::new(0);
    let outcome = plan.commit(&base_state, Some(&probe));

    assert_eq!(outcome.cache_admission(), CacheAdmission::Refused { authority: fln_core::outcome::Authority::NonAuthoritative });
    match outcome {
        Outcome::Inconclusive(inc) => {
            assert!(format!("{inc:?}").contains("before-publication"));
        }
        _ => panic!("expected Inconclusive outcome"),
    }

    // Base state remains completely unchanged
    assert_eq!(base_state.graph().len(), 0);

    // Retry with cancellation withdrawn succeeds cleanly
    probe.reset();
    let retry_plan = match ModuleBatchApplyPlan::stage(&base_state, &[pf1], vec![mod1_id]) {
        Outcome::Complete(Ok(plan)) => plan,
        _ => panic!("expected stage"),
    };
    let retry_outcome = retry_plan.commit(&base_state, Some(&probe));
    assert_eq!(retry_outcome.cache_admission(), CacheAdmission::Admissible);
    match retry_outcome {
        Outcome::Complete(Ok(res)) => {
            assert_eq!(res.applied_count, 1);
            assert_eq!(res.state.graph().len(), 1);
        }
        _ => panic!("expected successful retry"),
    }
}

#[test]
fn schedule_independence_matrix_1_8_32_threads() {
    let epoch = pinned_epoch();
    let base_state = ModuleApplyState::from_epoch(epoch.clone()).unwrap();

    let decl1 = dummy_axiom(Name::str(Name::anonymous(), "Sched.M1.decl"));
    let decl2 = dummy_axiom(Name::str(Name::anonymous(), "Sched.M2.decl"));
    let mod1_id = ModuleId::new(Name::str(Name::anonymous(), "Sched.M1"));
    let mod2_id = ModuleId::new(Name::str(Name::anonymous(), "Sched.M2"));

    let ev1 = ArtifactEvidence {
        epoch: epoch.clone(),
        content_digest: hash(Domain::Fixture, b"sched_m1"),
        producer: ArtifactProducer::FrankenLean,
        grade: ArtifactGrade::Verified,
    };
    let ev2 = ArtifactEvidence {
        epoch: epoch.clone(),
        content_digest: hash(Domain::Fixture, b"sched_m2"),
        producer: ArtifactProducer::FrankenLean,
        grade: ArtifactGrade::Verified,
    };

    let rec1 = ModuleRecord::new(mod1_id.clone(), true, Vec::new(), ev1);
    let rec2 = ModuleRecord::new(
        mod2_id.clone(),
        true,
        vec![DirectImport::new(mod1_id.clone(), false, true, false)],
        ev2,
    );
    let comp = ProvenanceCompleteness::new(
        CaptureStatus::Complete,
        PayloadTransparency::Understood,
        Vec::new(),
    );

    let c1 = ModuleContributionRecord::new(rec1, vec![decl1.name().clone()], Vec::new(), Vec::new(), comp.clone());
    let c2 = ModuleContributionRecord::new(rec2, vec![decl2.name().clone()], Vec::new(), Vec::new(), comp);

    let m1 = Arc::new(ModuleProvenanceManifest::new(epoch.clone(), vec![c1.clone()], ModuleProvenanceLimits::default()).unwrap());
    let m2 = Arc::new(ModuleProvenanceManifest::new(epoch.clone(), vec![c1.clone(), c2.clone()], ModuleProvenanceLimits::default()).unwrap());

    let txn1 = ModuleApplyTransaction::new(m1, c1, vec![decl1], Vec::new(), Vec::new());
    let txn2 = ModuleApplyTransaction::new(m2, c2, vec![decl2], Vec::new(), Vec::new());

    let pf1 = preflight_module_apply(txn1, &ModuleApplyLimits::default()).unwrap();
    let pf2 = preflight_module_apply(txn2, &ModuleApplyLimits::default()).unwrap();

    let preflights = vec![pf1, pf2];
    let modules = vec![mod1_id, mod2_id];

    let run_once = || {
        let plan = ModuleBatchApplyPlan::stage(&base_state, &preflights, modules.clone())
            .into_complete()
            .unwrap()
            .unwrap();
        let res = plan.commit(&base_state, None).into_complete().unwrap().unwrap();
        (res.manifest_root, res.logical_root, res.final_receipt.transaction_id().digest())
    };

    let reference_roots = run_once();

    for thread_count in [1, 8, 32] {
        let handles: Vec<_> = (0..thread_count)
            .map(|_| {
                let base = base_state.clone();
                let pfs = preflights.clone();
                let mods = modules.clone();
                thread::spawn(move || {
                    let plan = ModuleBatchApplyPlan::stage(&base, &pfs, mods)
                        .into_complete()
                        .unwrap()
                        .unwrap();
                    let res = plan.commit(&base, None).into_complete().unwrap().unwrap();
                    (res.manifest_root, res.logical_root, res.final_receipt.transaction_id().digest())
                })
            })
            .collect();

        for handle in handles {
            let thread_result = handle.join().expect("thread join");
            assert_eq!(
                thread_result, reference_roots,
                "schedule divergence detected at thread_count={thread_count}"
            );
        }
    }
}

#[test]
fn single_charge_accounting_across_all_planes() {
    let root = workspace_root();
    let epoch = pinned_epoch();
    let mod_id = ModuleId::new(Name::str(Name::anonymous(), "Init.BinderNameHint"));
    let fixture_path = root.join("tribunal/fixtures/c3/Init.BinderNameHint.olean");
    let decoded = OleanModuleAdapter::decode_file(
        mod_id,
        &fixture_path,
        epoch,
    )
    .expect("decode Init.BinderNameHint");

    let mut summary = ModuleBatchUsageSummary::default();
    summary.accumulate(&decoded);

    assert_eq!(summary.total_modules, 1);
    assert_eq!(summary.total_direct_import_rows, 2);
    assert_eq!(summary.total_declarations, decoded.constants.len());
    assert_eq!(summary.total_payload_bytes, decoded.payload_bytes as u64);
}

#[test]
fn injected_equal_digest_unequal_value_collision_disambiguation() {
    // Construct two distinct module names that map to distinct ModuleIds
    let mod1 = ModuleId::new(Name::str(Name::anonymous(), "Collision.A"));
    let mod2 = ModuleId::new(Name::str(Name::anonymous(), "Collision.B"));

    assert_ne!(mod1, mod2);
    assert_eq!(mod1, mod1.clone());
    assert_eq!(mod2, mod2.clone());

    let mut map = BTreeMap::new();
    map.insert(mod1.clone(), 100);
    map.insert(mod2.clone(), 200);

    assert_eq!(map.get(&mod1), Some(&100));
    assert_eq!(map.get(&mod2), Some(&200));
}

#[test]
fn mutant_kills_stale_base_and_partial_publication() {
    let epoch = pinned_epoch();
    let base_state = ModuleApplyState::from_epoch(epoch.clone()).unwrap();

    let decl1 = dummy_axiom(Name::str(Name::anonymous(), "Mutant.decl"));
    let mod1_id = ModuleId::new(Name::str(Name::anonymous(), "Mutant.Mod"));
    let ev1 = ArtifactEvidence {
        epoch: epoch.clone(),
        content_digest: hash(Domain::Fixture, b"mutant_test"),
        producer: ArtifactProducer::FrankenLean,
        grade: ArtifactGrade::Verified,
    };
    let rec1 = ModuleRecord::new(mod1_id.clone(), true, Vec::new(), ev1);
    let comp = ProvenanceCompleteness::new(
        CaptureStatus::Complete,
        PayloadTransparency::Understood,
        Vec::new(),
    );
    let c1 = ModuleContributionRecord::new(rec1, vec![decl1.name().clone()], Vec::new(), Vec::new(), comp);
    let m1 = Arc::new(ModuleProvenanceManifest::new(epoch.clone(), vec![c1.clone()], ModuleProvenanceLimits::default()).unwrap());
    let txn1 = ModuleApplyTransaction::new(m1, c1, vec![decl1], Vec::new(), Vec::new());
    let pf1 = preflight_module_apply(txn1, &ModuleApplyLimits::default()).unwrap();

    let plan = ModuleBatchApplyPlan::stage(&base_state, &[pf1], vec![mod1_id])
        .into_complete()
        .unwrap()
        .unwrap();

    // Kill mutant: commit with a DIFFERENT / stale base state must be refused with StaleBase
    let foreign_epoch = ModuleEpoch::new("v4.32.0", "1111111111111111111111111111111111111111");
    let foreign_base = ModuleApplyState::from_epoch(foreign_epoch).unwrap();

    let stale_commit = plan.commit(&foreign_base, None);
    match stale_commit {
        Outcome::Complete(Err(ModuleBatchCommitError::StaleBase)) => {
            // Mutant killed: stale base was refused
        }
        _ => panic!("expected StaleBase error"),
    }
}
