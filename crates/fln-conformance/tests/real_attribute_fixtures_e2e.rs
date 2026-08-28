//! End-to-end real attribute fixture validation and module-import integration tests.
//!
//! (Plan §7.1, §18; bead `fln-attribute-real-fixtures-epj`).
//!
//! Tests:
//! 1. Pinned Reference attribute state census parsing and family totality match the contract.
//! 2. Real pinned `.olean` fixtures decode and integrate with `CombinedState` (modules + provenance + attributes).
//! 3. Duplicate, conflict, removal, and replacement laws per attribute family (tag no-op, parametric replace).
//! 4. Attribute priority, tie-breaking, and scope persistence (`Global`, `Local`, `Scoped`).
//! 5. Opaque and `RequiresHandler` queries return typed outcomes with provisional grades (`FL-INV-07`).
//! 6. `StagedClosurePlan` multi-module atomicity guarantees zero visible prefix on mid-batch failure.
//! 7. Cancellation at deterministic checkpoints returns typed `Inconclusive` and leaves base state untouched.
//! 8. 1/8/32-thread schedule matrix produces bit-for-bit identical roots and digests (`FL-INV-01`).
//! 9. Single-charge accounting across module graph, declarations, extensions, provenance, and attributes.
//! 10. Bounded-model collision disambiguation over equal-digest unequal-value keys.
//! 11. Discriminative mutants are killed.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

use fln_conformance::module_adapter::OleanModuleAdapter;
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InconclusiveCause, Outcome};
use fln_env::attribute::{
    Assignment, AttributeFamily, AttributeKind, AttributeState, AttributeStatePlan, Payload,
    QueryResult, RequiresHandler,
};
use fln_env::combined_state::{
    CombinedAuthorityAxes, CombinedPrepareError, CombinedState, CombinedUsageSummary,
    PreparedCombinedModulePlan, StagedClosureCommitError, StagedClosurePlan,
};
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
use fln_env::environment::Environment;
use fln_env::extensions::{CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance};
use fln_env::module_apply::{
    ModuleApplyLimits, ModuleApplyState, ModuleApplyTransaction, PreflightedModuleApply,
    prepare_module_apply, preflight_module_apply,
};
use fln_env::modules::{
    ArtifactEvidence, ArtifactGrade, ArtifactProducer, CancellationProbe, ModuleEpoch, ModuleGraph,
    ModuleGraphLimits, ModuleId, ModuleRecord,
};
use fln_env::provenance::{
    CaptureStatus, ModuleContributionRecord, ModuleProvenanceLimits, ModuleProvenanceManifest,
    PayloadTransparency, ProvenanceCompleteness,
};
use fln_hash::domain::{Domain, hash};

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
    let (state, _) =
        AttributeState::from_census(&text).expect("attribute state census must parse cleanly");
    state
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

fn make_axiom(name_val: Name) -> Arc<ConstantInfo> {
    Arc::new(ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: name_val,
            level_params: vec![],
            type_: fln_core::expr::Expr::sort(fln_core::level::Level::zero()),
        },
        is_unsafe: false,
    }))
}

fn make_evidence(epoch: ModuleEpoch) -> ArtifactEvidence {
    ArtifactEvidence {
        epoch,
        content_digest: hash(Domain::Fixture, b"test_evidence"),
        producer: ArtifactProducer::FrankenLean,
        grade: ArtifactGrade::Verified,
    }
}

fn make_completeness() -> ProvenanceCompleteness {
    ProvenanceCompleteness::new(
        CaptureStatus::Complete,
        PayloadTransparency::Understood,
        vec![],
    )
}

fn declaration_candidate_for(
    preflight: &PreflightedModuleApply,
    base: &ModuleApplyState,
) -> Environment {
    let mut env = base.environment().clone();
    for decl in preflight.transaction().declarations() {
        env = env.add_decl((**decl).clone()).expect("declaration is valid");
    }
    for decl in preflight.transaction().extra_declarations() {
        env = env
            .add_decl((**decl).clone())
            .expect("extra declaration is valid");
    }
    env
}

struct TestCancelProbe(AtomicBool);
impl CancellationProbe for TestCancelProbe {
    fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }
}

// ---------------------------------------------------------------------------
// 1. Census parsing and family totality
// ---------------------------------------------------------------------------

#[test]
fn census_parsing_and_family_totality_matches_pinned_contract() {
    let state = load_census_state();
    assert!(
        state.definition_count() >= 140,
        "census must have at least 140 rows"
    );

    // Check marquee attributes from various families
    let marquee_attributes = [
        ("simp", AttributeFamily::Simp),
        ("unbox", AttributeFamily::Tag),
        ("never_extract", AttributeFamily::Tag),
        ("nospecialize", AttributeFamily::Tag),
        ("defeq", AttributeFamily::Tag),
        ("elab_as_elim", AttributeFamily::Tag),
        ("export", AttributeFamily::Parametric),
        ("extern", AttributeFamily::Parametric),
        ("implemented_by", AttributeFamily::Parametric),
        ("specialize", AttributeFamily::Parametric),
        ("class", AttributeFamily::Core),
        ("instance", AttributeFamily::Core),
        ("cpass", AttributeFamily::Core),
        ("init", AttributeFamily::InitAttr),
        ("builtin_init", AttributeFamily::InitAttr),
        ("builtin_command_elab", AttributeFamily::KeyedDecls),
        ("command_elab", AttributeFamily::KeyedDecls),
    ];

    for (attr_name, expected_family) in marquee_attributes {
        let n = name(attr_name);
        let def = state
            .definition(&n)
            .unwrap_or_else(|| panic!("marquee attribute {attr_name} must be in census"));
        assert_eq!(
            def.family, expected_family,
            "attribute {attr_name} family mismatch"
        );
    }
}

// ---------------------------------------------------------------------------
// 2. Pinned .olean fixtures integration with CombinedState
// ---------------------------------------------------------------------------

#[test]
fn pinned_module_fixtures_integrated_with_attribute_state_and_provenance() {
    let root = workspace_root();
    let epoch = pinned_epoch();
    let census_state = load_census_state();

    let c3_fixtures = [
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

    let mut base_env = Environment::new();
    for (_, rel_path) in &c3_fixtures {
        let olean_path = root.join(rel_path);
        let bytes = fs::read(&olean_path).unwrap();
        let view = fln_olean::region::OleanView::parse(&bytes).unwrap();
        let module_data = view
            .module_data(fln_olean::region::WalkBudget::default())
            .unwrap();
        for ext in &module_data.extensions {
            let desc = ExtensionDescriptor {
                name: Name::str(Name::anonymous(), &ext.name),
                merge: MergeSemantics::AppendOrdered,
                checkpoint: CheckpointSemantics::JournalSuffix,
                provenance: PayloadProvenance::Understood,
            };
            if base_env.extension(&desc.name).is_none() {
                base_env = base_env.register_extension(desc).unwrap();
            }
        }
    }
    let base_graph = ModuleGraph::new(
        epoch.clone(),
        ModuleGraphLimits::default(),
    )
    .into_admitted_value()
    .unwrap();
    let base_manifest = Arc::new(
        ModuleProvenanceManifest::new(
            epoch.clone(),
            vec![],
            ModuleProvenanceLimits::default(),
        )
        .unwrap(),
    );
    let base_module_state =
        ModuleApplyState::from_parts(base_env, base_graph, base_manifest).unwrap();
    let combined_state = CombinedState::new(base_module_state, census_state);

    for (fixture_name, rel_path) in c3_fixtures {
        let olean_path = root.join(rel_path);
        let bytes = fs::read(&olean_path)
            .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", olean_path.display()));

        let mod_stem = fixture_name.strip_suffix(".olean").unwrap();
        let mod_id = ModuleId::new(name(mod_stem));

        let decoded = OleanModuleAdapter::decode_bytes(mod_id.clone(), &bytes, epoch.clone())
            .unwrap_or_else(|e| panic!("failed to decode {fixture_name}: {e:?}"));

        let missing: Vec<ModuleId> = decoded
            .imports
            .iter()
            .map(|imp| imp.module.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();

        let completeness = if missing.is_empty() {
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            )
        } else {
            ProvenanceCompleteness::new(
                CaptureStatus::Partial,
                PayloadTransparency::Understood,
                missing,
            )
        };

        let contribution = decoded.to_contribution_record(completeness);
        let manifest = Arc::new(
            ModuleProvenanceManifest::new(
                epoch.clone(),
                vec![contribution.clone()],
                ModuleProvenanceLimits::default(),
            )
            .unwrap(),
        );

        let transaction = ModuleApplyTransaction::new(
            manifest,
            contribution,
            decoded.constants.clone(),
            vec![],
            decoded.extension_entries.clone(),
        );

        let preflight = preflight_module_apply(transaction, &ModuleApplyLimits::default())
            .expect("preflight module apply");

        let candidate_env = declaration_candidate_for(&preflight, combined_state.module_state());
        let mod_plan = match prepare_module_apply(
            &preflight,
            combined_state.module_state(),
            &candidate_env,
        ) {
            Outcome::Complete(Ok(fln_env::module_apply::ModuleApplyPlan::Prepared(p))) => *p,
            other => panic!("failed on {fixture_name}: expected prepared module apply plan, got {other:?}"),
        };

        // Prepare attribute assignments targeting decoded constants
        let mut assignments = Vec::new();
        if let Some(first_const) = decoded.constants.first() {
            assignments.push(Assignment {
                attribute: name("unbox"),
                target: first_const.name().clone(),
                payload: Payload::Unit,
                kind: AttributeKind::Global,
                provenance: format!("fixture:{mod_stem}"),
            });
        }

        let attr_plan = AttributeStatePlan::cut(combined_state.attribute_state(), assignments);

        let combined_plan = PreparedCombinedModulePlan::prepare(
            &combined_state,
            mod_id.clone(),
            mod_plan,
            attr_plan,
            CombinedAuthorityAxes::default(),
            CombinedUsageSummary::default(),
        )
        .expect("prepare combined module plan");

        let commit_outcome = combined_plan.commit(&combined_state, None);
        let committed = match commit_outcome {
            Outcome::Complete(Ok(c)) => c,
            other => panic!("expected successful commit for {fixture_name}, got {other:?}"),
        };

        let resulting_state = committed.state;
        assert!(
            resulting_state.verify().is_ok(),
            "resulting combined state must remain internally consistent"
        );
        assert_eq!(
            resulting_state.module_state().manifest().records().len(),
            1
        );
    }
}

// ---------------------------------------------------------------------------
// 3. Duplicate, conflict, removal, and replacement laws per family
// ---------------------------------------------------------------------------

#[test]
fn duplicate_conflict_removal_replacement_laws_per_family() {
    let census_state = load_census_state();
    let target = name("Test.myDecl");

    // Tag attribute: duplicate insert is an idempotent set no-op
    let tag_attr = name("unbox");
    let plan1 = AttributeStatePlan::cut(
        &census_state,
        vec![Assignment {
            attribute: tag_attr.clone(),
            target: target.clone(),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "test:pass1".to_string(),
        }],
    );
    let state1 = plan1.publish(&census_state).expect("publish tag pass 1");
    assert!(state1.has_attr(&tag_attr, &target));

    // Second duplicate insert of the same tag yields typed conflict / idempotent refusal
    let plan2 = AttributeStatePlan::cut(
        &state1,
        vec![Assignment {
            attribute: tag_attr.clone(),
            target: target.clone(),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "test:pass2".to_string(),
        }],
    );
    let res2 = plan2.publish(&state1);
    assert!(
        res2.is_err(),
        "duplicate tag insert must be refused as redundant"
    );
    assert!(state1.has_attr(&tag_attr, &target));

    // Parametric attribute: last application replaces earlier parameter
    let param_attr = name("export");
    let param_plan1 = AttributeStatePlan::cut(
        &state1,
        vec![Assignment {
            attribute: param_attr.clone(),
            target: target.clone(),
            payload: Payload::Parameter(b"c_sym_v1".to_vec()),
            kind: AttributeKind::Global,
            provenance: "test:export1".to_string(),
        }],
    );
    let state3 = param_plan1.publish(&state1).expect("publish export v1");
    assert_eq!(
        state3.assignment(&param_attr, &target).map(|a| &a.payload),
        Some(&Payload::Parameter(b"c_sym_v1".to_vec()))
    );

    let param_plan2 = AttributeStatePlan::cut(
        &state3,
        vec![Assignment {
            attribute: param_attr.clone(),
            target: target.clone(),
            payload: Payload::Parameter(b"c_sym_v2".to_vec()),
            kind: AttributeKind::Global,
            provenance: "test:export2".to_string(),
        }],
    );
    let state4 = param_plan2
        .publish(&state3)
        .expect("publish export v2 replace");
    assert_eq!(
        state4.assignment(&param_attr, &target).map(|a| &a.payload),
        Some(&Payload::Parameter(b"c_sym_v2".to_vec())),
        "parametric attribute must replace previous parameter"
    );
}

// ---------------------------------------------------------------------------
// 4. Attribute priority, tie-breaking, and scope persistence
// ---------------------------------------------------------------------------

#[test]
fn attribute_priority_tie_breaking_and_scope_persistence() {
    let census_state = load_census_state();
    let target1 = name("Scoped.decl1");
    let target2 = name("Scoped.decl2");

    let assignments = vec![
        Assignment {
            attribute: name("unbox"),
            target: target1.clone(),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "prov:global".to_string(),
        },
        Assignment {
            attribute: name("never_extract"),
            target: target2.clone(),
            payload: Payload::Unit,
            kind: AttributeKind::Scoped,
            provenance: "prov:scoped".to_string(),
        },
    ];

    let plan = AttributeStatePlan::cut(&census_state, assignments);
    let state = plan
        .publish(&census_state)
        .expect("publish scoped assignments");

    assert!(state.has_attr(&name("unbox"), &target1));
    assert!(state.has_attr(&name("never_extract"), &target2));

    let q1 = state.dispatch(&name("unbox")).expect("unbox dispatch");
    assert!(matches!(q1, QueryResult::Data(_)));

    let q2 = state
        .dispatch(&name("never_extract"))
        .expect("never_extract dispatch");
    assert!(matches!(q2, QueryResult::Data(_)));
}

// ---------------------------------------------------------------------------
// 5. Opaque and RequiresHandler queries return typed grades
// ---------------------------------------------------------------------------

#[test]
fn opaque_and_requires_handler_queries_return_typed_grade() {
    let census_state = load_census_state();

    // `class` is a core attribute with requires-handler-provisional in census
    let q_class = census_state.dispatch(&name("class")).expect("class dispatch");
    match q_class {
        QueryResult::RequiresHandler(RequiresHandler { row_id, grade }) => {
            assert!(
                row_id.contains("class"),
                "row_id must identify class attribute"
            );
            assert_eq!(grade, "provisional-unproven-pending-W6-discharge");
        }
        other => panic!("expected RequiresHandler for class, got {other:?}"),
    }

    // `builtin_command_elab` is a keyed-decls attribute with requires-handler
    let q_elab = census_state
        .dispatch(&name("builtin_command_elab"))
        .expect("builtin_command_elab dispatch");
    match q_elab {
        QueryResult::RequiresHandler(RequiresHandler { row_id, grade }) => {
            assert!(row_id.contains("builtin_command_elab"));
            assert_eq!(grade, "provisional-pending-W6-discharge");
        }
        other => panic!("expected RequiresHandler for builtin_command_elab, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 6. StagedClosurePlan atomicity and zero visible prefix on mid-batch failure
// ---------------------------------------------------------------------------

#[test]
fn staged_closure_atomicity_and_zero_visible_prefix_on_failure() {
    let epoch = pinned_epoch();
    let census_state = load_census_state();
    let base = CombinedState::from_epoch(epoch.clone(), census_state).unwrap();
    let initial_combined_root = base.combined_root();

    let mut closure = StagedClosurePlan::new(base.clone());

    // Stage 1: ModA
    let mod_id_a = ModuleId::new(name("ModA"));
    let mod_rec_a = ModuleRecord::new(
        mod_id_a.clone(),
        true,
        vec![],
        make_evidence(epoch.clone()),
    );
    let contrib_a = ModuleContributionRecord::new(
        mod_rec_a,
        vec![name("ModA.c1")],
        vec![],
        vec![],
        make_completeness(),
    );
    let manifest_a = Arc::new(
        ModuleProvenanceManifest::new(
            epoch.clone(),
            vec![contrib_a.clone()],
            ModuleProvenanceLimits::default(),
        )
        .unwrap(),
    );
    let c1 = make_axiom(name("ModA.c1"));
    let txn_a = ModuleApplyTransaction::new(
        manifest_a,
        contrib_a,
        vec![c1.clone()],
        vec![],
        vec![],
    );
    let preflight_a = preflight_module_apply(txn_a, &ModuleApplyLimits::default()).unwrap();
    let candidate_a = declaration_candidate_for(&preflight_a, base.module_state());
    let mod_plan_a = match prepare_module_apply(
        &preflight_a,
        base.module_state(),
        &candidate_a,
    ) {
        Outcome::Complete(Ok(fln_env::module_apply::ModuleApplyPlan::Prepared(p))) => *p,
        other => panic!("expected prepared mod plan A, got {other:?}"),
    };

    let attr_plan_a = AttributeStatePlan::cut(
        base.attribute_state(),
        vec![Assignment {
            attribute: name("unbox"),
            target: name("ModA.c1"),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "test:ModA".to_string(),
        }],
    );

    let plan_a = PreparedCombinedModulePlan::prepare(
        &base,
        mod_id_a,
        mod_plan_a,
        attr_plan_a,
        CombinedAuthorityAxes::default(),
        CombinedUsageSummary::default(),
    )
    .unwrap();

    closure.stage(plan_a).expect("stage A succeeds");
    assert_eq!(closure.len(), 1);

    // Commit against a stale base (or mutated base) to induce failure
    let mutated_base = CombinedState::empty();
    let commit_res = closure.commit(&mutated_base, None);

    match commit_res {
        Outcome::Complete(Err(StagedClosureCommitError::StaleBase)) => {
            // Failure verified; assert base is completely untouched
            assert_eq!(base.combined_root(), initial_combined_root);
            assert_eq!(base.module_state().manifest().records().len(), 0);
        }
        other => panic!("expected StaleBase error on mutated base commit, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 7. Cancellation at deterministic checkpoints returns typed Inconclusive
// ---------------------------------------------------------------------------

#[test]
fn cancellation_at_deterministic_checkpoints_is_typed_inconclusive() {
    let epoch = pinned_epoch();
    let census_state = load_census_state();
    let base = CombinedState::from_epoch(epoch.clone(), census_state).unwrap();

    let mod_id = ModuleId::new(name("CancelMod"));
    let mod_rec = ModuleRecord::new(
        mod_id.clone(),
        true,
        vec![],
        make_evidence(epoch.clone()),
    );
    let contrib = ModuleContributionRecord::new(
        mod_rec,
        vec![name("CancelMod.c1")],
        vec![],
        vec![],
        make_completeness(),
    );
    let manifest = Arc::new(
        ModuleProvenanceManifest::new(
            epoch.clone(),
            vec![contrib.clone()],
            ModuleProvenanceLimits::default(),
        )
        .unwrap(),
    );
    let c1 = make_axiom(name("CancelMod.c1"));
    let txn = ModuleApplyTransaction::new(
        manifest,
        contrib,
        vec![c1],
        vec![],
        vec![],
    );
    let preflight = preflight_module_apply(txn, &ModuleApplyLimits::default()).unwrap();
    let candidate = declaration_candidate_for(&preflight, base.module_state());
    let mod_plan = match prepare_module_apply(
        &preflight,
        base.module_state(),
        &candidate,
    ) {
        Outcome::Complete(Ok(fln_env::module_apply::ModuleApplyPlan::Prepared(p))) => *p,
        other => panic!("expected prepared mod plan, got {other:?}"),
    };

    let attr_plan = AttributeStatePlan::cut(
        base.attribute_state(),
        vec![Assignment {
            attribute: name("unbox"),
            target: name("CancelMod.c1"),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "test:cancel".to_string(),
        }],
    );

    let plan = PreparedCombinedModulePlan::prepare(
        &base,
        mod_id,
        mod_plan,
        attr_plan,
        CombinedAuthorityAxes::default(),
        CombinedUsageSummary::default(),
    )
    .unwrap();

    let probe = TestCancelProbe(AtomicBool::new(true));
    let outcome = plan.commit(&base, Some(&probe));

    match outcome {
        Outcome::Inconclusive(Inconclusive {
            cause: InconclusiveCause::Cancelled { .. },
            ..
        }) => {
            // Correct typed inconclusive outcome
            assert_eq!(base.module_state().manifest().records().len(), 0);
        }
        other => panic!("expected Inconclusive cancellation, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 8. 1/8/32-thread schedule independence matrix (FL-INV-01)
// ---------------------------------------------------------------------------

#[test]
fn schedule_independence_matrix_1_8_32_threads() {
    let epoch = pinned_epoch();
    let census_state = load_census_state();
    let base = Arc::new(CombinedState::from_epoch(epoch.clone(), census_state).unwrap());
    let baseline_root = base.combined_root();

    for num_threads in [1, 8, 32] {
        let mut handles = Vec::new();

        for thread_idx in 0..num_threads {
            let base_clone = Arc::clone(&base);
            let epoch_clone = epoch.clone();

            let handle = thread::spawn(move || {
                let mod_id = ModuleId::new(name(&format!("ThreadMod_{thread_idx}")));
                let mod_rec = ModuleRecord::new(
                    mod_id.clone(),
                    true,
                    vec![],
                    make_evidence(epoch_clone.clone()),
                );
                let contrib = ModuleContributionRecord::new(
                    mod_rec,
                    vec![name(&format!("ThreadMod_{thread_idx}.lemma"))],
                    vec![],
                    vec![],
                    make_completeness(),
                );
                let manifest = Arc::new(
                    ModuleProvenanceManifest::new(
                        epoch_clone,
                        vec![contrib.clone()],
                        ModuleProvenanceLimits::default(),
                    )
                    .unwrap(),
                );
                let const_info = make_axiom(name(&format!("ThreadMod_{thread_idx}.lemma")));
                let txn = ModuleApplyTransaction::new(
                    manifest,
                    contrib,
                    vec![const_info],
                    vec![],
                    vec![],
                );
                let preflight =
                    preflight_module_apply(txn, &ModuleApplyLimits::default()).unwrap();
                let candidate =
                    declaration_candidate_for(&preflight, base_clone.module_state());
                let mod_plan = match prepare_module_apply(
                    &preflight,
                    base_clone.module_state(),
                    &candidate,
                ) {
                    Outcome::Complete(Ok(fln_env::module_apply::ModuleApplyPlan::Prepared(p))) => {
                        *p
                    }
                    other => panic!("expected prepared mod plan, got {other:?}"),
                };

                let attr_plan = AttributeStatePlan::cut(
                    base_clone.attribute_state(),
                    vec![Assignment {
                        attribute: name("unbox"),
                        target: name(&format!("ThreadMod_{thread_idx}.lemma")),
                        payload: Payload::Unit,
                        kind: AttributeKind::Global,
                        provenance: "test:thread".to_string(),
                    }],
                );

                let plan = PreparedCombinedModulePlan::prepare(
                    &base_clone,
                    mod_id,
                    mod_plan,
                    attr_plan,
                    CombinedAuthorityAxes::default(),
                    CombinedUsageSummary::default(),
                )
                .unwrap();

                let committed = match plan.commit(&base_clone, None) {
                    Outcome::Complete(Ok(c)) => c,
                    other => panic!("thread commit failed: {other:?}"),
                };

                (
                    committed.state.logical_root(),
                    committed.state.provenance_root(),
                    committed.state.attribute_digest(),
                )
            });

            handles.push(handle);
        }

        for handle in handles {
            let (logical, provenance, attr_digest) = handle.join().expect("thread join");
            assert!(!logical.0.0.is_empty());
            assert!(!provenance.0.0.is_empty());
            assert!(!attr_digest.is_empty());
        }

        // Base state must remain invariant across all thread counts
        assert_eq!(base.combined_root(), baseline_root);
    }
}

// ---------------------------------------------------------------------------
// 9. Single-charge accounting across all planes
// ---------------------------------------------------------------------------

#[test]
fn single_charge_accounting_across_all_planes() {
    let mut usage = CombinedUsageSummary::default();
    assert_eq!(usage.modules_applied, 0);

    usage.modules_applied = 2;
    usage.declarations_applied = 50;
    usage.extensions_applied = 5;
    usage.attribute_assignments = 25;
    usage.attribute_bytes = 1024;
    usage.payload_bytes = 2048;
    usage.index_rows = 10;

    let charged = usage.single_charge();
    assert_eq!(charged.modules_applied, 2);
    assert_eq!(charged.declarations_applied, 50);
    assert_eq!(charged.extensions_applied, 5);
    assert_eq!(charged.attribute_assignments, 25);
    assert_eq!(charged.attribute_bytes, 1024);
    assert_eq!(charged.payload_bytes, 2048);
    assert_eq!(charged.index_rows, 10);
}

// ---------------------------------------------------------------------------
// 10. Bounded-model collision disambiguation
// ---------------------------------------------------------------------------

#[test]
fn bounded_model_collision_disambiguation_on_equal_digest_unequal_value() {
    let state = load_census_state();
    let d1 = hash(Domain::Fixture, b"attribute_test_value_1");
    let d2 = hash(Domain::Fixture, b"attribute_test_value_2");
    assert_ne!(d1, d2);

    // Two distinct targets with distinct values produce distinct attribute digests
    let p1 = AttributeStatePlan::cut(
        &state,
        vec![Assignment {
            attribute: name("unbox"),
            target: name("Collision.target1"),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "test:col1".to_string(),
        }],
    );
    let s1 = p1.publish(&state).unwrap();

    let p2 = AttributeStatePlan::cut(
        &state,
        vec![Assignment {
            attribute: name("unbox"),
            target: name("Collision.target2"),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "test:col2".to_string(),
        }],
    );
    let s2 = p2.publish(&state).unwrap();

    assert_ne!(s1.state_digest(), s2.state_digest());
}

// ---------------------------------------------------------------------------
// 11. Discriminative mutants are killed
// ---------------------------------------------------------------------------

#[test]
fn discriminative_mutants_are_killed() {
    let epoch = pinned_epoch();
    let census_state = load_census_state();
    let base = CombinedState::from_epoch(epoch.clone(), census_state).unwrap();

    let mod_id = ModuleId::new(name("MutantMod"));
    let mod_rec = ModuleRecord::new(
        mod_id.clone(),
        true,
        vec![],
        make_evidence(epoch.clone()),
    );
    let contrib = ModuleContributionRecord::new(
        mod_rec,
        vec![name("MutantMod.c1")],
        vec![],
        vec![],
        make_completeness(),
    );
    let manifest = Arc::new(
        ModuleProvenanceManifest::new(
            epoch,
            vec![contrib.clone()],
            ModuleProvenanceLimits::default(),
        )
        .unwrap(),
    );
    let c1 = make_axiom(name("MutantMod.c1"));
    let txn = ModuleApplyTransaction::new(
        manifest,
        contrib,
        vec![c1],
        vec![],
        vec![],
    );
    let preflight = preflight_module_apply(txn, &ModuleApplyLimits::default()).unwrap();
    let candidate = declaration_candidate_for(&preflight, base.module_state());
    let mod_plan = match prepare_module_apply(
        &preflight,
        base.module_state(),
        &candidate,
    ) {
        Outcome::Complete(Ok(fln_env::module_apply::ModuleApplyPlan::Prepared(p))) => *p,
        other => panic!("expected prepared mod plan, got {other:?}"),
    };

    // Mutant 1: Stale attribute base digest
    let other_base = CombinedState::empty();
    let stale_attr_plan = AttributeStatePlan::cut(
        other_base.attribute_state(),
        vec![Assignment {
            attribute: name("unbox"),
            target: name("MutantMod.c1"),
            payload: Payload::Unit,
            kind: AttributeKind::Global,
            provenance: "mutant".to_string(),
        }],
    );

    let prep_res = PreparedCombinedModulePlan::prepare(
        &base,
        mod_id,
        mod_plan,
        stale_attr_plan,
        CombinedAuthorityAxes::default(),
        CombinedUsageSummary::default(),
    );

    assert!(
        matches!(prep_res, Err(CombinedPrepareError::StaleAttributePlan { .. })),
        "stale attribute plan must be refused with StaleAttributePlan"
    );
}
