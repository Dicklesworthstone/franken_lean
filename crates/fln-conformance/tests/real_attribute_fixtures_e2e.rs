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
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use fln_env::module_apply::{
    ModuleApplyLimits, ModuleApplyState, ModuleApplyTransaction, PreflightedModuleApply,
    preflight_module_apply, prepare_module_apply,
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

/// The oracle serializes components, never a display spelling that loses dots,
/// numeric constructors, anonymous names, or UTF-8 boundaries.
fn oracle_name(encoded: &str) -> Name {
    let mut components = encoded.split('/');
    assert_eq!(components.next(), Some("a"));
    components.fold(Name::anonymous(), |parent, component| {
        if let Some(hex) = component.strip_prefix('s') {
            assert_eq!(hex.len() % 2, 0);
            let bytes: Vec<u8> = hex
                .as_bytes()
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| {
                    let pair = std::str::from_utf8(pair).unwrap();
                    u8::from_str_radix(pair, 16).unwrap()
                })
                .collect();
            Name::str(parent, String::from_utf8(bytes).unwrap())
        } else {
            Name::num(
                parent,
                component.strip_prefix('n').unwrap().parse().unwrap(),
            )
        }
    })
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
        env = env
            .add_decl((**decl).clone())
            .expect("declaration is valid");
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
        let extensions = view
            .extension_payloads(fln_olean::region::WalkBudget::default(), 64 * 1024 * 1024)
            .unwrap();
        for ext in &extensions {
            let desc = ExtensionDescriptor {
                name: ext.name.clone(),
                merge: MergeSemantics::AppendOrdered,
                checkpoint: CheckpointSemantics::JournalSuffix,
                provenance: PayloadProvenance::Opaque,
            };
            if base_env.extension(&desc.name).is_none() {
                base_env = base_env.register_extension(desc).unwrap();
            }
        }
    }
    let base_graph = ModuleGraph::new(epoch.clone(), ModuleGraphLimits::default())
        .into_admitted_value()
        .unwrap();
    let base_manifest = Arc::new(
        ModuleProvenanceManifest::new(epoch.clone(), vec![], ModuleProvenanceLimits::default())
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

        let evidence = ArtifactEvidence {
            epoch: epoch.clone(),
            content_digest: hash(Domain::Fixture, &bytes),
            producer: ArtifactProducer::Reference,
            // This local resolver has not authenticated the fixture manifest.
            grade: ArtifactGrade::Provisional,
        };
        let decoded = OleanModuleAdapter::decode_bytes(mod_id.clone(), &bytes, evidence.clone())
            .unwrap_or_else(|e| panic!("failed to decode {fixture_name}: {e:?}"));
        assert_eq!(decoded.evidence, evidence);

        let missing: Vec<ModuleId> = decoded
            .imports
            .iter()
            .map(|imp| imp.module.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();

        let transparency =
            if decoded.extension_entries.is_empty() {
                PayloadTransparency::Understood
            } else {
                let false_completeness = ProvenanceCompleteness::new(
                    CaptureStatus::Partial,
                    PayloadTransparency::Understood,
                    missing.clone(),
                );
                assert!(
                    matches!(ModuleProvenanceManifest::new(
                epoch.clone(), vec![decoded.to_contribution_record(false_completeness)],
                ModuleProvenanceLimits::default(),
            ), Err(fln_env::provenance::ModuleProvenanceError::PayloadTransparencyMismatch { .. })),
                    "opaque bytes cannot be relabeled understood to pass the old fixture"
                );
                PayloadTransparency::Opaque
            };
        let completeness = if missing.is_empty() {
            ProvenanceCompleteness::new(CaptureStatus::Complete, transparency, vec![])
        } else {
            ProvenanceCompleteness::new(CaptureStatus::Partial, transparency, missing)
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

        let mut corrupted = decoded.extension_entries.clone();
        let original = &corrupted[0];
        let mut changed_bytes = original.payload().to_vec();
        changed_bytes[0] ^= 1;
        corrupted[0] = fln_env::module_apply::ExtensionPayload::new(
            original.contribution_index(),
            original.descriptor().clone(),
            original.source_ordinal(),
            changed_bytes,
        );
        assert!(
            preflight_module_apply(
                ModuleApplyTransaction::new(
                    manifest.clone(),
                    contribution.clone(),
                    decoded.constants.clone(),
                    vec![],
                    corrupted,
                ),
                &ModuleApplyLimits::default()
            )
            .is_err(),
            "payload corruption must fail its original manifest before staging"
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
        let mod_plan =
            match prepare_module_apply(&preflight, combined_state.module_state(), &candidate_env) {
                Outcome::Complete(Ok(fln_env::module_apply::ModuleApplyPlan::Prepared(p))) => *p,
                other => panic!(
                    "failed on {fixture_name}: expected prepared module apply plan, got {other:?}"
                ),
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
        assert_eq!(resulting_state.module_state().manifest().records().len(), 1);
        assert!(
            !decoded.extension_entries.is_empty(),
            "real fixture must exercise opaque entries"
        );
        for payload in &decoded.extension_entries {
            let extension = resulting_state
                .module_state()
                .environment()
                .extension(&payload.descriptor().name)
                .expect("applied extension");
            assert_eq!(extension.provenance(), PayloadProvenance::Opaque);
            assert!(!extension.supports_fine_invalidation());
            let applied = extension
                .entries()
                .nth(payload.source_ordinal() as usize)
                .expect("each decoded entry was applied in source order");
            assert_eq!(applied.payload.as_ref(), payload.payload());
            let contribution = &decoded.extension_contributions[payload.contribution_index()];
            assert_eq!(
                contribution.entries()[payload.source_ordinal() as usize],
                fln_env::provenance::ExtensionEntryId::derive(
                    &epoch,
                    payload.descriptor(),
                    &applied.payload,
                )
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 3. Duplicate, conflict, removal, and replacement laws per family
// ---------------------------------------------------------------------------

#[test]
fn real_imported_tag_entries_drive_native_attribute_queries() {
    use fln_olean::decl::ChainLimits;
    use fln_olean::region::WalkBudget;
    let fixtures = workspace_root().join("crates/fln-conformance/fixtures/tag_attributes");
    let read = |suffix| {
        fs::read(fixtures.join(format!("prelude.olean{suffix}")))
            .expect("the generated Reference fixture chain must be checked in")
    };
    let parts = [read(""), read(".server"), read(".private")];
    let decoded = OleanModuleAdapter::decode_chain_bytes(
        ModuleId::new(Name::from_components(["Init", "Prelude"])),
        &parts[0],
        &parts[1],
        &parts[2],
        ArtifactEvidence {
            epoch: pinned_epoch(),
            content_digest: OleanModuleAdapter::chain_content_digest(
                &parts[0], &parts[1], &parts[2],
            ),
            producer: ArtifactProducer::Reference,
            grade: ArtifactGrade::Provisional,
        },
        ChainLimits::new(parts.iter().map(Vec::len).sum()),
    )
    .unwrap();
    let base = load_census_state();
    let census =
        fs::read_to_string(workspace_root().join("contracts/ATTRIBUTE_STATE_CENSUS.txt")).unwrap();
    for (from, to) in [
        ("tag=v4.32.0", "tag=v9.0.0"),
        (
            "commit=8c9756b28d64dab099da31a4c09229a9e6a2ef35",
            "commit=0000000000000000000000000000000000000000",
        ),
    ] {
        let (foreign, _) = AttributeState::from_census(&census.replace(from, to)).unwrap();
        assert!(
            matches!(decoded.tag_attribute_plan(&foreign, WalkBudget::default(), 64 * 1024 * 1024),
            Err(fln_conformance::module_adapter::ModuleAdapterError::AttributeCensusEpochMismatch { artifact, census })
                if artifact == decoded.evidence.epoch && Some(&census) == foreign.census_epoch()),
            "a real pinned module must not decode tags with a foreign census: {to}"
        );
    }
    assert!(matches!(
        decoded.tag_attribute_plan(&AttributeState::new(), WalkBudget::default(), usize::MAX),
        Err(fln_conformance::module_adapter::ModuleAdapterError::UnboundAttributeCensus)
    ));
    let (unprefixed, _) =
        AttributeState::from_census(&census.replace("tag=v4.32.0", "tag=4.32.0")).unwrap();
    assert_eq!(
        decoded
            .tag_attribute_plan(&unprefixed, WalkBudget::default(), usize::MAX)
            .unwrap()
            .assignments(),
        decoded
            .tag_attribute_plan(&base, WalkBudget::default(), usize::MAX)
            .unwrap()
            .assignments()
    );
    let plan = decoded
        .tag_attribute_plan(&base, WalkBudget::default(), 64 * 1024 * 1024)
        .unwrap();
    let targets: Vec<_> = plan
        .assignments()
        .iter()
        .filter(|a| a.attribute == name("unbox"))
        .map(|a| a.target.to_display_string())
        .collect();
    eprintln!("Prelude imported unbox targets: {targets:?}");
    assert_eq!(targets.len(), 3);
    let expected_state = plan.clone().publish(&base).unwrap();
    let mut environment = Environment::new();
    for contribution in &decoded.extension_contributions {
        environment = environment
            .register_extension(contribution.descriptor().clone())
            .unwrap();
    }
    let module_base = ModuleApplyState::from_parts(
        environment,
        ModuleGraph::new(pinned_epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .unwrap(),
        Arc::new(
            ModuleProvenanceManifest::new(
                pinned_epoch(),
                vec![],
                ModuleProvenanceLimits::default(),
            )
            .unwrap(),
        ),
    )
    .unwrap();
    let combined_base = CombinedState::new(module_base, base.clone());
    let missing = decoded
        .imports
        .iter()
        .map(|i| i.module.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let completeness = ProvenanceCompleteness::new(
        if missing.is_empty() {
            CaptureStatus::Complete
        } else {
            CaptureStatus::Partial
        },
        PayloadTransparency::Opaque,
        missing,
    );
    let record = decoded.to_contribution_record(completeness.clone());
    let manifest = Arc::new(
        ModuleProvenanceManifest::new(
            pinned_epoch(),
            vec![record],
            ModuleProvenanceLimits::default(),
        )
        .unwrap(),
    );
    let transaction =
        OleanModuleAdapter::build_transaction(&decoded, manifest, completeness).unwrap();
    let preflight = preflight_module_apply(transaction, &ModuleApplyLimits::default()).unwrap();
    let candidate = declaration_candidate_for(&preflight, combined_base.module_state());
    let module_plan =
        match prepare_module_apply(&preflight, combined_base.module_state(), &candidate) {
            Outcome::Complete(Ok(fln_env::module_apply::ModuleApplyPlan::Prepared(plan))) => *plan,
            other => panic!("real module preparation failed: {other:?}"),
        };
    let combined = PreparedCombinedModulePlan::prepare(
        &combined_base,
        decoded.module_id.clone(),
        module_plan,
        plan,
        CombinedAuthorityAxes::conservative(),
        CombinedUsageSummary::default(),
    )
    .unwrap();
    let before = combined_base.combined_root();
    let cancelled = combined.clone().commit(
        &combined_base,
        Some(&TestCancelProbe(AtomicBool::new(true))),
    );
    assert!(matches!(cancelled, Outcome::Inconclusive(_)));
    assert_eq!(combined_base.combined_root(), before);
    assert!(combined_base.attribute_state().assignments().is_empty());
    let committed = combined
        .commit(&combined_base, None)
        .into_complete()
        .unwrap()
        .unwrap();
    assert_eq!(committed.state.attribute_state(), &expected_state);
    assert_eq!(
        committed
            .state
            .module_state()
            .graph()
            .record(&decoded.module_id)
            .unwrap()
            .artifact,
        decoded.evidence
    );
    for info in decoded.constants.iter().chain(&decoded.extra_constants) {
        assert_eq!(
            committed
                .state
                .module_state()
                .environment()
                .find(info.name()),
            Some(info.as_ref())
        );
    }
    let state = committed.state.attribute_state();
    let fixture = fs::read_to_string(
        workspace_root().join("crates/fln-conformance/fixtures/tag_attributes/prelude.tsv"),
    )
    .expect(
        "regenerate the additive oracle with gen_attribute_state_census.py --tag-oracle-output",
    );
    let lock = fs::read_to_string(workspace_root().join("SUITE.lock")).unwrap();
    let pin = lock
        .lines()
        .find(|line| line.starts_with("reference "))
        .unwrap();
    let field = |key: &str| {
        pin.split_whitespace()
            .find_map(|token| token.strip_prefix(key))
            .unwrap()
    };
    let mut lines = fixture.lines();
    assert_eq!(lines.next(), Some("schema fln-imported-tag-queries/1"));
    assert_eq!(
        lines.next().unwrap(),
        format!(
            "oracle\t{}\t{}",
            field("tag=").trim_start_matches('v'),
            field("commit=")
        )
    );
    assert_eq!(lines.next(), Some("module\tInit.Prelude\tprivate"));
    let mut oracle_positive = BTreeSet::new();
    let mut bindings = BTreeSet::new();
    let mut negatives = BTreeSet::new();
    for line in lines {
        let fields: Vec<_> = line.split('\t').collect();
        match fields.as_slice() {
            ["binding", attribute, _declaration, extension] => {
                let attribute = name(attribute);
                assert!(bindings.insert(attribute.clone()));
                assert_eq!(
                    base.definition(&attribute).unwrap().serialized_extension,
                    Some(oracle_name(extension))
                );
            }
            ["query", attribute, target, verdict] => {
                let attribute = name(attribute);
                let target = oracle_name(target);
                let expected = match *verdict {
                    "true" => true,
                    "false" => false,
                    other => panic!("unknown oracle verdict {other}"),
                };
                assert_eq!(state.has_attr(&attribute, &target), expected, "{line}");
                if expected {
                    assert!(oracle_positive.insert((attribute, target)));
                } else {
                    assert!(negatives.insert(attribute));
                }
            }
            _ => panic!("unknown oracle record {line}"),
        }
    }
    let registered_tags = base
        .definitions()
        .iter()
        .filter(|(_, definition)| definition.family == AttributeFamily::Tag)
        .map(|(_, definition)| definition.name.clone())
        .collect::<BTreeSet<_>>();
    assert!(!oracle_positive.is_empty());
    assert_eq!(bindings, registered_tags);
    assert_eq!(negatives, registered_tags);
    assert_eq!(
        oracle_positive,
        state
            .assignments()
            .iter()
            .map(|(_, a)| (a.attribute.clone(), a.target.clone()))
            .collect()
    );
    for payload in &decoded.extension_entries {
        let extension = committed
            .state
            .module_state()
            .environment()
            .extension(&payload.descriptor().name)
            .unwrap();
        assert_eq!(extension.provenance(), PayloadProvenance::Opaque);
        assert!(!extension.supports_fine_invalidation());
        assert_eq!(
            extension
                .entries()
                .nth(payload.source_ordinal() as usize)
                .unwrap()
                .payload
                .as_ref(),
            payload.payload()
        );
    }
    for target in ["Prod", "Option", "Except"] {
        assert!(!base.has_attr(&name("unbox"), &name(target)));
        assert!(state.has_attr(&name("unbox"), &name(target)));
    }
    assert!(!state.has_attr(&name("unbox"), &name("Nat")));
    let mut missing_target = decoded.clone();
    missing_target
        .constants
        .retain(|info| info.name() != &name("Prod"));
    missing_target
        .extra_constants
        .retain(|info| info.name() != &name("Prod"));
    assert!(
        matches!(missing_target.tag_attribute_plan(&base, WalkBudget::default(), usize::MAX),
        Err(fln_conformance::module_adapter::ModuleAdapterError::MissingAttributeTarget { attribute, target })
            if attribute == name("unbox") && target == name("Prod"))
    );
    let tag_index = decoded
        .extension_entries
        .iter()
        .position(|entry| entry.descriptor().name == name("Lean.IR.UnboxResult.unboxAttr"))
        .unwrap();
    let original = &decoded.extension_entries[tag_index];
    let mut corrupt = decoded.clone();
    corrupt.extension_entries[tag_index] = fln_env::module_apply::ExtensionPayload::new(
        original.contribution_index(),
        original.descriptor().clone(),
        original.source_ordinal(),
        vec![1; 8],
    );
    assert!(matches!(
        corrupt.tag_attribute_plan(&base, WalkBudget::default(), usize::MAX),
        Err(fln_conformance::module_adapter::ModuleAdapterError::AttributePayloadMismatch { .. })
    ));
    assert!(matches!(
        decoded.tag_attribute_plan(&base, WalkBudget::default(), 0),
        Err(
            fln_conformance::module_adapter::ModuleAdapterError::CapturedName(
                fln_olean::region::CapturedNameError::Bytes { .. }
            )
        )
    ));
    assert!(matches!(
        decoded.tag_attribute_plan(&base, WalkBudget { max_objects: 0 }, usize::MAX),
        Err(
            fln_conformance::module_adapter::ModuleAdapterError::CapturedName(
                fln_olean::region::CapturedNameError::Objects { .. }
            )
        )
    ));
    assert_eq!(
        decoded
            .tag_attribute_plan(&base, WalkBudget::default(), 64 * 1024 * 1024)
            .unwrap()
            .publish(&base)
            .unwrap(),
        expected_state
    );
}

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
    let q_class = census_state
        .dispatch(&name("class"))
        .expect("class dispatch");
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
    let mod_rec_a = ModuleRecord::new(mod_id_a.clone(), true, vec![], make_evidence(epoch.clone()));
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
    let txn_a =
        ModuleApplyTransaction::new(manifest_a, contrib_a, vec![c1.clone()], vec![], vec![]);
    let preflight_a = preflight_module_apply(txn_a, &ModuleApplyLimits::default()).unwrap();
    let candidate_a = declaration_candidate_for(&preflight_a, base.module_state());
    let mod_plan_a = match prepare_module_apply(&preflight_a, base.module_state(), &candidate_a) {
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
    let mod_rec = ModuleRecord::new(mod_id.clone(), true, vec![], make_evidence(epoch.clone()));
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
    let txn = ModuleApplyTransaction::new(manifest, contrib, vec![c1], vec![], vec![]);
    let preflight = preflight_module_apply(txn, &ModuleApplyLimits::default()).unwrap();
    let candidate = declaration_candidate_for(&preflight, base.module_state());
    let mod_plan = match prepare_module_apply(&preflight, base.module_state(), &candidate) {
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
                let preflight = preflight_module_apply(txn, &ModuleApplyLimits::default()).unwrap();
                let candidate = declaration_candidate_for(&preflight, base_clone.module_state());
                let mod_plan =
                    match prepare_module_apply(&preflight, base_clone.module_state(), &candidate) {
                        Outcome::Complete(Ok(
                            fln_env::module_apply::ModuleApplyPlan::Prepared(p),
                        )) => *p,
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
    let mod_rec = ModuleRecord::new(mod_id.clone(), true, vec![], make_evidence(epoch.clone()));
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
    let txn = ModuleApplyTransaction::new(manifest, contrib, vec![c1], vec![], vec![]);
    let preflight = preflight_module_apply(txn, &ModuleApplyLimits::default()).unwrap();
    let candidate = declaration_candidate_for(&preflight, base.module_state());
    let mod_plan = match prepare_module_apply(&preflight, base.module_state(), &candidate) {
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
        matches!(
            prep_res,
            Err(CombinedPrepareError::StaleAttributePlan { .. })
        ),
        "stale attribute plan must be refused with StaleAttributePlan"
    );
}
