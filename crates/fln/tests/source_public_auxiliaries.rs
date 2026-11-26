//! Public proof tactics retain checked auxiliary bodies in the selected world
//! and publish only the pin's permitted interfaces.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
    SourceModuleSession, imported::SourceOleanImportLimits,
};
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, OleanWalkBudget, OleanWriteBudget, Outcome, SourceCheckLimits,
    SourceModuleInput,
};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn private(module: &str, declaration: &str) -> Name {
    Name::num(n(&format!("_private.{module}")), 0).append_core(&n(declaration))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}

fn check(files: &[(&str, &str)]) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    Engine::builder()
        .build_empty()
        .check_source_modules(&inputs, &names[0], &KVMap::new(), limits())
}

fn checked(files: &[(&str, &str)]) -> SourceModuleCheck {
    check(files)
        .unwrap_or_else(|error| panic!("{files:?}: {error:?}"))
        .into_complete()
        .unwrap()
}

fn auxiliaries(engine: &Engine, owner: &Name) -> Vec<Name> {
    engine
        .environment()
        .constants()
        .filter_map(|(name, _)| {
            (name.parent() == *owner
                && matches!(name.leaf_view(), fln_core::name::LeafView::Str(part)
                    if part.starts_with("_proof_")))
            .then(|| name.clone())
        })
        .collect()
}

const BASE: &str = "prelude\ninductive Truth : Prop where\n| make\nstructure Box where\n  proof : Truth\nclass Law : Prop where\n  proof : Truth\nclass Pick where\n  proof : Truth";
const HEADER: &str = "module\nprelude\npublic import Base\n";

#[test]
fn public_declarations_without_auxiliaries_keep_their_identity_predecessor() {
    let api = format!(
        "{HEADER}public theorem ordinary : Truth := Truth.make\n\
         public noncomputable def hidden : Box := Box.mk Truth.make\n\
         @[expose] public noncomputable def exposed : Box := Box.mk Truth.make\n\
         public instance ordinaryLaw : Law := Law.mk Truth.make\n\
         public noncomputable instance ordinaryPick : Pick := Pick.mk Truth.make\n"
    );
    let local = checked(&[("Api", &api), ("Base", BASE)]);
    let imported = checked(&[
        ("Main", "module\nprelude\npublic import Api"),
        ("Api", &api),
        ("Base", BASE),
    ]);
    for name in ["ordinary", "hidden", "ordinaryLaw"] {
        assert!(
            matches!(
                imported.checked.engine.environment().find(&n(name)),
                Some(ConstantInfo::Axiom(_))
            ),
            "{name}"
        );
    }
    for name in ["exposed", "ordinaryPick"] {
        assert!(
            matches!(
                imported.checked.engine.environment().find(&n(name)),
                Some(ConstantInfo::Defn(_))
            ),
            "{name}"
        );
    }
    for name in ["ordinary", "hidden", "exposed", "ordinaryLaw", "ordinaryPick"] {
        assert!(auxiliaries(&local.checked.engine, &n(name)).is_empty());
        assert!(auxiliaries(&local.checked.engine, &private("Api", name)).is_empty());
    }
}

#[test]
fn hidden_public_theorems_keep_auxiliary_proofs_out_of_importers() {
    let api = format!(
        "{HEADER}private theorem secret : Truth := Truth.make\n\
         public theorem proof : Truth := by as_aux_lemma => exact secret\n"
    );
    let local = checked(&[("Api", &api), ("Base", BASE)]);
    let names = auxiliaries(&local.checked.engine, &private("Api", "proof"));
    assert_eq!(names, [private("Api", "proof._proof_1_1")]);
    for name in &names {
        assert!(matches!(
            local.checked.engine.environment().find(name),
            Some(ConstantInfo::Thm(_))
        ));
    }
    assert!(auxiliaries(&local.checked.engine, &n("proof")).is_empty());

    let imported = checked(&[
        (
            "Main",
            "module\nprelude\npublic import Api\npublic theorem useProof : Truth := proof",
        ),
        ("Api", &api),
        ("Base", BASE),
    ]);
    let environment = imported.checked.engine.environment();
    assert!(matches!(
        environment.find(&n("proof")),
        Some(ConstantInfo::Axiom(_))
    ));
    assert!(matches!(
        environment.find(&n("useProof")),
        Some(ConstantInfo::Thm(_))
    ));
    assert!(!environment.contains(&private("Api", "secret")));
    for name in names {
        assert!(!environment.contains(&name), "{name:?}");
    }
}

#[test]
fn hidden_definitions_and_both_kinds_of_instances_admit_auxiliary_predecessors() {
    let api = format!(
        "{HEADER}private theorem secret : Truth := Truth.make\n\
         public noncomputable def hidden : Box := Box.mk (by as_aux_lemma => exact secret)\n\
         @[no_expose] public noncomputable instance chosen : Pick := Pick.mk (by as_aux_lemma => exact secret)\n\
         public instance lawful : Law := by as_aux_lemma => exact Law.mk secret\n"
    );
    let local = checked(&[("Api", &api), ("Base", BASE)]);
    for owner in ["hidden", "chosen", "lawful"] {
        let names = auxiliaries(&local.checked.engine, &private("Api", owner));
        assert_eq!(names.len(), 1, "{owner}");
        assert!(matches!(
            local.checked.engine.environment().find(&names[0]),
            Some(ConstantInfo::Thm(_))
        ));
    }
    let imported = checked(&[
        (
            "Main",
            "module\nprelude\npublic import Api\npublic theorem fromDefinition : Truth := hidden.proof\npublic theorem fromInstance : Truth := Pick.proof\npublic theorem fromProofInstance : Truth := Law.proof",
        ),
        ("Api", &api),
        ("Base", BASE),
    ]);
    for owner in ["hidden", "chosen", "lawful"] {
        assert!(
            matches!(
                imported.checked.engine.environment().find(&n(owner)),
                Some(ConstantInfo::Axiom(_))
            ),
            "{owner}"
        );
        assert!(auxiliaries(&imported.checked.engine, &private("Api", owner)).is_empty());
    }
}

#[test]
fn exposed_data_and_proof_instances_export_auxiliary_signatures_without_bodies() {
    let api = format!(
        "{HEADER}@[expose] public noncomputable def exposed : Box := Box.mk (by as_aux_lemma => exact Truth.make)\n\
         @[expose] public instance exposedLaw : Law := by as_aux_lemma => exact Law.mk Truth.make\n\
         public noncomputable instance exposedPick : Pick := Pick.mk (by as_aux_lemma => exact Truth.make)\n"
    );
    let local = checked(&[("Api", &api), ("Base", BASE)]);
    let imported = checked(&[
        (
            "Main",
            "module\nprelude\npublic import Api\npublic theorem useExposed : Truth := exposed.proof",
        ),
        ("Api", &api),
        ("Base", BASE),
    ]);
    for owner in ["exposed", "exposedLaw", "exposedPick"] {
        let names = auxiliaries(&local.checked.engine, &n(owner));
        assert_eq!(names.len(), 1, "{owner}");
        let Some(ConstantInfo::Thm(theorem)) = local.checked.engine.environment().find(&names[0])
        else {
            panic!("the defining world must retain {owner}'s checked auxiliary proof");
        };
        let Some(ConstantInfo::Axiom(interface)) =
            imported.checked.engine.environment().find(&names[0])
        else {
            panic!("the exported world must receive only {owner}'s auxiliary signature");
        };
        assert_eq!(interface.base, theorem.base);
        assert!(!interface.is_unsafe);
        assert!(auxiliaries(&local.checked.engine, &private("Api", owner)).is_empty());
    }
    assert!(matches!(
        imported.checked.engine.environment().find(&n("exposed")),
        Some(ConstantInfo::Defn(_))
    ));
    assert!(matches!(
        imported.checked.engine.environment().find(&n("exposedPick")),
        Some(ConstantInfo::Defn(_))
    ));
    assert!(matches!(
        imported.checked.engine.environment().find(&n("exposedLaw")),
        Some(ConstantInfo::Axiom(_))
    ));
}

#[test]
fn multiple_auxiliaries_leave_instance_and_simp_metadata_on_the_owner() {
    let base = Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let names = [n("Main"), n("Api")];
    let api = "module\nprelude\npublic inductive OtherTruth : Prop where\n| make\npublic class Bundle : Prop where\n  left : True\n  right : OtherTruth\n@[simp] public instance bundled : Bundle := by\n  constructor\n  as_aux_lemma => exact True.intro\n  as_aux_lemma => exact OtherTruth.make";
    let local = base
        .check_source_modules(
            &[SourceModuleInput {
                name: &names[1],
                source: api.as_bytes(),
            }],
            &names[1],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let helpers = auxiliaries(&local.checked.engine, &private("Api", "bundled"));
    assert_eq!(helpers.len(), 2);
    let main = "module\nprelude\npublic import Api\npublic theorem byInstance : Bundle := by infer_instance\npublic theorem bySimp : Bundle := by simp";
    let imported = base
        .check_source_modules(
            &[
                SourceModuleInput {
                    name: &names[0],
                    source: main.as_bytes(),
                },
                SourceModuleInput {
                    name: &names[1],
                    source: api.as_bytes(),
                },
            ],
            &names[0],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for engine in [&local.checked.engine, &imported.checked.engine] {
        let registry = fln_elab::instances::InstanceRegistry::read(engine.environment()).unwrap();
        let [instance] = registry.candidates(&n("Bundle")) else {
            panic!("only the completed owner may become the class instance");
        };
        assert_eq!(instance.declaration, n("bundled"));
        let simp = fln_elab::source::scope::simp::read(engine.environment()).unwrap();
        assert_eq!(
            simp.iter()
                .filter(|entry| entry.declaration == n("bundled"))
                .count(),
            1
        );
        assert!(simp.iter().all(|entry| !helpers.contains(&entry.declaration)));
    }
}

#[test]
fn exposed_auxiliaries_cannot_borrow_private_bodies_or_header_dependencies() {
    for body in [
        "@[expose] public noncomputable def bad : Box := Box.mk (by as_aux_lemma => exact secret)",
        "@[expose] public instance bad : Law := by as_aux_lemma => exact Law.mk secret",
        "public noncomputable instance bad : Pick := Pick.mk (by as_aux_lemma => exact secret)",
        "public theorem bad (h : Hidden Truth) : Truth := by as_aux_lemma => exact h",
        "public theorem bad (P : Prop) (h : P) : Truth := by as_aux_lemma => exact h",
    ] {
        let api = format!(
            "{HEADER}private theorem secret : Truth := Truth.make\n\
             private noncomputable def Hidden (P : Prop) : Prop := P\n{body}\n"
        );
        assert!(
            matches!(
                check(&[("Api", &api), ("Base", BASE)]),
                Err(SourceModuleCheckError::Source { .. })
            ),
            "{body}"
        );
    }
}

#[test]
fn auxiliary_name_freshness_checks_the_private_predecessor_of_an_exposed_body() {
    let api = format!(
        "{HEADER}namespace exposed\nprivate theorem _proof_1 : Truth := Truth.make\nend exposed\n\
         @[expose] public noncomputable def exposed : Box := Box.mk (by as_aux_lemma => exact Truth.make)\n"
    );
    let checked = checked(&[("Api", &api), ("Base", BASE)]);
    assert!(
        checked
            .checked
            .engine
            .environment()
            .contains(&private("Api", "exposed._proof_1"))
    );
    assert_eq!(
        auxiliaries(&checked.checked.engine, &n("exposed")),
        [n("exposed._proof_2")]
    );
}

#[test]
fn a_failed_owner_rolls_back_its_auxiliaries_and_cached_public_interfaces() {
    let mut session = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let names = [n("Main"), n("Api")];
    let main = "module\nprelude\npublic import Api\npublic theorem consumer (P : Prop) (h : P) : P := api P h";
    let valid = "module\nprelude\npublic theorem api (P : Prop) (h : P) : P := by\n  have saved : P := by as_aux_lemma => exact h\n  exact saved";
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: main.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: valid.as_bytes(),
        },
    ];
    let cold = session
        .check(&inputs, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    let retained = session.retained_modules();
    for bad in [
        valid.replace("exact saved", "exact missing"),
        valid.replace("exact saved", "exact (fun (Q : Prop) (hq : Q) => hq)"),
    ] {
        let changed = [
            inputs[0],
            SourceModuleInput {
                name: &names[1],
                source: bad.as_bytes(),
            },
        ];
        assert!(matches!(
            session.check(&changed, &names[0]),
            Err(SourceModuleCheckError::Source { .. })
        ));
        assert_eq!(session.retained_modules(), retained);
        let recovered = session
            .check(&inputs, &names[0])
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(recovered.reused_modules, 2);
        assert_eq!(
            recovered.checked.checked.result_logical_root,
            cold.checked.checked.result_logical_root
        );
    }
}

#[test]
fn module_artifacts_retain_checked_auxiliaries_only_in_private_companions() {
    let initial = Engine::builder().build_empty();
    let module = n("Api");
    let source = "module\nprelude\npublic inductive Truth : Prop where\n| make\npublic theorem proof : Truth := by as_aux_lemma => exact Truth.make";
    let built = initial
        .compile_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            limits(),
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let [artifact] = built.artifacts.as_slice() else {
        panic!("one source module must produce one artifact");
    };
    let public = fln_olean::region::OleanView::parse(&artifact.bytes)
        .unwrap()
        .module_data(OleanWalkBudget::default())
        .unwrap();
    assert!(public.const_names.contains(&n("proof")));
    let auxiliary = private("Api", "proof._proof_1_1");
    assert!(!public.const_names.contains(&auxiliary));
    let parts = artifact.companions.as_ref().unwrap();
    let imported = initial
        .import_olean_modules_for_source(
            &[OleanModuleInput {
                name: &module,
                artifact: &artifact.bytes,
                server_artifact: Some(&parts.server),
                private_artifact: Some(&parts.private),
            }],
            std::slice::from_ref(&module),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                4 * 1024 * 1024,
                limits().source.admission.kernel,
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(
        imported.engine.environment().find(&auxiliary),
        Some(ConstantInfo::Thm(_))
    ));
    assert!(initial.environment().is_empty());
}

#[test]
fn public_partial_entry_points_do_not_drop_auxiliary_effects() {
    let plain = "module\nprelude\npublic partial def identity (P : Prop) (h : P) : P := h";
    let completed = checked(&[("Api", plain)]);
    assert!(matches!(
        completed.checked.engine.environment().find(&n("identity")),
        Some(ConstantInfo::Defn(_))
    ));
    let unsupported = "module\nprelude\npublic partial def identity (P : Prop) (h : P) : P := by as_aux_lemma => exact h";
    let error = check(&[("Api", unsupported)]).unwrap_err();
    let SourceModuleCheckError::Source { error, .. } = error else {
        panic!("an effectless partial entry must report the tactic capability boundary");
    };
    assert_eq!(error.disposition(), ("capability", false, 5));
}

#[test]
fn exhausted_public_proof_checking_never_publishes_a_proof_interface() {
    let base = Engine::builder().build_empty();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let module = n("Api");
    let mut starved = limits();
    starved.source.admission.kernel.steps = 0;
    let result = base.check_source_modules(
        &[SourceModuleInput {
            name: &module,
            source: b"module\nprelude\npublic theorem proof (P : Prop) (h : P) : P := by as_aux_lemma => exact h",
        }],
        &module,
        &options,
        starved,
    );
    assert!(matches!(result, Ok(Outcome::Inconclusive(_))), "{result:?}");
    assert_eq!(base.logical_root(&options), root);
    assert!(base.environment().is_empty());
}
