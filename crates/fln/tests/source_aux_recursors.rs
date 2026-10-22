//! Auxiliary metadata survives native module boundaries and real Reference
//! import, without granting tags to a name merely because of its suffix.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::{SourceOleanImportError, SourceOleanImportLimits};
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, OleanCheckLimits, OleanModuleInput,
    OleanWriteBudget, SourceCheckLimits, SourceModuleInput,
};
use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_elab::aux_recursors::AuxRecursors;
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_olean::region::{ModuleImport, OleanView, WalkBudget};
use fln_olean::source_extensions::{self, DecodeLimits};
use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(8 * 1024 * 1024))
}

fn source_limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(admission()))
}

fn metadata(bytes: &[u8]) -> source_extensions::SourceExtensions {
    let blocks = OleanView::parse(bytes)
        .unwrap()
        .extension_payloads(WalkBudget::default(), 4 << 20)
        .unwrap();
    source_extensions::decode(&blocks, DecodeLimits::default()).unwrap()
}

#[test]
fn generated_tags_cross_artifact_diamonds_and_warm_replay_once() {
    // casesOn and course-of-values generation require the polymorphic PUnit
    // and PProd primitives.
    // The native source frontend does not yet accept `PUnit.{u} : Sort u`, and
    // an ambient seed has no artifact import identity. Extract only the seed's
    // already checked primitive declarations, then check their Primitives
    // artifact through both seats to obtain a bound predecessor for this test.
    let primitive_constants: Vec<_> = {
        let seed = Engine::with_source_seed(admission())
            .unwrap()
            .into_complete()
            .unwrap();
        [
            "PUnit",
            "PUnit.unit",
            "PUnit.rec",
            "PProd",
            "PProd.mk",
            "PProd.rec",
            "Eq",
            "Eq.refl",
            "Eq.rec",
            "rfl",
        ]
        .into_iter()
        .map(|name| seed.environment().find(&n(name)).unwrap().clone())
        .collect()
    };
    let primitive_module = n("Primitives");
    let primitive_artifact = encoded(&primitive_constants, &[], &[]);
    let predecessor = Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &[OleanModuleInput {
                name: &primitive_module,
                artifact: &primitive_artifact,
                server_artifact: None,
                private_artifact: None,
            }],
            std::slice::from_ref(&primitive_module),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(1 << 20, admission().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    assert!(predecessor.environment().contains(&n("PUnit")));
    assert!(
        AuxRecursors::read(predecessor.environment())
            .unwrap()
            .is_empty()
    );
    let files = [
        (
            n("Base"),
            "prelude\nimport Primitives\n\
             inductive Flag : Type where | off | on\n\
             structure Prod (A B : Type) where\n  fst : A\n  snd : B\n\
             inductive Tick : Type where | stop | step : Tick -> Tick\n\
             def Fake.casesOn (A : Type) (x : A) : A := x\n\
             def identity (A : Type) (x : A) : A := x\n\
             theorem baseRfl (A : Type) (x : A) : identity A x = x := rfl",
        ),
        (n("Left"), "prelude\nimport Base"),
        (n("Right"), "prelude\nimport Base"),
        (
            n("Main"),
            "prelude\nimport Left\nimport Right\n\
             def chosen (b : Flag) (A : Type) (x y : A) : A := Flag.casesOn b x y\n\
             theorem recurse (A : Type) (x : A) : Tick.brecOn Tick.stop (fun _ _ => x) = x := rfl",
        ),
    ];
    let inputs: Vec<_> = files
        .iter()
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let mut session = SourceModuleSession::new(
        predecessor.clone(),
        KVMap::new(),
        source_limits(),
        SourceModuleCacheLimits::default(),
    );
    let cold = session
        .compile(&inputs, &n("Main"), OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let expected = AuxRecursors::read(cold.checked.checked.engine.environment()).unwrap();
    assert_eq!(expected.len(), 8);
    for name in [
        "Flag.recOn",
        "Flag.casesOn",
        "Prod.recOn",
        "Prod.casesOn",
        "Tick.recOn",
        "Tick.casesOn",
        "Tick.below",
        "Tick.brecOn",
    ] {
        assert!(expected.contains(&n(name)), "{name}");
    }
    assert!(!expected.contains(&n("Fake.casesOn")));
    assert!(!expected.contains(&n("Tick.brecOn.go")));
    let expected_defeq = [n("baseRfl"), n("recurse")].into_iter().collect();
    assert_eq!(
        fln_elab::source::scope::simp::defeq::read(
            cold.checked.checked.engine.environment(),
            || Ok(())
        )
        .unwrap(),
        expected_defeq
    );
    for artifact in &cold.artifacts {
        let tags = metadata(&artifact.bytes);
        assert_eq!(
            tags.aux_recursors.len(),
            if artifact.name == n("Base") { 8 } else { 0 }
        );
        let own_defeq = if artifact.name == n("Base") {
            vec![n("baseRfl")]
        } else if artifact.name == n("Main") {
            vec![n("recurse")]
        } else {
            vec![]
        };
        assert_eq!(tags.defeq, own_defeq);
        assert_eq!(tags.backward_defeq, own_defeq);
    }
    let warm = session
        .compile(&inputs, &n("Main"), OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (4, 0));
    assert_eq!(
        AuxRecursors::read(warm.checked.checked.engine.environment()).unwrap(),
        expected
    );
    assert_eq!(
        fln_elab::source::scope::simp::defeq::read(
            warm.checked.checked.engine.environment(),
            || Ok(())
        )
        .unwrap(),
        expected_defeq
    );
    assert!(
        cold.artifacts
            .iter()
            .zip(&warm.artifacts)
            .all(|(cold, warm)| cold.bytes == warm.bytes)
    );
    let mut modules: Vec<_> = cold
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    // The artifact checker consumes a complete closed set. Recheck the same
    // primitive bytes with the four new artifacts from an empty environment,
    // so no ambient declaration can make an incomplete artifact pass.
    modules.push(OleanModuleInput {
        name: &primitive_module,
        artifact: &primitive_artifact,
        server_artifact: None,
        private_artifact: None,
    });
    let receipt = Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &modules,
            &[n("Main")],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(4 << 20, admission().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|m| m.aux_recursors)
            .sum::<usize>(),
        8
    );
    assert_eq!(
        AuxRecursors::read(receipt.engine.environment()).unwrap(),
        expected
    );
    assert_eq!(receipt.modules.iter().map(|m| m.defeq).sum::<usize>(), 2);
    assert_eq!(
        fln_elab::source::scope::simp::defeq::read(receipt.engine.environment(), || Ok(()))
            .unwrap(),
        expected_defeq
    );
    receipt
        .engine
        .check_source_files(
            &["def use (A : Type) (x y : A) : A := Flag.casesOn Flag.off x y\n\
                theorem useHistory (A : Type) (x : A) : Tick.brecOn (Tick.step Tick.stop) (fun _ _ => x) = x := rfl\n\
                theorem useTag (A : Type) (x : A) (P : A -> Prop) (h : P x) : P (identity A x) := by\n  fail_if_success dsimp only []\n  dsimp only [baseRfl]\n  guard_target =ₛ P x\n  exact h".as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn real_prelude_auxiliary_tags_activate_after_both_seats_check_the_definitions() {
    const STACK: usize = 128 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let module = n("Init.Prelude");
            let inputs = [OleanModuleInput {
                name: &module,
                artifact: include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                ),
                server_artifact: Some(include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                )),
                private_artifact: Some(include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                )),
            }];
            let base = Engine::builder().build_empty();
            let root = base.logical_root(&KVMap::new());
            let receipt = base
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&module),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        16 << 20,
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(base.logical_root(&KVMap::new()), root);
            assert_eq!(receipt.modules[0].aux_recursors, 317);
            assert!(
                !receipt.modules[0]
                    .uninterpreted
                    .contains(&n("Lean.auxRecExt"))
            );
            let tags = AuxRecursors::read(receipt.engine.environment()).unwrap();
            assert_eq!(tags.len(), 317);
            for tagged in tags.iter() {
                assert!(matches!(
                    receipt.engine.environment().find(tagged),
                    Some(ConstantInfo::Defn(_))
                ));
            }
            assert!(tags.contains(&n("Nat.recOn")));
            assert!(tags.contains(&n("Nat.casesOn")));
            assert!(!tags.contains(&n("Nat.add")));
            assert!(!tags.contains(&n("Eq.ndrec")));

            // These are the real nested Array/List recursors retained in
            // Prelude. Their data-producing motive is not the first motive.
            // The pinned Reference refuses all three exact partial applications.
            let boundary_cases = [
                (
                    "def blocked := @Lean.Syntax.brecOn_1 (fun _ => Prop) (fun _ => Nat) (fun _ => Prop)",
                    "Failed to find LCNF signature for Lean.Syntax.brecOn_1",
                ),
                (
                    "def blocked := @Lean.Syntax.brecOn_2.{1} (fun _ => Prop) (fun _ => Prop) (fun _ => Nat)",
                    "Failed to find LCNF signature for Lean.Syntax.brecOn_2",
                ),
                (
                    "def blocked := @Lean.Syntax.rec_1 (fun _ => Prop) (fun _ => Nat) (fun _ => Prop)",
                    "code generator does not support recursor `Lean.Syntax.rec_1`",
                ),
            ];
            for (source, expected) in boundary_cases {
                let error = receipt
                    .engine
                    .check_source_files(
                        &[source.as_bytes()],
                        &KVMap::new(),
                        SourceCheckLimits::new(admission()),
                    )
                    .expect_err("a nested data motive must require the compiled signature");
                assert!(error.to_string().contains(expected), "{source}\n{error}");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn encoded(constants: &[ConstantInfo], tagged: &[Name], imports: &[ModuleImport]) -> Vec<u8> {
    encode_module_with_source_metadata(
        ModuleWriteInput {
            is_module: false,
            imports,
            constants,
            extra_const_names: &[],
        },
        &SourceMetadata {
            aux_recursors: tagged.to_vec(),
            ..SourceMetadata::default()
        },
        OleanWriteHeader {
            version: fln_olean::format::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln_olean::format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln_olean::format::PIN_COMMIT,
            base_addr: 2 * fln_olean::format::REGION_ALIGN as u64,
        },
        OleanWriteBudget::default(),
    )
    .unwrap()
    .bytes
}

#[test]
fn imported_tags_require_an_owned_definition_and_preserve_the_base_on_failure() {
    let base = ConstantVal {
        name: n("Generated.recOn"),
        level_params: Vec::new(),
        type_: Expr::sort(Level::one()),
    };
    let constants = [
        ConstantInfo::Defn(DefinitionVal {
            all: vec![base.name.clone()],
            base: base.clone(),
            value: Expr::sort(Level::zero()),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
        }),
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("User.casesOn"),
                ..base
            },
            is_unsafe: false,
        }),
    ];
    let engine = Engine::builder().build_empty();
    let root = engine.logical_root(&KVMap::new());
    let module = n("Main");
    for tagged in [n("User.casesOn"), n("Missing.recOn")] {
        let bytes = encoded(&constants, &[tagged], &[]);
        let result = engine.import_olean_modules_for_source(
            &[OleanModuleInput {
                name: &module,
                artifact: &bytes,
                server_artifact: None,
                private_artifact: None,
            }],
            std::slice::from_ref(&module),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(1 << 20, admission().kernel)),
        );
        assert!(matches!(
            result,
            Err(SourceOleanImportError::Metadata { .. })
        ));
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    // Even an already admitted definition cannot acquire a tag from a module
    // that merely imports it: the pin consults the declaration owner's array.
    let library_name = n("Library");
    let library = encoded(&constants, &[], &[]);
    let main = encoded(
        &[],
        &[n("Generated.recOn")],
        &[ModuleImport {
            module: library_name.clone(),
            is_exported: true,
            is_meta: false,
            import_all: false,
        }],
    );
    let result = engine.import_olean_modules_for_source(
        &[
            OleanModuleInput {
                name: &library_name,
                artifact: &library,
                server_artifact: None,
                private_artifact: None,
            },
            OleanModuleInput {
                name: &module,
                artifact: &main,
                server_artifact: None,
                private_artifact: None,
            },
        ],
        std::slice::from_ref(&module),
        &KVMap::new(),
        SourceOleanImportLimits::new(OleanCheckLimits::new(1 << 20, admission().kernel)),
    );
    assert!(matches!(
        result,
        Err(SourceOleanImportError::Metadata { module: owner, declaration, .. })
            if owner == module && declaration == n("Generated.recOn")
    ));
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
