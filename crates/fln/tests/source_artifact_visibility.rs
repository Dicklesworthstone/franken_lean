//! Real module-system artifacts retain separate checked logical and executable
//! views. These fixtures need no prelude seed, unsafe axiom, or Reference files.
#![forbid(unsafe_code)]

use fln::source_check::modules::execution::SourceProgramLimits;
use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::source_check::modules::{
    SourceModuleBuild, SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
};
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    OleanCheckLimits, OleanModuleInput, OleanWriteBudget, Outcome, SourceCheckLimits,
    SourceModuleInput, VmExit,
};
use fln_elab::instances::InstanceRegistry;
use std::sync::OnceLock;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn private(module: &str, declaration: &str) -> Name {
    Name::num(n(&format!("_private.{module}")), 0).append_core(&n(declaration))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 << 20),
    )))
}

const BASE: &str = "module\nprelude\n@[expose] public section\ninductive Token where\n| left\n| right\n| extra\nclass Pick (A : Type) where\n  value : A\ndef chosen {A : Type} [p : Pick A] : A := p.value\n";
const SECRET: &str =
    "module\nprelude\npublic import Base\npublic def transitive : Token := Token.extra\n";
const PRODUCER: &str = "module\nprelude\npublic import Base\nimport Secret\nprivate def privateValue : Token := Token.left\npublic def hidden : Token := privateValue\npublic def indirect : Token := transitive\n@[expose] public def exposed : Token := Token.right\npublic instance visible : Pick Token := Pick.mk Token.left\nprivate instance privateChoice : Pick Token := Pick.mk Token.right\n";
const LIBRARY: &[(&str, &str)] = &[("Producer", PRODUCER), ("Base", BASE), ("Secret", SECRET)];

fn compile(files: &[(&str, &str)]) -> SourceModuleBuild {
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
        .compile_source_modules(
            &inputs,
            &names[0],
            &KVMap::new(),
            limits(),
            OleanWriteBudget::default(),
        )
        .unwrap_or_else(|error| panic!("{files:?}: {error:?}"))
        .into_complete()
        .unwrap()
}

fn import(built: &SourceModuleBuild, root: &str) -> SourceOleanImport {
    let inputs: Vec<_> = built
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: artifact
                .companions
                .as_ref()
                .map(|parts| parts.server.as_slice()),
            private_artifact: artifact
                .companions
                .as_ref()
                .map(|parts| parts.private.as_slice()),
        })
        .collect();
    Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &inputs,
            &[n(root)],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                8 << 20,
                limits().source.admission.kernel,
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap()
}

fn receipt() -> &'static SourceOleanImport {
    static RECEIPT: OnceLock<SourceOleanImport> = OnceLock::new();
    RECEIPT.get_or_init(|| import(&compile(LIBRARY), "Producer"))
}

fn from_artifact(source: &str) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let main = n("Main");
    receipt().check_source_modules(
        &[SourceModuleInput {
            name: &main,
            source: source.as_bytes(),
        }],
        &main,
        &KVMap::new(),
        limits(),
        None,
    )
}

fn from_source(source: &str) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let mut files = vec![("Main", source)];
    files.extend_from_slice(LIBRARY);
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    Engine::builder().build_empty().check_source_modules(
        &inputs,
        &names[0],
        &KVMap::new(),
        limits(),
    )
}

fn both(source: &str) -> [Result<Outcome<SourceModuleCheck>, SourceModuleCheckError>; 2] {
    [from_source(source), from_artifact(source)]
}

fn complete(
    result: Result<Outcome<SourceModuleCheck>, SourceModuleCheckError>,
) -> SourceModuleCheck {
    result
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap()
}

fn rejected(source: &str) {
    for result in both(source) {
        assert!(
            matches!(result, Err(SourceModuleCheckError::Source { module, .. }) if module == n("Main")),
            "{source}"
        );
    }
}

#[test]
fn ordinary_modern_artifacts_preserve_actual_opaque_interfaces_and_private_name_absence() {
    for result in both("module\nprelude\npublic import Producer\n") {
        let result = complete(result);
        let env = result.checked.engine.environment();
        assert!(matches!(
            env.find(&n("hidden")),
            Some(ConstantInfo::Axiom(_))
        ));
        assert!(matches!(
            env.find(&n("indirect")),
            Some(ConstantInfo::Axiom(_))
        ));
        assert!(matches!(
            env.find(&n("exposed")),
            Some(ConstantInfo::Defn(_))
        ));
        assert!(!env.contains(&private("Producer", "privateValue")));
        assert!(!env.contains(&private("Producer", "privateChoice")));
        assert!(!env.contains(&n("privateValue")));
        assert!(!env.contains(&n("transitive")));
    }
    // A dependent argument forces exactly the same conversion as an rfl proof,
    // without installing synthetic equality axioms into the empty foundation.
    rejected(
        "module\nprelude\npublic import Producer\ndef leak (P : Token -> Type) (x : P Token.left) : P hidden := x\n",
    );
    rejected("module\nprelude\npublic import Producer\ndef leak : Token := privateValue\n");
    rejected("module\nprelude\npublic import Producer\ndef leak : Token := transitive\n");
}

#[test]
fn legacy_and_explicit_all_imports_replay_bodies_without_creating_short_private_aliases() {
    for header in [
        "prelude\nimport Producer",
        "module\nprelude\nimport all Producer",
    ] {
        let source = format!(
            "{header}\ndef witness (P : Token -> Type) (x : P Token.left) : P hidden := x\n"
        );
        for result in both(&source) {
            let result = complete(result);
            let env = result.checked.engine.environment();
            assert!(matches!(
                env.find(&n("hidden")),
                Some(ConstantInfo::Defn(_))
            ));
            assert!(env.contains(&private("Producer", "privateValue")));
            assert!(!env.contains(&n("privateValue")));
        }
        rejected(&format!("{header}\ndef leak : Token := privateValue\n"));
    }
}

#[test]
fn import_all_is_not_transitive_over_an_ordinary_import_and_never_opens_the_public_world() {
    let all = "module\nprelude\npublic import Producer\nimport all Producer\n";
    for result in both(all) {
        let result = complete(result);
        let env = result.checked.engine.environment();
        assert!(matches!(
            env.find(&n("hidden")),
            Some(ConstantInfo::Defn(_))
        ));
        assert!(matches!(
            env.find(&n("indirect")),
            Some(ConstantInfo::Defn(_))
        ));
        assert!(matches!(
            env.find(&n("transitive")),
            Some(ConstantInfo::Axiom(_))
        ));
    }
    rejected(&format!(
        "{all}\ndef leak (P : Token -> Type) (x : P Token.extra) : P indirect := x\n"
    ));
    rejected(&format!(
        "{all}\n@[expose] public def leak (P : Token -> Type) (x : P Token.left) : P hidden := x\n"
    ));
    for result in both(
        "prelude\nimport Producer\ndef witness (P : Token -> Type) (x : P Token.extra) : P indirect := x\n",
    ) {
        complete(result);
    }
}

#[test]
fn artifact_instance_selection_uses_the_selected_journal_and_preserves_private_order() {
    for (header, token, selected, count) in [
        (
            "module\nprelude\npublic import Producer",
            "left",
            n("visible"),
            1,
        ),
        (
            "module\nprelude\nimport all Producer",
            "right",
            private("Producer", "privateChoice"),
            2,
        ),
        (
            "prelude\nimport Producer",
            "right",
            private("Producer", "privateChoice"),
            2,
        ),
    ] {
        let source = format!(
            "{header}\ndef witness (P : Token -> Type) (x : P Token.{token}) : P chosen := x\n"
        );
        for result in both(&source) {
            let result = complete(result);
            let env = result.checked.engine.environment();
            let registry = InstanceRegistry::read(env).unwrap();
            let candidates = registry.candidates(&n("Pick"));
            assert_eq!(candidates.len(), count);
            assert_eq!(candidates[0].declaration, selected);
            assert_eq!(
                env.contains(&private("Producer", "privateChoice")),
                count == 2
            );
        }
    }
}

#[test]
fn serialized_import_all_retains_its_flag_and_its_private_scope() {
    let main = "module\nprelude\nimport all Producer\ndef witness (P : Token -> Type) (x : P Token.left) : P hidden := x\n";
    let mut files = vec![("Main", main)];
    files.extend_from_slice(LIBRARY);
    let built = compile(&files);
    let artifact = built
        .artifacts
        .iter()
        .find(|artifact| artifact.name == n("Main"))
        .unwrap();
    let decoded =
        fln::decode_olean_artifact(&artifact.bytes, fln::OleanDecodeLimits::new(8 << 20)).unwrap();
    assert_eq!(decoded.module.imports.len(), 1);
    assert_eq!(decoded.module.imports[0].module, n("Producer"));
    assert!(decoded.module.imports[0].import_all);
    assert!(!decoded.module.imports[0].is_exported);
    let imported = import(&built, "Main");
    let client = n("Client");
    let result = imported
        .check_source_modules(
            &[SourceModuleInput {
                name: &client,
                source: b"module\nprelude\npublic import Main\n",
            }],
            &client,
            &KVMap::new(),
            limits(),
            None,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(!result.checked.engine.environment().contains(&n("hidden")));
    assert!(!result.checked.engine.environment().contains(&n("Token")));
}

fn returned_tag(exit: &VmExit, tag: u8) {
    let VmExit::Returned(returned) = exit else {
        panic!("expected a constructor result, got {exit:?}")
    };
    assert!(!returned.value.is_scalar());
    assert_eq!(returned.value.header().tag, tag);
}

#[test]
fn modern_opaque_imports_execute_from_checked_private_bodies_and_replay_bytecode() {
    let changed = PRODUCER.replacen(
        "private def privateValue : Token := Token.left",
        "private def privateValue : Token := Token.right",
        1,
    );
    let changed = import(
        &compile(&[("Producer", &changed), ("Base", BASE), ("Secret", SECRET)]),
        "Producer",
    );
    let mut first_header = None;
    let mut first_bytecode = None;
    for (receipt, expected) in [(receipt(), [0, 1, 2, 0]), (&changed, [1, 1, 2, 1])] {
        let main = n("Main");
        let source = b"module\nprelude\npublic import Producer\n#eval hidden\n#eval exposed\n#eval indirect\n#eval (fun x : Token => x) hidden\n";
        let program = receipt
            .execute_source_modules(
                &[SourceModuleInput {
                    name: &main,
                    source,
                }],
                &main,
                &KVMap::new(),
                SourceProgramLimits::new(EngineExecutionLimits::new(
                    limits().source.admission.kernel,
                )),
                None,
            )
            .unwrap_or_else(|error| panic!("{error:?}"))
            .into_complete()
            .unwrap();
        let commands = &program.modules.last().unwrap().commands;
        assert_eq!(commands.batch.source_evaluation_indices.len(), 4);
        for (&index, tag) in commands
            .batch
            .source_evaluation_indices
            .iter()
            .zip(expected)
        {
            let execution = &commands.batch.executions[index];
            returned_tag(&execution.exit, tag);
            let replay = fln::execute_flbc_artifact(
                &execution.flbc_artifact,
                &KVMap::new(),
                Default::default(),
            )
            .unwrap()
            .into_complete()
            .unwrap();
            returned_tag(&replay, tag);
        }
        let env = commands.batch.engine.environment();
        let header = env.find(&n("hidden")).unwrap();
        assert!(matches!(header, ConstantInfo::Axiom(_)));
        assert!(!env.contains(&private("Producer", "privateValue")));
        assert!(!env.contains(&n("transitive")));
        let bytecode =
            &commands.batch.executions[commands.batch.source_evaluation_indices[0]].flbc_artifact;
        if let Some(first_header) = &first_header {
            assert_eq!(first_header, header, "private code changed no public type");
            assert_ne!(
                first_bytecode.as_ref().unwrap(),
                bytecode,
                "changed implementation must not reuse old code"
            );
        } else {
            first_header = Some(header.clone());
            first_bytecode = Some(bytecode.clone());
        }
    }
}

#[test]
fn a_new_checked_name_cannot_replace_a_hidden_runtime_implementation() {
    let checked = complete(from_artifact("module\nprelude\npublic import Producer\n"));
    let engine = &checked.checked.engine;
    let name = private("Producer", "privateValue");
    assert!(!engine.environment().contains(&name));
    let declaration = fln::Declaration::Defn(fln::DefinitionVal {
        base: fln::ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_: fln::Expr::const_(n("Token"), Vec::new()),
        },
        value: fln::Expr::const_(n("Token.extra"), Vec::new()),
        hints: fln::ReducibilityHints::Abbrev,
        safety: fln::DefinitionSafety::Safe,
        all: vec![name.clone()],
    });
    let admitted = engine
        .admit_declaration(
            declaration.clone(),
            &KVMap::new(),
            limits().source.admission,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(admitted.engine.environment().contains(&name));
    let Err(error) = engine.execute_definition(
        declaration,
        &KVMap::new(),
        EngineExecutionLimits::new(limits().source.admission.kernel),
    ) else {
        panic!("a checked local name must not replace a hidden imported implementation");
    };
    assert!(matches!(
        error,
        fln::EngineExecutionError::Ingress(fln::IngressError::UnsupportedNode {
            kind: "local declaration collides with a private runtime import",
        })
    ));
    assert!(!engine.environment().contains(&name));
}

#[test]
fn a_raw_import_engine_cannot_impersonate_an_exported_artifact_receipt() {
    let source = b"module\nprelude\npublic import Producer\n";
    let main = n("Main");
    let error = receipt()
        .engine
        .check_source_modules(
            &[SourceModuleInput {
                name: &main,
                source,
            }],
            &main,
            &KVMap::new(),
            limits(),
        )
        .unwrap_err();
    assert!(matches!(
        error,
        SourceModuleCheckError::ImportContext { .. }
    ));
    assert_eq!(error.disposition().0, "inconclusive");
    assert!(matches!(
        receipt().engine.environment().find(&n("hidden")),
        Some(ConstantInfo::Defn(_))
    ));
}

#[test]
fn checked_private_bodies_keep_noncomputable_and_bodyless_dependencies_unavailable() {
    use fln::source_check::SourceCheckError;
    use fln_elab::source::SourceInferenceError;
    use fln_elab::{NatDefinitionElabError, NatDefinitionFrontendError};

    fn dependency(error: SourceModuleCheckError) -> Name {
        let SourceModuleCheckError::Source {
            module,
            error: SourceCheckError::Command { error, .. },
        } = error
        else {
            panic!("expected an ordinary source compiler refusal, got {error:?}")
        };
        assert_eq!(module, n("Main"));
        let mut error = *error;
        loop {
            match error {
                fln::EngineExecutionError::BatchCommand { error: inner, .. } => {
                    error = *inner;
                }
                fln::EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
                    NatDefinitionElabError::Inference(
                        SourceInferenceError::NoncomputableDependency(name),
                    ),
                )) => return name,
                other => panic!("expected a noncomputable dependency, got {other:?}"),
            }
        }
    }

    const UNAVAILABLE: &str = "module\nprelude\npublic import Base\npublic noncomputable def logicalOnly : Token := Token.left\npublic axiom bodyless : Token\n";
    let receipt = import(
        &compile(&[("Unavailable", UNAVAILABLE), ("Base", BASE)]),
        "Unavailable",
    );
    let main = n("Main");
    let unavailable = n("Unavailable");
    let base = n("Base");
    let check = |source: &str| {
        let inputs = [
            SourceModuleInput {
                name: &main,
                source: source.as_bytes(),
            },
            SourceModuleInput {
                name: &unavailable,
                source: UNAVAILABLE.as_bytes(),
            },
            SourceModuleInput {
                name: &base,
                source: BASE.as_bytes(),
            },
        ];
        [
            Engine::builder().build_empty().check_source_modules(
                &inputs,
                &main,
                &KVMap::new(),
                limits(),
            ),
            receipt.check_source_modules(&inputs[..1], &main, &KVMap::new(), limits(), None),
        ]
    };
    for header in [
        "module\nprelude\npublic import Unavailable",
        "module\nprelude\nimport all Unavailable",
        "prelude\nimport Unavailable",
    ] {
        for name in ["logicalOnly", "bodyless"] {
            for result in check(&format!("{header}\ndef use : Token := {name}\n")) {
                assert_eq!(dependency(result.unwrap_err()), n(name));
            }
        }
    }
    // The suppressed failure publishes a fresh local tag after the retained
    // import prefix. A provider frozen to the old snapshot would miss it and
    // incorrectly accept the final definition's reference to localOnly.
    let prefix = "module\nprelude\npublic import Unavailable\nnoncomputable section\npublic def localOnly : Token := logicalOnly\nend\n";
    for result in check(prefix) {
        let checked = complete(result);
        assert!(
            fln_elab::noncomputable::read(checked.checked.engine.environment())
                .unwrap()
                .contains(&n("localOnly"))
        );
    }
    for result in check(&format!("{prefix}def use : Token := localOnly\n")) {
        assert_eq!(dependency(result.unwrap_err()), n("localOnly"));
    }
}
