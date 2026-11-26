//! Declaration-owned extraction policy survives artifacts, visibility and replay.
#![forbid(unsafe_code)]
use super::*;
use std::collections::BTreeSet;

const LIBRARY: &str = r#"prelude
namespace Tagged
@[never_extract] axiom carrier : Type
@[never_extract] inductive Choice where | first | second
@[never_extract] def choose : Choice := Choice.first
@[never_extract] theorem identity (P : Prop) (h : P) : P := h
@[never_extract] structure Box where
  value : Choice
def later : Choice := Choice.second
attribute [never_extract] later Choice.first
attribute [never_extract] choose
end Tagged
"#;

fn expected() -> BTreeSet<Name> {
    [
        "Tagged.carrier",
        "Tagged.Choice",
        "Tagged.choose",
        "Tagged.identity",
        "Tagged.Box",
        "Tagged.later",
        "Tagged.Choice.first",
    ]
    .into_iter()
    .map(name)
    .collect()
}

#[test]
fn owned_never_extract_tags_survive_diamond_cache_and_persisted_readmission() {
    use fln::source_check::modules::persisted::{
        PersistedModules, SourceModuleKey, SourceModuleStore,
    };
    use fln::source_check::modules::reuse::CheckerIdentity;
    use std::cell::RefCell;
    use std::collections::BTreeMap;

    #[derive(Default)]
    struct Records(RefCell<BTreeMap<SourceModuleKey, Vec<u8>>>);
    impl SourceModuleStore for Records {
        fn load(&self, key: SourceModuleKey) -> Result<Option<Vec<u8>>, String> {
            Ok(self.0.borrow().get(&key).cloned())
        }
        fn save(&self, key: SourceModuleKey, bytes: &[u8]) -> Result<(), String> {
            self.0.borrow_mut().insert(key, bytes.to_vec());
            Ok(())
        }
    }

    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    let modules = [name("Lib"), name("Left"), name("Right"), name("Main")];
    let sources = [
        LIBRARY,
        "prelude\nimport Lib\ndef left : Tagged.Choice := Tagged.choose",
        "prelude\nimport Lib\ndef right : Tagged.Choice := Tagged.later",
        "prelude\nimport Left\nimport Right\ndef use : Tagged.Choice := left",
    ];
    let inputs: Vec<_> = modules
        .iter()
        .zip(sources)
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let records = Records::default();
    let new_session = || {
        SourceModuleSession::new(
            initial.clone(),
            KVMap::new(),
            limits(),
            SourceModuleCacheLimits::default(),
        )
    };
    let compile = |session: &mut SourceModuleSession| {
        session
            .compile_with_records(
                &inputs,
                &modules[3],
                OleanWriteBudget::default(),
                Some(PersistedModules {
                    checker: CheckerIdentity::of_executable(b"checked-never-extract-replay"),
                    store: &records,
                }),
                None,
            )
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let mut session = new_session();
    let cold = compile(&mut session);
    assert_eq!((cold.elaborated_modules, cold.persisted_modules), (4, 0));
    let warm = compile(&mut session);
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (4, 0));
    let restored = compile(&mut new_session());
    assert_eq!(
        (restored.persisted_modules, restored.elaborated_modules),
        (4, 0)
    );
    for result in [&cold, &warm, &restored] {
        assert_eq!(
            fln_elab::never_extract::read(result.checked.checked.engine.environment()).unwrap(),
            expected()
        );
        assert_eq!(
            result.checked.checked.result_logical_root,
            cold.checked.checked.result_logical_root
        );
        for (original, actual) in cold.artifacts.iter().zip(&result.artifacts) {
            assert_eq!(actual.name, original.name);
            assert_eq!(actual.bytes, original.bytes);
            let rows = metadata(&actual.bytes).never_extract;
            if actual.name == modules[0] {
                assert_eq!(rows.into_iter().collect::<BTreeSet<_>>(), expected());
            } else {
                assert!(
                    rows.is_empty(),
                    "an importer cannot re-export another module's tags"
                );
            }
        }
    }
    let receipt = imported(&restored);
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|module| module.never_extract)
            .sum::<usize>(),
        7
    );
    let env = receipt.engine.environment();
    assert_eq!(fln_elab::never_extract::read(env).unwrap(), expected());
    assert!(fln_elab::never_extract::has_tag(env, &name("Tagged.choose._lambda.child")).unwrap());
    assert!(!fln_elab::never_extract::has_tag(env, &name("Tagged.choose.child")).unwrap());
    assert_eq!(initial.logical_root(&KVMap::new()), root);
    assert!(initial.environment().is_empty());

    // The oracle loads our physical artifact; it cannot rebuild this module.
    aliases::reference_import(
        &restored,
        r#"prelude
import Lean
import Main
run_cmd do
  let env ← Lean.getEnv
  for n in [`Tagged.carrier, `Tagged.Choice, `Tagged.choose, `Tagged.identity,
            `Tagged.Box, `Tagged.later, `Tagged.Choice.first,
            `Tagged.choose._lambda.child] do
    unless Lean.hasNeverExtractAttribute env n do
      throwError "missing never_extract policy for {n}"
  if Lean.hasNeverExtractAttribute env `Tagged.choose.child then
    throwError "ordinary child inherited never_extract"
"#,
        true,
    );
}

#[test]
fn never_extract_remains_global_owned_argument_free_and_kernel_checked() {
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    let module = name("Policy");
    // These inputs have module headers, so both the positive control and the
    // refusals must go through the module checker rather than the command API.
    let valid = initial
        .check_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: b"prelude\naxiom target : Type\nattribute [never_extract] target\n@[never_extract] theorem valid (P : Prop) (h : P) : P := h",
            }],
            &module,
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        fln_elab::never_extract::read(valid.checked.engine.environment()).unwrap(),
        BTreeSet::from([name("target"), name("valid")])
    );
    assert_eq!(valid.checked.theorems, 1);
    for (source, expected_command) in [
        (
            "prelude\naxiom target : Type\nattribute [local never_extract] target",
            1,
        ),
        (
            "prelude\nnamespace Tagged\naxiom target : Type\nattribute [scoped never_extract] target\nend Tagged",
            2,
        ),
        (
            "prelude\naxiom target : Type\nattribute [never_extract 1] target",
            1,
        ),
        (
            "prelude\n@[never_extract] axiom target : Type\nattribute [-never_extract] target",
            1,
        ),
        (
            "prelude\naxiom target : Type\nattribute [never_extract] target missing",
            1,
        ),
        (
            "prelude\n@[never_extract] theorem invalid (P Q : Prop) (h : P) : Q := h",
            0,
        ),
    ] {
        let error = initial
            .check_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                }],
                &module,
                &KVMap::new(),
                limits(),
            )
            .err()
            .unwrap_or_else(|| panic!("invalid module was not refused: {source}"));
        assert!(
            matches!(
                &error,
                SourceModuleCheckError::Source {
                    error: fln::SourceCheckError::Scope { command, .. }
                        | fln::SourceCheckError::Command { command, .. },
                    ..
                } if *command == expected_command
            ),
            "expected refusal at command {expected_command}: {source}: {error}"
        );
        assert_eq!(initial.logical_root(&KVMap::new()), root);
        assert!(initial.environment().is_empty());
        assert!(
            fln_elab::never_extract::read(initial.environment())
                .unwrap()
                .is_empty()
        );
    }
    let built = compiled(&[("Main", "prelude\nimport Lib"), ("Lib", LIBRARY)]);
    let receipt = imported(&built);
    let root = receipt.engine.logical_root(&KVMap::new());
    let imported_target = "attribute [never_extract] Tagged.choose";
    assert!(
        receipt
            .engine
            .check_source_files(
                &[imported_target.as_bytes()],
                &KVMap::new(),
                limits().source
            )
            .is_err()
    );
    assert_eq!(receipt.engine.logical_root(&KVMap::new()), root);
    assert_eq!(
        fln_elab::never_extract::read(receipt.engine.environment()).unwrap(),
        expected()
    );
    aliases::reference_import(
        &built,
        &format!("prelude\nimport Main\n{imported_target}"),
        false,
    );
}

#[test]
fn foreign_never_extract_rows_require_an_admitted_owning_declaration() {
    use fln::source_check::modules::imported::SourceOleanImportError;
    use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};

    let built = compiled(&[
        ("Lib", "prelude\naxiom dependency : Type"),
        ("Main", "prelude\nimport Lib\naxiom localTag : Type"),
    ]);
    let library = built
        .artifacts
        .iter()
        .find(|artifact| artifact.name == name("Lib"))
        .unwrap();
    let constants = [built
        .checked
        .checked
        .engine
        .environment()
        .find(&name("localTag"))
        .unwrap()
        .clone()];
    let imports = [fln::OleanModuleImport {
        module: library.name.clone(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let encode = |declaration: &str| {
        encode_module_with_source_metadata(
            fln::OleanModuleWriteInput {
                is_module: false,
                imports: &imports,
                constants: &constants,
                extra_const_names: &[],
            },
            &SourceMetadata {
                never_extract: vec![name(declaration)],
                ..SourceMetadata::default()
            },
            fln::OleanWriteHeader {
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
    };
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    let main = name("Main");
    let activate = |artifact: &[u8], budget: SourceOleanImportLimits| {
        initial.import_olean_modules_for_source(
            &[
                OleanModuleInput {
                    name: &library.name,
                    artifact: &library.bytes,
                    server_artifact: None,
                    private_artifact: None,
                },
                OleanModuleInput {
                    name: &main,
                    artifact,
                    server_artifact: None,
                    private_artifact: None,
                },
            ],
            std::slice::from_ref(&main),
            &KVMap::new(),
            budget,
        )
    };
    let budget = || {
        SourceOleanImportLimits::new(OleanCheckLimits::new(
            4 << 20,
            limits().source.admission.kernel,
        ))
    };
    let valid = encode("localTag");
    let accepted = activate(&valid, budget()).unwrap().into_complete().unwrap();
    assert!(
        fln_elab::never_extract::has_tag(accepted.engine.environment(), &name("localTag")).unwrap()
    );
    for declaration in ["dependency", "missing"] {
        let error = activate(&encode(declaration), budget()).unwrap_err();
        assert!(
            matches!(error, SourceOleanImportError::Metadata { declaration: actual, .. } if actual == name(declaration)),
            "{declaration}"
        );
        assert_eq!(initial.logical_root(&KVMap::new()), root);
        assert!(initial.environment().is_empty());
    }
    let mut exhausted = budget();
    exhausted.metadata.max_entries = 0;
    assert!(matches!(
        activate(&valid, exhausted),
        Err(SourceOleanImportError::Limit(_))
    ));
    let recovered = activate(&valid, budget()).unwrap().into_complete().unwrap();
    assert_eq!(
        recovered.engine.logical_root(&KVMap::new()),
        accepted.engine.logical_root(&KVMap::new())
    );
    assert_eq!(initial.logical_root(&KVMap::new()), root);
}

#[test]
fn public_never_extract_exports_do_not_reveal_private_tags() {
    let built = compiled(&[
        (
            "Lib",
            "module\nprelude\n@[never_extract] public axiom visible : Type\n@[never_extract] private axiom secret : Type",
        ),
        (
            "Main",
            "module\nprelude\npublic import Lib\npublic axiom use : visible",
        ),
    ]);
    let library = built
        .artifacts
        .iter()
        .find(|artifact| artifact.name == name("Lib"))
        .unwrap();
    assert!(library.companions.is_some());
    assert_eq!(metadata(&library.bytes).never_extract, [name("visible")]);
    let receipt = imported(&built);
    let private = Name::num(name("_private.Lib"), 0).append_core(&name("secret"));
    // The physical loader retains checked private companions. Public source
    // imports select their exported contexts instead of exposing that world.
    assert_eq!(
        fln_elab::never_extract::read(receipt.engine.environment()).unwrap(),
        BTreeSet::from([name("visible"), private.clone()])
    );
    assert!(receipt.engine.environment().contains(&private));
    let use_name = name("Use");
    let checked = receipt
        .check_source_modules(
            &[SourceModuleInput {
                name: &use_name,
                source: b"module\nprelude\npublic import Main\npublic axiom consumer : visible",
            }],
            &use_name,
            &KVMap::new(),
            limits(),
            None,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(!checked.checked.engine.environment().contains(&private));
    assert!(
        checked
            .checked
            .engine
            .environment()
            .contains(&name("visible"))
    );
    assert_eq!(
        fln_elab::never_extract::read(checked.checked.engine.environment()).unwrap(),
        BTreeSet::from([name("visible")])
    );
}
