//! Pattern aliases remain usable across checked artifact and cache boundaries.
#![forbid(unsafe_code)]
use super::*;

const LIBRARY: &str = r#"prelude
inductive Color where | red | blue
inductive Same (left : Color) : Color → Prop where
  | refl : Same left left
@[match_pattern] def scarlet : Color := Color.red
def untagged : Color := Color.blue
"#;

const CONSUMER: &str = r#"prelude
import Lib
def classify (color : Color) : Color := match color with
  | scarlet => Color.red
  | _ => Color.blue
theorem classify_red : Same (classify Color.red) Color.red := @Same.refl Color.red
theorem classify_blue : Same (classify Color.blue) Color.blue := @Same.refl Color.blue
"#;

#[test]
fn pattern_aliases_survive_compiled_import_cache_reuse_and_persisted_readmission() {
    use fln::source_check::modules::persisted::{
        PersistedModules, SourceModuleKey, SourceModuleStore,
    };
    use fln::source_check::modules::reuse::CheckerIdentity;
    use std::cell::RefCell;
    use std::collections::{BTreeMap, BTreeSet};

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
    let modules = [name("Lib"), name("Main")];
    let inputs = [
        SourceModuleInput {
            name: &modules[0],
            source: LIBRARY.as_bytes(),
        },
        SourceModuleInput {
            name: &modules[1],
            source: CONSUMER.as_bytes(),
        },
    ];
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
                &modules[1],
                OleanWriteBudget::default(),
                Some(PersistedModules {
                    checker: CheckerIdentity::of_executable(b"checked-match-pattern-replay"),
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
    assert_eq!((cold.elaborated_modules, cold.persisted_modules), (2, 0));
    assert!(cold.checked.checked.theorems >= 2);
    for declaration in ["classify_red", "classify_blue"] {
        assert!(matches!(
            cold.checked
                .checked
                .engine
                .environment()
                .find(&name(declaration)),
            Some(fln::ConstantInfo::Thm(_)),
        ));
    }
    let warm = compile(&mut session);
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (2, 0));
    let restored = compile(&mut new_session());
    assert_eq!(
        (restored.persisted_modules, restored.elaborated_modules),
        (2, 0)
    );
    for result in [&cold, &warm, &restored] {
        assert_eq!(
            result.checked.checked.theorems,
            cold.checked.checked.theorems
        );
        assert_eq!(
            result.checked.checked.result_logical_root,
            cold.checked.checked.result_logical_root
        );
        for (original, actual) in cold.artifacts.iter().zip(&result.artifacts) {
            assert_eq!(actual.name, original.name);
            assert_eq!(actual.bytes, original.bytes);
            let tags = metadata(&actual.bytes).match_patterns;
            if actual.name == modules[0] {
                assert_eq!(tags, [name("scarlet")]);
            } else {
                assert!(
                    tags.is_empty(),
                    "an importer must not re-export its dependency's tag"
                );
            }
        }
    }
    // Reading physical .olean bytes invokes both ordinary admission engines;
    // successful in-memory source checking alone cannot satisfy this probe.
    let receipt = imported(&restored);
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|module| module.match_patterns)
            .sum::<usize>(),
        1
    );
    assert_eq!(
        fln_elab::match_pattern::read(receipt.engine.environment()).unwrap(),
        BTreeSet::from([name("scarlet")])
    );
    let checked = receipt
        .engine
        .check_source_files(
            &[
                br#"def classifyAgain (color : Color) : Color := match color with
  | scarlet => Color.red
  | _ => Color.blue
theorem imported_red : Same (classifyAgain Color.red) Color.red := @Same.refl Color.red
theorem imported_blue : Same (classifyAgain Color.blue) Color.blue := @Same.refl Color.blue
"#,
            ],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(checked.theorems >= 2);
    for declaration in ["imported_red", "imported_blue"] {
        assert!(matches!(
            checked.engine.environment().find(&name(declaration)),
            Some(fln::ConstantInfo::Thm(_)),
        ));
    }
    assert_eq!(initial.logical_root(&KVMap::new()), root);
    assert!(initial.environment().is_empty());
}

#[test]
fn imported_pattern_tags_require_owned_well_typed_exposed_definitions() {
    use fln::source_check::modules::imported::SourceOleanImportError;
    use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};

    let built = compiled(&[
        ("Lib", LIBRARY),
        (
            "Main",
            "prelude\nimport Lib\naxiom opaquePattern : Color\ndef localAlias : Color := Color.blue",
        ),
    ]);
    let library = built
        .artifacts
        .iter()
        .find(|artifact| artifact.name == name("Lib"))
        .unwrap();
    let environment = built.checked.checked.engine.environment();
    let constants: Vec<_> = ["opaquePattern", "localAlias"]
        .map(|decl| environment.find(&name(decl)).unwrap().clone())
        .into();
    let imports = [fln::OleanModuleImport {
        module: library.name.clone(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let encode = |constants: &[fln::ConstantInfo], declaration: &str| {
        encode_module_with_source_metadata(
            fln::OleanModuleWriteInput {
                is_module: false,
                imports: &imports,
                constants,
                extra_const_names: &[],
            },
            &SourceMetadata {
                match_patterns: vec![name(declaration)],
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
    let valid = encode(&constants, "localAlias");
    let accepted = activate(&valid, budget()).unwrap().into_complete().unwrap();
    assert!(
        fln_elab::match_pattern::read(accepted.engine.environment())
            .unwrap()
            .contains(&name("localAlias"))
    );
    for declaration in ["opaquePattern", "untagged", "missing"] {
        let error = activate(&encode(&constants, declaration), budget()).unwrap_err();
        match error {
            SourceOleanImportError::Metadata {
                module,
                declaration: actual,
                ..
            } => {
                assert_eq!(module, main);
                assert_eq!(actual, name(declaration));
            }
            other => panic!("{declaration}: {other:?}"),
        }
        assert_eq!(initial.logical_root(&KVMap::new()), root);
        assert!(initial.environment().is_empty());
    }
    let mut wrong = constants.clone();
    let fln::ConstantInfo::Defn(definition) = &mut wrong[1] else {
        panic!("localAlias is a definition")
    };
    definition.value = fln::Expr::const_(name("Color"), vec![]);
    assert!(
        activate(&encode(&wrong, "localAlias"), budget()).is_err(),
        "a tag cannot admit a body of the wrong type"
    );
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
fn public_pattern_exports_keep_private_alias_bodies_hidden() {
    let library = r#"module
prelude
public inductive Color where | red | blue
@[expose, match_pattern] public def scarlet : Color := Color.red
@[match_pattern] private def secretAlias : Color := Color.blue
"#;
    let consumer = r#"module
prelude
public import Lib
@[expose] public def select (color : Color) : Color := match color with
  | scarlet => Color.red
  | _ => Color.blue
public def selected (P : Color → Prop) (h : P Color.red) : P (select Color.red) := h
"#;
    let built = compiled(&[("Lib", library), ("Main", consumer)]);
    let library = built
        .artifacts
        .iter()
        .find(|artifact| artifact.name == name("Lib"))
        .unwrap();
    assert!(library.companions.is_some());
    assert_eq!(metadata(&library.bytes).match_patterns, [name("scarlet")]);
    let private = Name::num(name("_private.Lib"), 0).append_core(&name("secretAlias"));
    assert!(
        !built
            .checked
            .checked
            .engine
            .environment()
            .contains(&private)
    );
    let receipt = imported(&built);
    let use_name = name("Use");
    let checked = receipt.check_source_modules(
        &[SourceModuleInput {
            name: &use_name,
            source: b"module\nprelude\npublic import Main\npublic def use (P : Color -> Prop) (h : P Color.red) : P (select Color.red) := h",
        }],
        &use_name,
        &KVMap::new(),
        limits(),
        None,
    ).unwrap().into_complete().unwrap();
    assert!(!checked.checked.engine.environment().contains(&private));
    assert!(
        !fln_elab::match_pattern::read(checked.checked.engine.environment())
            .unwrap()
            .contains(&private)
    );
}
