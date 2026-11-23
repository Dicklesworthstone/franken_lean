//! Symmetry selection survives checked artifacts, scope boundaries, and readmission.
#![forbid(unsafe_code)]
use super::*;

const LIBRARY: &str = r#"prelude
inductive Color where | red | blue
inductive Rel (a b : Color) : Prop where | intro : Rel a b
inductive ScopedRel (a b : Color) : Prop where | intro : ScopedRel a b
inductive LocalRel (a b : Color) : Prop where | intro : LocalRel a b
theorem reverse (a b : Color) (h : Rel a b) : Rel b a := @Rel.intro b a
theorem localReverse (a b : Color) (h : LocalRel a b) : LocalRel b a := @LocalRel.intro b a
namespace Group
theorem scopedReverse (a b : Color) (h : ScopedRel a b) : ScopedRel b a := @ScopedRel.intro b a
attribute [scoped symm] scopedReverse
end Group
"#;
const CONSUMER: &str = r#"prelude
import Lib
attribute [symm] reverse
attribute [symm] reverse
theorem globalUse (a b : Color) (h : Rel a b) : Rel b a := by
  symm
  exact h
open scoped Group
theorem scopedUse (a b : Color) (h : ScopedRel a b) : ScopedRel b a := by
  symm
  exact h
section
attribute [local symm] localReverse
theorem localUse (a b : Color) (h : LocalRel a b) : LocalRel b a := by
  symm
  exact h
end
"#;

#[test]
fn imported_retags_scopes_and_duplicates_survive_artifact_cache_and_persisted_readmission() {
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
                    checker: CheckerIdentity::of_executable(b"checked-symmetry-replay"),
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
    let warm = compile(&mut session);
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (2, 0));
    let restored = compile(&mut new_session());
    assert_eq!(
        (restored.persisted_modules, restored.elaborated_modules),
        (2, 0)
    );
    for result in [&cold, &warm, &restored] {
        assert_eq!(
            result.checked.checked.result_logical_root,
            cold.checked.checked.result_logical_root
        );
        for declaration in ["globalUse", "scopedUse", "localUse"] {
            assert!(matches!(
                result
                    .checked
                    .checked
                    .engine
                    .environment()
                    .find(&name(declaration)),
                Some(fln::ConstantInfo::Thm(_))
            ));
        }
        for (expected, actual) in cold.artifacts.iter().zip(&result.artifacts) {
            assert_eq!(actual.name, expected.name);
            assert_eq!(actual.bytes, expected.bytes);
            let rows = metadata(&actual.bytes).symms;
            if actual.name == modules[0] {
                assert_eq!(rows.len(), 1);
                assert_eq!(rows[0].declaration, name("Group.scopedReverse"));
                assert_eq!(rows[0].scope, Some(name("Group")));
            } else {
                assert_eq!(
                    rows.len(),
                    2,
                    "repeat registrations must survive; local rows must not export"
                );
                assert_eq!(rows[0], rows[1]);
                assert_eq!(rows[0].declaration, name("reverse"));
                assert_eq!(rows[0].scope, None);
            }
        }
    }
    let receipt = imported(&restored);
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|report| report.symms)
            .sum::<usize>(),
        3
    );
    let rows = fln_elab::symm::read(receipt.engine.environment()).unwrap();
    assert_eq!(
        rows.iter()
            .map(|row| row.lemma.declaration.clone())
            .collect::<Vec<_>>(),
        [
            name("Group.scopedReverse"),
            name("reverse"),
            name("reverse")
        ]
    );
    let accepted = receipt
        .engine
        .check_source_files(
            &[
                br#"theorem importedGlobal (a b : Color) (h : Rel a b) : Rel b a := by
  symm
  exact h
open scoped Group
theorem importedScoped (a b : Color) (h : ScopedRel a b) : ScopedRel b a := by
  symm
  exact h
"#,
            ],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(
        accepted.engine.environment().find(&name("importedScoped")),
        Some(fln::ConstantInfo::Thm(_))
    ));
    for relation in ["ScopedRel", "LocalRel"] {
        let source = format!(
            "theorem unavailable (a b : Color) (h : {relation} a b) : {relation} b a := by\n  symm\n  exact h"
        );
        assert!(
            !matches!(
                receipt.engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    limits().source
                ),
                Ok(Outcome::Complete(_))
            ),
            "{relation}: import must restore scope boundaries"
        );
    }
    aliases::reference_import(
        &restored,
        "import Lean.Elab.Tactic.Symm\nimport Main\nexample (a b : Color) (h : Rel a b) : Rel b a := by symm; exact h\nopen scoped Group\nexample (a b : Color) (h : ScopedRel a b) : ScopedRel b a := by symm; exact h",
        true,
    );
    aliases::reference_import(
        &restored,
        "import Lean.Elab.Tactic.Symm\nimport Main\nexample (a b : Color) (h : LocalRel a b) : LocalRel b a := by symm; exact h",
        false,
    );
    assert_eq!(initial.logical_root(&KVMap::new()), root);
    assert!(initial.environment().is_empty());
}

#[test]
fn symmetry_imports_check_lemma_headers_reachable_names_and_shared_key_limits() {
    use fln::source_check::modules::imported::SourceOleanImportError;
    use fln_olean::source_extensions::{DiscrTreeKey, SymmEntry};
    use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};
    let library_source = format!(
        "{LIBRARY}\ninductive Nat where | zero | succ (n : Nat)\ninductive False : Prop\ntheorem falseId (h : False) : False := h\ndef constantNat : Nat := Nat.zero\n"
    );
    let built = compiled(&[
        ("Lib", &library_source),
        (
            "Main",
            "prelude\nimport Lib\ntheorem outsider (a b : Color) (h : Rel a b) : Rel b a := @Rel.intro b a",
        ),
    ]);
    let library = built
        .artifacts
        .iter()
        .find(|artifact| artifact.name == name("Lib"))
        .unwrap();
    let outsider = built
        .checked
        .checked
        .engine
        .environment()
        .find(&name("outsider"))
        .unwrap()
        .clone();
    let main = name("Main");
    let unrelated = name("Unrelated");
    let dependency = |module: &str| fln::OleanModuleImport {
        module: name(module),
        import_all: false,
        is_exported: true,
        is_meta: false,
    };
    let encode = |imports: &[fln::OleanModuleImport],
                  constants: &[fln::ConstantInfo],
                  symms: Vec<SymmEntry>| {
        encode_module_with_source_metadata(
            fln::OleanModuleWriteInput {
                is_module: false,
                imports,
                constants,
                extra_const_names: &[],
            },
            &SourceMetadata {
                symms,
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
    let row = |declaration: &str| SymmEntry {
        declaration: name(declaration),
        keys: vec![DiscrTreeKey::Const(name("Rel"), 0)],
        scope: None,
    };
    let foreign = encode(&[dependency("Lib")], &[outsider], vec![]);
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    let budget = || {
        SourceOleanImportLimits::new(OleanCheckLimits::new(
            4 << 20,
            limits().source.admission.kernel,
        ))
    };
    let activate = |artifact: &[u8], foreign: Option<&[u8]>, roots: &[Name], limits| {
        let mut modules = vec![
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
        ];
        if let Some(artifact) = foreign {
            modules.push(OleanModuleInput {
                name: &unrelated,
                artifact,
                server_artifact: None,
                private_artifact: None,
            });
        }
        initial.import_olean_modules_for_source(&modules, roots, &KVMap::new(), limits)
    };
    let valid = encode(&[dependency("Lib")], &[], vec![row("reverse")]);
    let accepted = activate(&valid, None, std::slice::from_ref(&main), budget())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        fln_elab::symm::read(accepted.engine.environment())
            .unwrap()
            .last()
            .unwrap()
            .lemma
            .declaration,
        name("reverse")
    );
    for declaration in ["falseId", "constantNat"] {
        let artifact = encode(
            &[dependency("Lib")],
            &[],
            vec![row("reverse"), row(declaration)],
        );
        assert!(
            matches!(activate(&artifact, None, std::slice::from_ref(&main), budget()), Err(SourceOleanImportError::Symm { error: fln_elab::symm::SymmRegistryError::InvalidLemma(actual), .. }) if actual == name(declaration)),
            "{declaration}"
        );
        assert_eq!(initial.logical_root(&KVMap::new()), root);
        assert!(
            fln_elab::symm::read(initial.environment())
                .unwrap()
                .is_empty()
        );
    }
    for bad in [
        row("missing"),
        row("outsider"),
        SymmEntry {
            keys: vec![DiscrTreeKey::Const(name("outsider"), 0)],
            ..row("reverse")
        },
    ] {
        let artifact = encode(&[dependency("Lib")], &[], vec![bad]);
        assert!(matches!(
            activate(
                &artifact,
                Some(&foreign),
                &[main.clone(), unrelated.clone()],
                budget()
            ),
            Err(SourceOleanImportError::Metadata { .. })
        ));
        assert_eq!(initial.logical_root(&KVMap::new()), root);
    }
    let reachable = encode(
        &[dependency("Lib"), dependency("Unrelated")],
        &[],
        vec![row("outsider")],
    );
    assert!(
        activate(
            &reachable,
            Some(&foreign),
            std::slice::from_ref(&main),
            budget()
        )
        .unwrap()
        .into_complete()
        .is_ok()
    );
    let mut exhausted = budget();
    exhausted.metadata.max_keys = 0;
    let error = activate(&valid, None, std::slice::from_ref(&main), exhausted).unwrap_err();
    assert!(error.metadata_resource_exhausted());
    let recovered = activate(&valid, None, std::slice::from_ref(&main), budget())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(recovered.result_logical_root, accepted.result_logical_root);
    assert_eq!(initial.logical_root(&KVMap::new()), root);
}

#[test]
fn public_symmetry_exports_keep_private_registrations_and_lexical_scopes_hidden() {
    let library = r#"module
prelude
public inductive Color where | red | blue
public inductive Rel (a b : Color) : Prop where | intro : Rel a b
private theorem secretReverse (a b : Color) (h : Rel a b) : Rel b a := @Rel.intro b a
public theorem exportedReverse (a b : Color) (h : Rel a b) : Rel b a := @Rel.intro b a
attribute [symm] secretReverse exportedReverse
namespace Choice
attribute [scoped symm] exportedReverse
end Choice
"#;
    let main = "module\nprelude\npublic import Lib\npublic theorem publicUse (a b : Color) (h : Rel a b) : Rel b a := by\n  symm\n  exact h";
    let built = compiled(&[("Lib", library), ("Main", main)]);
    let library = built
        .artifacts
        .iter()
        .find(|artifact| artifact.name == name("Lib"))
        .unwrap();
    assert!(library.companions.is_some());
    let rows = metadata(&library.bytes).symms;
    assert_eq!(rows.len(), 2);
    assert!(
        rows.iter()
            .all(|row| row.declaration == name("exportedReverse"))
    );
    assert_eq!(rows[0].scope, None);
    assert_eq!(rows[1].scope, Some(name("Choice")));
    assert!(
        metadata(&library.bytes)
            .namespaces
            .contains(&name("Choice"))
    );
    let receipt = imported(&built);
    let use_name = name("Use");
    let checked = receipt.check_source_modules(&[SourceModuleInput {
        name: &use_name,
        source: b"module\nprelude\npublic import Main\nopen scoped Choice\npublic theorem nextUse (a b : Color) (h : Rel a b) : Rel b a := by\n  symm\n  exact h",
    }], &use_name, &KVMap::new(), limits(), None).unwrap().into_complete().unwrap();
    let private = Name::num(name("_private.Lib"), 0).append_core(&name("secretReverse"));
    assert!(!checked.checked.engine.environment().contains(&private));
    assert!(
        fln_elab::symm::read(checked.checked.engine.environment())
            .unwrap()
            .iter()
            .all(|row| row.lemma.declaration != private)
    );
}

#[test]
fn symmetry_header_aliases_observe_imported_reducibility_and_keep_coverage_refusals_typed() {
    use fln::source_check::modules::imported::SourceOleanImportError;
    use fln_olean::source_extensions::ReducibilityStatus;
    use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};
    let source = r#"prelude
inductive Color where | red | blue
inductive Rel (a b : Color) : Prop where | intro : Rel a b
def SymmetryType : Prop := ∀ (a b : Color), Rel a b → Rel b a
attribute [reducible] SymmetryType
@[symm] theorem aliasReverse : SymmetryType := fun a b h => @Rel.intro b a
"#;
    let built = compiled(&[("Main", source)]);
    let receipt = imported(&built);
    let checked = receipt
        .engine
        .check_source_files(
            &[
                br#"theorem useAlias (a b : Color) (h : Rel a b) : Rel b a := by
  symm
  exact h
"#,
            ],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(
        checked.engine.environment().find(&name("useAlias")),
        Some(fln::ConstantInfo::Thm(_))
    ));
    aliases::reference_import(
        &built,
        "import Lean.Elab.Tactic.Symm\nimport Main\nexample (a b : Color) (h : Rel a b) : Rel b a := by symm; exact h",
        true,
    );

    // The pin permits an explicitly opted-in reducibility policy change after
    // registration. The olean retains the original path and final policy, not
    // the historical policy that exposed this theorem's telescope.
    // A bounded reader must report its coverage limit rather than call the
    // already checked theorem malformed when its telescope is now hidden.
    let artifact = &built.artifacts[0];
    let decoded =
        fln::decode_olean_artifact(&artifact.bytes, fln::OleanDecodeLimits::new(4 << 20)).unwrap();
    let mut rows = metadata(&artifact.bytes);
    let policy = rows
        .reducibility
        .iter_mut()
        .find(|row| row.declaration == name("SymmetryType"))
        .unwrap();
    policy.status = ReducibilityStatus::Irreducible;
    let changed = encode_module_with_source_metadata(
        fln::OleanModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &decoded.constants,
            extra_const_names: &[],
        },
        &SourceMetadata {
            symms: rows.symms,
            reducibility: rows.reducibility,
            aux_recursors: rows.aux_recursors,
            noncomputable: rows.noncomputable,
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
    .unwrap();
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    let error = initial
        .import_olean_modules_for_source(
            &[OleanModuleInput {
                name: &artifact.name,
                artifact: &changed.bytes,
                server_artifact: None,
                private_artifact: None,
            }],
            std::slice::from_ref(&artifact.name),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                4 << 20,
                limits().source.admission.kernel,
            )),
        )
        .unwrap_err();
    assert!(matches!(error, SourceOleanImportError::Symm {
        error: fln_elab::symm::SymmRegistryError::UnsupportedLemma(declaration), ..
    } if declaration == name("aliasReverse")));
    assert_eq!(initial.logical_root(&KVMap::new()), root);
}
