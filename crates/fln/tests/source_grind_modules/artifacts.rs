//! Reusable grind metadata must survive build-session and artifact boundaries.
#![forbid(unsafe_code)]
use super::*;
use fln::source_check::modules::imported::SourceOleanImportError;
use fln::source_check::modules::persisted::{PersistedModules, SourceModuleKey, SourceModuleStore};
use fln::source_check::modules::reuse::CheckerIdentity;
use fln::source_check::modules::{SourceModuleCacheLimits, SourceModuleSession};
use fln_olean::source_extensions::GrindPatternEntry;
use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};
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

#[test]
fn dependency_registrations_keep_order_through_cached_and_persisted_builds() {
    let base = Engine::builder().build_empty();
    let names = [n("Lib"), n("Main")];
    let inputs = [
        SourceModuleInput { name: &names[0], source: CORE.as_bytes() },
        SourceModuleInput {
            name: &names[1],
            source: b"prelude\nimport Lib\ngrind_pattern rule => trigger x\ngrind_pattern rule => other x\ngrind_pattern rule => trigger x\n",
        },
    ];
    let records = Records::default();
    let new_session = || {
        SourceModuleSession::new(
            base.clone(),
            KVMap::new(),
            limits(),
            SourceModuleCacheLimits::default(),
        )
    };
    let compile = |session: &mut SourceModuleSession| {
        session
            .compile_with_records(
                &inputs,
                &names[1],
                OleanWriteBudget::default(),
                Some(PersistedModules {
                    checker: CheckerIdentity::of_executable(b"checked-grind-pattern-replay"),
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
    let warm = compile(&mut session);
    let restored = compile(&mut new_session());
    assert_eq!((cold.elaborated_modules, cold.persisted_modules), (2, 0));
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (2, 0));
    assert_eq!(
        (restored.persisted_modules, restored.elaborated_modules),
        (2, 0)
    );
    let expected = [
        row(n("rule"), "trigger"),
        row(n("rule"), "other"),
        row(n("rule"), "trigger"),
    ];
    for built in [&cold, &warm, &restored] {
        assert_eq!(
            built.checked.checked.result_logical_root,
            cold.checked.checked.result_logical_root
        );
        for (artifact, original) in built.artifacts.iter().zip(&cold.artifacts) {
            assert_eq!(artifact.name, original.name);
            assert_eq!(artifact.bytes, original.bytes);
        }
        let loaded = import(&base, built);
        assert_eq!(
            grind_patterns::read(loaded.engine.environment()).unwrap(),
            expected
        );
        let counts: Vec<_> = loaded
            .modules
            .iter()
            .map(|module| {
                (
                    module.module.clone(),
                    module.grind_entries,
                    module.grind_patterns,
                    module.deferred_grind,
                )
            })
            .collect();
        assert_eq!(counts, [(n("Lib"), 0, 0, 0), (n("Main"), 3, 3, 0)]);
    }
    assert!(base.environment().is_empty());
}

#[test]
fn captured_patterns_reimport_after_their_function_type_becomes_irreducible() {
    use fln_elab::reducibility::{Reducibility, ReducibilityTable};

    let base = Engine::builder().build_empty();
    let declarations = CORE.replace(
        "axiom trigger : A -> A",
        "def FunctionType := A -> A\naxiom trigger : FunctionType",
    );
    let source = format!(
        "{declarations}grind_pattern rule => trigger x\nattribute [irreducible] FunctionType\n"
    );
    let built = build(&base, &[("Main", &source)]);
    let loaded = import(&base, &built);
    for environment in [
        built.checked.checked.engine.environment(),
        loaded.engine.environment(),
    ] {
        assert_eq!(
            grind_patterns::read(environment).unwrap(),
            [row(n("rule"), "trigger")]
        );
        assert_eq!(
            ReducibilityTable::read(environment)
                .unwrap()
                .status(&n("FunctionType")),
            Reducibility::Irreducible
        );
    }
    assert_eq!(loaded.modules[0].grind_patterns, 1);
    assert_eq!(loaded.modules[0].deferred_grind, 0);
    assert!(base.environment().is_empty());
}

fn dependency(module: &str) -> fln::OleanModuleImport {
    fln::OleanModuleImport {
        module: n(module),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }
}
fn encode(imports: &[fln::OleanModuleImport], rows: Vec<GrindPatternEntry>) -> Vec<u8> {
    encode_module_with_source_metadata(
        fln::OleanModuleWriteInput {
            is_module: false,
            imports,
            constants: &[],
            extra_const_names: &[],
        },
        &SourceMetadata {
            grind_patterns: rows,
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
}
fn wire_row(declaration: &str, trigger: &str) -> GrindPatternEntry {
    GrindPatternEntry {
        declaration: n(declaration),
        proof: Expr::const_(n(declaration), vec![]),
        num_params: 2,
        patterns: vec![Expr::app(
            Expr::const_(n(trigger), vec![]),
            Expr::bvar(1).unwrap(),
        )],
        symbols: vec![n(trigger)],
    }
}

#[test]
fn metadata_uses_each_recording_modules_dependency_closure_and_preserves_resource_refusals() {
    let base = Engine::builder().build_empty();
    let root = base.logical_root(&KVMap::new());
    let built = build(
        &base,
        &[
            ("Lib", CORE),
            (
                "Unrelated",
                "prelude\nimport Lib\naxiom secret : A -> A\ntheorem outsider (x : A) (h : p x) : p x := h\n",
            ),
            ("Main", "prelude\nimport Lib\nimport Unrelated"),
        ],
    );
    let main = n("Main");
    let unrelated = n("Unrelated");
    let budget = || {
        SourceOleanImportLimits::new(OleanCheckLimits::new(
            4 << 20,
            limits().source.admission.kernel,
        ))
    };
    let activate = |artifact: &[u8], roots: &[Name], limits| {
        let mut inputs: Vec<_> = built
            .artifacts
            .iter()
            .filter(|item| item.name != main)
            .map(|item| OleanModuleInput {
                name: &item.name,
                artifact: &item.bytes,
                server_artifact: None,
                private_artifact: None,
            })
            .collect();
        inputs.push(OleanModuleInput {
            name: &main,
            artifact,
            server_artifact: None,
            private_artifact: None,
        });
        base.import_olean_modules_for_source(&inputs, roots, &KVMap::new(), limits)
    };
    let valid = encode(&[dependency("Lib")], vec![wire_row("rule", "trigger")]);
    let roots = [main.clone(), unrelated.clone()];
    let accepted = activate(&valid, &roots, budget())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        grind_patterns::read(accepted.engine.environment()).unwrap(),
        [row(n("rule"), "trigger")]
    );
    for bad in [
        wire_row("outsider", "trigger"),
        wire_row("rule", "secret"),
        wire_row("missing", "trigger"),
    ] {
        let invalid = encode(&[dependency("Lib")], vec![wire_row("rule", "trigger"), bad]);
        assert!(matches!(
            activate(&invalid, &roots, budget()),
            Err(SourceOleanImportError::Metadata { .. }),
        ));
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(grind_patterns::read(base.environment()).unwrap().is_empty());
    }
    let reachable = encode(
        &[dependency("Lib"), dependency("Unrelated")],
        vec![wire_row("outsider", "secret")],
    );
    let loaded = activate(&reachable, std::slice::from_ref(&main), budget())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        grind_patterns::read(loaded.engine.environment()).unwrap(),
        [row(n("outsider"), "secret")]
    );

    // A valid wire row may still lie about its full theorem telescope.
    let invalid = encode(
        &[dependency("Lib")],
        vec![
            wire_row("rule", "trigger"),
            GrindPatternEntry {
                num_params: 3,
                ..wire_row("rule", "trigger")
            },
        ],
    );
    assert!(matches!(
        activate(&invalid, &roots, budget()),
        Err(SourceOleanImportError::Grind { .. })
    ));
    let mut exhausted = budget();
    exhausted.metadata.max_keys = 0;
    let failure = activate(&valid, &roots, exhausted).unwrap_err();
    assert!(failure.metadata_resource_exhausted());
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(base.environment().is_empty());
}

#[test]
fn public_artifacts_hide_private_grind_targets_but_legacy_companions_retain_them() {
    let base = Engine::builder().build_empty();
    let library = "module\nprelude\npublic axiom A : Type\npublic axiom p : A -> Prop\npublic axiom trigger : A -> A\npublic theorem visible (x : A) (h : p x) : p x := h\nprivate theorem hidden (x : A) (h : p x) : p x := h\ngrind_pattern visible => trigger x\ngrind_pattern hidden => trigger x\n";
    let hidden = Name::num(n("_private.Library"), 0).append_core(&n("hidden"));
    for (main, private_visible) in [
        ("module\nprelude\npublic import Library", false),
        ("prelude\nimport Library", true),
    ] {
        let built = build(&base, &[("Library", library), ("Main", main)]);
        let loaded = import(&base, &built);
        let mut expected = vec![row(n("visible"), "trigger")];
        if private_visible {
            expected.push(row(hidden.clone(), "trigger"));
        }
        assert_eq!(
            grind_patterns::read(loaded.engine.environment()).unwrap(),
            expected
        );
        assert_eq!(
            loaded.engine.environment().contains(&hidden),
            private_visible
        );
    }
    assert!(base.environment().is_empty());
}
