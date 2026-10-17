//! Public exports cross the checked source-module boundary as metadata, never
//! as copied declarations or unchecked proof bodies.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn check_modules(
    files: &[(&str, &str)],
) -> Result<
    fln::Outcome<fln::source_check::modules::SourceModuleCheck>,
    fln::source_check::modules::SourceModuleCheckError,
> {
    use fln::source_check::modules::SourceModuleCheckLimits;
    let names: Vec<_> = files
        .iter()
        .map(|(name, _)| fln::Name::from_components(name.split('.')))
        .collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| fln::SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    engine().check_source_modules(
        &inputs,
        &names[0],
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
    )
}

#[test]
fn module_exports_reach_public_headers_hidden_bodies_and_transitive_importers() {
    let api = "module\nprelude\nnamespace Values\npublic inductive Token where\n| first\n| second\n@[expose] public def identity (n : Nat) : Nat := n\npublic theorem witness (P : Prop) (h : P) : P := h\nend Values\nexport Values (Token identity witness)\nexport Values.Token (first second)\nprivate def localValue : Token := first\npublic theorem localUse (P : Prop) (h : P) : P := witness P h\n@[expose] public def visible : Token := second";
    let local = check_modules(&[("Api", api)])
        .unwrap()
        .into_complete()
        .unwrap();
    let local_aliases =
        fln_elab::aliases::AliasTable::read(local.checked.engine.environment()).unwrap();
    assert_eq!(
        local_aliases.targets(&fln::Name::from_components(["first"])),
        [fln::Name::from_components(["Values", "Token", "first"])]
    );
    let main = "prelude\nimport Middle\ndef value : Token := first\ntheorem t : identity 7 = 7 := rfl\ntheorem useWitness (P : Prop) (h : P) : P := witness P h";
    let imported = check_modules(&[
        ("Main", main),
        ("Middle", "module\nprelude\npublic import Api"),
        ("Api", api),
    ])
    .unwrap()
    .into_complete()
    .unwrap();
    let aliases =
        fln_elab::aliases::AliasTable::read(imported.checked.engine.environment()).unwrap();
    assert_eq!(aliases, local_aliases);
    assert!(matches!(
        imported
            .checked
            .engine
            .environment()
            .find(&fln::Name::from_components(["Values", "witness"])),
        Some(fln_env::constants::ConstantInfo::Axiom(_))
    ));
    // The export command is metadata, not another declaration or unchecked body.
    assert!(
        !imported
            .checked
            .engine
            .environment()
            .contains(&fln::Name::from_components(["first"]))
    );
}

#[test]
fn module_aliases_reexport_under_namespaces_and_do_not_require_a_public_section() {
    let api = "module\nprelude\nnamespace Original\n@[expose] public def x : Nat := 7\nend Original\nnamespace Aliased\nexport Original (x)\nend Aliased\nexport Aliased (x)\nprivate theorem localUse : x = 7 := rfl";
    let main = "prelude\nimport Api\ntheorem imported : x = 7 := rfl\ntheorem qualified : Aliased.x = 7 := rfl";
    check_modules(&[("Main", main), ("Api", api)])
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn bad_exports_do_not_publish_prefixes_or_leak_private_targets() {
    use fln::source_check::modules::{
        SourceModuleCacheLimits, SourceModuleCheckError, SourceModuleCheckLimits,
        SourceModuleSession,
    };
    use fln::{Name, SourceModuleInput};
    let api = "module\nprelude\nnamespace Values\n@[expose] public def x : Nat := 7\nprivate def hidden : Nat := 8\nend Values\nexport Values (x)";
    let main = "prelude\nimport Api\ntheorem t : x = 7 := rfl";
    let names = [
        Name::from_components(["Main"]),
        Name::from_components(["Api"]),
    ];
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: main.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: api.as_bytes(),
        },
    ];
    let mut session = SourceModuleSession::new(
        engine(),
        KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        SourceModuleCacheLimits::default(),
    );
    let cold = session
        .check(&inputs, &names[0])
        .unwrap()
        .into_complete()
        .unwrap();
    let root = cold.checked.checked.result_logical_root;
    let retained = session.retained_modules();
    for export in [
        "export Values (x missing)",
        "export Values (x hidden)",
        "namespace Values\nexport Values (x)\nend Values",
    ] {
        let changed = api.replace("export Values (x)", export);
        let mut bad = inputs;
        bad[1].source = changed.as_bytes();
        assert!(
            matches!(session.check(&bad, &names[0]), Err(SourceModuleCheckError::Source { module, .. }) if module == names[1]),
            "{changed}"
        );
        assert_eq!(session.retained_modules(), retained);
        let recovered = session
            .check(&inputs, &names[0])
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(recovered.reused_modules, 2);
        assert_eq!(recovered.checked.checked.result_logical_root, root);
    }
    let hidden_import = "module\nprelude\nimport Secret\nexport Values (x)";
    assert!(
        check_modules(&[
            ("Api", hidden_import),
            (
                "Secret",
                "prelude\nnamespace Values\ndef x : Nat := 7\nend Values"
            )
        ])
        .is_err()
    );
}

#[test]
fn execution_replays_module_aliases_without_exposing_hidden_bodies() {
    use fln::source_check::modules::{execution::SourceProgramLimits, imported::SourceOleanImport};
    use fln::{EngineExecutionLimits, Name, SourceModuleInput};
    let api = "module\nprelude\nnamespace Values\npublic inductive Token where\n| first\nend Values\nexport Values (Token)\nexport Values.Token (first)";
    let main = "prelude\nimport Api\n#check first\ndef chosen : Token := first";
    let names = [
        Name::from_components(["Main"]),
        Name::from_components(["Api"]),
    ];
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: main.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: api.as_bytes(),
        },
    ];
    let executed = SourceOleanImport::empty(&KVMap::new())
        .execute_source_modules(
            &inputs,
            &names[0],
            &KVMap::new(),
            SourceProgramLimits::new(EngineExecutionLimits::new(limits().kernel)),
            None,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let env = executed
        .modules
        .last()
        .unwrap()
        .commands
        .batch
        .engine
        .environment();
    let table = fln_elab::aliases::AliasTable::read(env).unwrap();
    assert_eq!(
        table.targets(&Name::from_components(["first"])),
        [Name::from_components(["Values", "Token", "first"])]
    );
    assert!(env.contains(&Name::from_components(["chosen"])));
    assert!(!env.contains(&Name::from_components(["first"])));
}
