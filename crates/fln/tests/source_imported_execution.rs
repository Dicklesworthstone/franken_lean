//! Real imported declarations, isolated module worlds, and native execution.
#![forbid(unsafe_code)]

use fln::source_check::modules::execution::{
    SourceProgramExecution, SourceProgramLimits, preflight_source_program,
};
use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionLimits, Environment, KVMap, Name,
    OleanCheckLimits, OleanModuleInput, SourceModuleInput,
};
use std::path::PathBuf;

const STACK: usize = 256 * 1024 * 1024;

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn limits() -> SourceProgramLimits {
    SourceProgramLimits::new(EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)))
}

fn pinned_prelude() -> Option<SourceOleanImport> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|lib| lib.is_dir());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required"
        );
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return None;
    };
    let path = lib.join("Init/Prelude.olean");
    let parts = [
        std::fs::read(&path).unwrap(),
        std::fs::read(path.with_extension("olean.server")).unwrap(),
        std::fs::read(path.with_extension("olean.private")).unwrap(),
    ];
    let prelude = name("Init.Prelude");
    let inputs = [OleanModuleInput {
        name: &prelude,
        artifact: &parts[0],
        server_artifact: Some(&parts[1]),
        private_artifact: Some(&parts[2]),
    }];
    Some(
        Engine::from_environment(Environment::new())
            .import_olean_modules_for_source(
                &inputs,
                std::slice::from_ref(&prelude),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    256 * 1024 * 1024,
                    Budget::for_stack_bytes(STACK),
                )),
            )
            .expect("read and check the actual pinned Prelude")
            .into_complete()
            .expect("K1 and independent checker agree"),
    )
}

fn run(
    imported: &SourceOleanImport,
    sources: &[(&str, &str)],
    entry: &str,
) -> SourceProgramExecution {
    let names: Vec<_> = sources.iter().map(|(module, _)| name(module)).collect();
    let modules: Vec<_> = names
        .iter()
        .zip(sources)
        .map(|(name, (_, source))| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    imported
        .execute_source_modules(&modules, &name(entry), &KVMap::new(), limits(), None)
        .unwrap_or_else(|error| panic!("imported source: {error:?}"))
        .into_complete()
        .expect("source program completes")
}

fn values(program: &SourceProgramExecution) -> Vec<Vec<usize>> {
    program
        .modules
        .iter()
        .map(|module| {
            module
                .commands
                .batch
                .source_evaluation_indices
                .iter()
                .map(|&index| {
                    match fln::closed_vm_value(&module.commands.batch.executions[index].exit)
                        .unwrap()
                    {
                        Some(ClosedVmValue::Scalar(value)) => value,
                        other => panic!("expected a Nat result: {other:?}"),
                    }
                })
                .collect()
        })
        .collect()
}

#[test]
fn real_imports_execute_in_exact_module_worlds_and_keep_query_candidates_private() {
    std::thread::Builder::new().stack_size(STACK).spawn(|| {
        let Some(mut imported) = pinned_prelude() else { return };
        let options = KVMap::new();
        let original = imported.engine.logical_root(&options);
        assert!(imported.engine.environment().len() > 2000);
        let direct = [("Main", "prelude\nimport Init.Prelude\n#check Nat\ndef answer : Nat := id 42\n#eval answer")];
        let first = run(&imported, &direct, "Main");
        assert_eq!(values(&first), [vec![42]]);
        assert_eq!(first.modules[0].commands.checks.len(), 1);
        let artifact = first.modules[0].commands.batch.executions.last().unwrap().flbc_artifact.clone();

        // Both siblings allocate an evaluation candidate at command zero in
        // their own world. Neither candidate may be replayed into the other or
        // collide when the entry imports both siblings.
        let graph = [
            ("Main", "prelude\nimport Left\nimport Right\n#check left\n#eval left\n#eval right"),
            ("Right", "prelude\nimport Init.Prelude\n#eval (12 : Nat)\ndef right : Nat := id 22"),
            ("Left", "prelude\nimport Init.Prelude\n#eval (11 : Nat)\ndef left : Nat := id 20"),
        ];
        let checked = run(&imported, &graph, "Main");
        assert_eq!(checked.modules.iter().map(|m| m.module.to_display_string()).collect::<Vec<_>>(), ["Left", "Right", "Main"]);
        assert_eq!(values(&checked), [vec![11], vec![12], vec![20, 22]]);
        assert!(!checked.modules[1].commands.batch.engine.environment().contains(&name("left")));

        // Local class registrations are imported in source order, with the
        // actual Prelude's classes, instances and protected-name metadata.
        let registries = [
            ("Main", "prelude\nimport Low\nimport High\n#eval Pick.value (self := inferInstance)"),
            ("Base", "prelude\nimport Init.Prelude\nclass Pick where\n  value : Nat"),
            ("Low", "prelude\nimport Base\ninstance low : Pick := Pick.mk 11"),
            ("High", "prelude\nimport Base\ninstance high : Pick := Pick.mk 22"),
        ];
        let ordered = run(&imported, &registries, "Main");
        assert_eq!(values(&ordered).last(), Some(&vec![22]));
        let reversed = [("Main", "prelude\nimport High\nimport Low\n#eval Pick.value (self := inferInstance)"), registries[1], registries[2], registries[3]];
        assert_eq!(values(&run(&imported, &reversed, "Main")).last(), Some(&vec![11]));

        let entry = name("Main");
        for bad in [
            "prelude\n#check Nat",
            "prelude\nimport Missing\n#eval (42 : Nat)",
            "prelude\nimport Init.Prelude\ndef stagedResult : Nat := 42\n#eval stagedResult\ntheorem falseClaim : (1 : Nat) = 2 := rfl",
        ] {
            let modules = [SourceModuleInput { name: &entry, source: bad.as_bytes() }];
            let error = imported.execute_source_modules(&modules, &entry, &options, limits(), None)
                .expect_err("invalid module returns no partial execution");
            if bad.contains("stagedResult") {
                assert!(matches!(error, fln::source_check::modules::SourceModuleCheckError::Source {
                    error: fln::SourceCheckError::Command { command: 2, .. }, ..
                }), "the valid definition and evaluation must precede the failure: {error:?}");
            }
            assert_eq!(imported.engine.logical_root(&options), original);
            assert!(!imported.engine.environment().contains(&name("stagedResult")));
        }
        // A source sibling's declarations do not become ambient merely
        // because another entry branch imports that sibling.
        let left = name("Left");
        let right = name("Right");
        let leak = [
            SourceModuleInput { name: &entry, source: b"prelude\nimport Left\nimport Right\n#eval stolen" },
            SourceModuleInput { name: &left, source: b"prelude\nimport Init.Prelude\ndef secret : Nat := 41" },
            SourceModuleInput { name: &right, source: b"prelude\nimport Init.Prelude\ndef stolen : Nat := secret" },
        ];
        assert!(imported.execute_source_modules(&leak, &entry, &options, limits(), None).is_err());

        let modules = [SourceModuleInput { name: &entry, source: direct[0].1.as_bytes() }];
        let mut tight = limits();
        tight.modules.source.max_commands = 2;
        assert!(imported.execute_source_modules(&modules, &entry, &options, tight, None).is_err());
        let retried = run(&imported, &direct, "Main");
        assert_eq!(retried.modules[0].commands.batch.executions.last().unwrap().flbc_artifact, artifact);

        // Public reports are caller-editable; retained private contexts alone
        // choose the world from which execution obtains its authority.
        imported.engine = Engine::from_environment(Environment::new());
        imported.checked.engine = Engine::from_environment(Environment::new());
        imported.checked.modules.clear();
        imported.modules.clear();
        let retried = run(&imported, &direct, "Main");
        assert_eq!(values(&retried), [vec![42]]);
        assert_eq!(retried.modules[0].commands.batch.executions.last().unwrap().flbc_artifact, artifact);
        let empty = run(&imported, &[("Main", "prelude\nimport Init.Prelude\n")], "Main");
        assert_eq!(empty.modules[0].commands.command_count, 0);
        assert!(empty.modules[0].commands.outputs.is_empty());
    }).unwrap().join().unwrap();
}

#[test]
fn explicit_prelude_programs_start_in_a_genuinely_empty_import_world() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let options = KVMap::new();
            let imported = SourceOleanImport::empty(&options);
            let root = imported.engine.logical_root(&options);
            assert!(imported.checked.modules.is_empty());
            assert!(imported.modules.is_empty());
            assert_eq!(imported.checked.base_logical_root, root);
            assert_eq!(imported.checked.result_logical_root, root);
            assert_eq!(imported.result_logical_root, root);
            let sources = [
                ("Main", "prelude\nimport Base\n#check token\n"),
                (
                    "Base",
                    "prelude\ninductive Token where\n  | mk\ndef token : Token := Token.mk\n",
                ),
            ];
            let first = run(&imported, &sources, "Main");
            assert_eq!(
                first.modules.iter().map(|m| &m.module).collect::<Vec<_>>(),
                [&name("Base"), &name("Main")]
            );
            assert_eq!(first.modules[1].commands.outputs.len(), 1);
            for module in &first.modules {
                assert!(
                    module
                        .commands
                        .batch
                        .engine
                        .environment()
                        .find(&name("Nat"))
                        .is_none()
                );
            }
            let entry = name("Main");
            for source in ["prelude\n#check Nat", "prelude\nimport Init.Prelude\n"] {
                let modules = [SourceModuleInput {
                    name: &entry,
                    source: source.as_bytes(),
                }];
                assert!(
                    imported
                        .execute_source_modules(&modules, &entry, &options, limits(), None)
                        .is_err()
                );
            }
            struct Cancelled;
            impl fln::CancellationProbe for Cancelled {
                fn is_cancelled(&self) -> bool {
                    true
                }
            }
            let modules = [SourceModuleInput {
                name: &entry,
                source: b"prelude\n",
            }];
            assert!(matches!(
                imported
                    .execute_source_modules(&modules, &entry, &options, limits(), Some(&Cancelled))
                    .unwrap(),
                fln::Outcome::Inconclusive(_)
            ));
            // These are real compiler and bytecode resource stops after
            // admission, not evidence that the source declaration is invalid.
            let names = [name("Main"), name("Base")];
            let modules: Vec<_> = names
                .iter()
                .zip(&sources)
                .map(|(name, (_, source))| SourceModuleInput {
                    name,
                    source: source.as_bytes(),
                })
                .collect();
            let mut compiler_limit = limits();
            compiler_limit.execution.ingress.max_nodes = 1;
            let mut codec_limit = limits();
            codec_limit.execution.flbc_codec.max_artifact_bytes = 1;
            for restricted in [compiler_limit, codec_limit] {
                let error = imported
                    .execute_source_modules(&modules, &entry, &options, restricted, None)
                    .expect_err("the limited compiler cannot complete this program");
                assert_eq!(error.disposition(), ("resource", false, 3), "{error:?}");
            }
            let retry = run(&imported, &sources, "Main");
            assert_eq!(
                first.modules[1]
                    .commands
                    .batch
                    .engine
                    .logical_root(&options),
                retry.modules[1]
                    .commands
                    .batch
                    .engine
                    .logical_root(&options)
            );
            assert_eq!(imported.engine.logical_root(&options), root);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn execution_preflight_accepts_queries_and_rebases_bad_source_before_import_admission() {
    let entry = name("Main");
    let valid =
        "\u{feff}prelude\r\nimport Init.Prelude\r\nopen Nat in #check Nat\r\n#eval id 42\r\n";
    preflight_source_program(
        &[SourceModuleInput {
            name: &entry,
            source: valid.as_bytes(),
        }],
        limits().modules,
    )
    .unwrap();
    let invalid = "\u{feff}prelude\r\nimport Init.Prelude\r\n#eval (";
    let error = preflight_source_program(
        &[SourceModuleInput {
            name: &entry,
            source: invalid.as_bytes(),
        }],
        limits().modules,
    )
    .unwrap_err();
    match error {
        fln::source_check::modules::SourceModuleCheckError::Source {
            error: fln::SourceCheckError::Command { offset, error, .. },
            ..
        } => {
            assert!(offset >= invalid.find("#eval").unwrap());
            assert!(
                error
                    .primary_source_offset()
                    .is_some_and(|at| at.0 >= invalid.find("#eval").unwrap())
            );
        }
        other => panic!("body error retains its original source offset: {other:?}"),
    }
}
