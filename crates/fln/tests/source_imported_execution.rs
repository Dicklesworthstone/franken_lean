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

        // The actual Prelude's Not definition differs from the seed in binder
        // names and reducibility hints. Its checked proof field still has the
        // same erased layout, including decisions consumed by compiled matches.
        let decisions = [("Main", "prelude\nimport Init.Prelude\ndef decision : Decidable True := Decidable.isTrue True.intro\ndef choose (d : Decidable True) : Nat := match d with | .isTrue h => 42 | .isFalse h => 0\n#eval choose decision")];
        assert_eq!(values(&run(&imported, &decisions, "Main")), [vec![42]]);

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

        // The imported library's private recursion helpers must remain in
        // each execution world, including calls reached through a source
        // dependency's exported definition.
        let lists = [
            ("Main", "prelude\nimport Lists\n#eval total (List.map (fun n => n + 1) combined)"),
            ("Lists", "prelude\nimport Init.Prelude\ndef combined : List Nat := List.append [19] [21]\ndef total (xs : List Nat) : Nat := match xs with | [] => 0 | x :: tail => x + total tail"),
        ];
        let list_program = run(&imported, &lists, "Main");
        assert_eq!(values(&list_program), [vec![], vec![42]]);
        assert_eq!(imported.engine.logical_root(&options), original);

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
fn ordinary_execution_imports_init_for_each_module_without_rewriting_source() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let options = KVMap::new();
            let imported = SourceOleanImport::empty(&options);
            let original = imported.engine.logical_root(&options);
            let names = [name("Main"), name("Right"), name("Init"), name("Left")];
            let sources = [
                "\u{feff}import Left\r\nimport Right\r\n#check Token\r\n#eval left\r\n#eval right\r\n",
                "def right : Token := token\n#eval right\n",
                "prelude\ninductive Token where\n  | off\n  | on\ndef token : Token := Token.on\n",
                "def left : Token := token\n",
            ];
            let modules: Vec<_> = names
                .iter()
                .zip(&sources)
                .map(|(name, source)| SourceModuleInput {
                    name,
                    source: source.as_bytes(),
                })
                .collect();
            let mut exact = limits();
            exact.modules.source.max_bytes = sources.iter().map(|source| source.len()).sum();
            exact.modules.max_imports = 5;
            let first = imported
                .execute_lean_source_modules(&modules, &names[0], &options, exact, None)
                .expect("all ordinary modules receive their actual Init import")
                .into_complete()
                .unwrap();
            let token_values = |program: &SourceProgramExecution| {
                program.modules.iter().map(|module| {
                    module.commands.batch.source_evaluation_indices.iter().map(|&index| {
                        let fln::VmExit::Returned(returned) = &module.commands.batch.executions[index].exit else {
                            panic!("the imported Token value must return");
                        };
                        assert!(!returned.value.is_scalar());
                        returned.value.header().tag
                    }).collect::<Vec<_>>()
                }).collect::<Vec<_>>()
            };
            assert_eq!(
                first.modules.iter().map(|module| &module.module).collect::<Vec<_>>(),
                [&names[2], &names[3], &names[1], &names[0]]
            );
            assert_eq!(token_values(&first), [vec![], vec![], vec![1], vec![1, 1]]);
            assert_eq!(first.modules[3].commands.checks.len(), 1);
            assert!(!first.modules[2].commands.batch.engine.environment().contains(&name("left")));
            assert!(!first.modules[0].commands.batch.engine.environment().contains(&name("Nat")));

            // The explicit-import API retains its contract: it cannot reach
            // this Init source unless a source header actually imports it.
            assert!(matches!(
                imported.execute_source_modules(&modules, &names[0], &options, exact, None),
                Err(fln::source_check::modules::SourceModuleCheckError::UnreachableModule(module))
                    if module == names[2]
            ));
            let mut fewer_imports = exact;
            fewer_imports.modules.max_imports = 4;
            let mut fewer_bytes = exact;
            fewer_bytes.modules.source.max_bytes -= 1;
            for restricted in [fewer_imports, fewer_bytes] {
                let error = imported
                    .execute_lean_source_modules(&modules, &names[0], &options, restricted, None)
                    .expect_err("both implicit imports and original source bytes are charged");
                assert_eq!(error.disposition(), ("resource", false, 3), "{error:?}");
            }

            // A non-prelude sibling gets Init, but still cannot see another
            // sibling's declarations merely because their entry imports both.
            let mut leaking = modules.clone();
            leaking[1].source = b"def right : Token := left\n";
            assert!(matches!(
                imported.execute_lean_source_modules(&leaking, &names[0], &options, limits(), None),
                Err(fln::source_check::modules::SourceModuleCheckError::Source { module, .. })
                    if module == names[1]
            ));
            // `prelude` on that same sibling removes its implicit dependency;
            // Init being present elsewhere must not make Token ambient.
            let mut explicit_prelude = modules.clone();
            explicit_prelude[1].source = b"prelude\ndef right : Token := Token.on\n";
            assert!(matches!(
                imported.execute_lean_source_modules(&explicit_prelude, &names[0], &options, limits(), None),
                Err(fln::source_check::modules::SourceModuleCheckError::Source { module, .. })
                    if module == names[1]
            ));

            let bad = "\u{feff}import Left\r\nimport Right\r\n#check Token\r\n#check unknownToken\r\n";
            let mut invalid = modules.clone();
            invalid[0].source = bad.as_bytes();
            let error = imported
                .execute_lean_source_modules(&invalid, &names[0], &options, limits(), None)
                .unwrap_err();
            match error {
                fln::source_check::modules::SourceModuleCheckError::Source {
                    module,
                    error: fln::SourceCheckError::Command { command, offset, .. },
                } => {
                    assert_eq!(module, names[0]);
                    assert_eq!(command, 1);
                    assert_eq!(offset, bad.find("#check unknownToken").unwrap());
                }
                other => panic!("the diagnostic must retain the original source position: {other:?}"),
            }
            let retry = imported
                .execute_lean_source_modules(&modules, &names[0], &options, exact, None)
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(token_values(&retry), token_values(&first));
            for (before, after) in first.modules.iter().zip(&retry.modules) {
                assert_eq!(
                    before.commands.batch.engine.logical_root(&options),
                    after.commands.batch.engine.logical_root(&options)
                );
                for (before, after) in before.commands.batch.executions.iter().zip(&after.commands.batch.executions) {
                    assert_eq!(before.flbc_artifact, after.flbc_artifact);
                }
            }
            assert_eq!(imported.engine.logical_root(&options), original);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn ordinary_execution_requires_init_and_preserves_empty_prelude_worlds() {
    let options = KVMap::new();
    let imported = SourceOleanImport::empty(&options);
    let original = imported.engine.logical_root(&options);
    let entry = name("Main");
    let modules = [SourceModuleInput {
        name: &entry,
        source: b"",
    }];
    let error = imported
        .execute_lean_source_modules(&modules, &entry, &options, limits(), None)
        .expect_err("even a headerless empty file needs its real Init dependency");
    assert_eq!(error.disposition(), ("input", false, 1));
    assert!(matches!(
        error,
        fln::source_check::modules::SourceModuleCheckError::MissingModule { importer, module }
            if importer == entry && module == name("Init")
    ));
    struct Cancelled;
    impl fln::CancellationProbe for Cancelled {
        fn is_cancelled(&self) -> bool {
            true
        }
    }
    assert!(matches!(
        imported
            .execute_lean_source_modules(&modules, &entry, &options, limits(), Some(&Cancelled))
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    let prelude = [SourceModuleInput {
        name: &entry,
        source: b"prelude\n",
    }];
    let first = imported
        .execute_lean_source_modules(&prelude, &entry, &options, limits(), None)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(first.modules.len(), 1);
    assert_eq!(first.modules[0].commands.command_count, 0);
    assert!(
        first.modules[0]
            .commands
            .batch
            .engine
            .environment()
            .is_empty()
    );
    assert_eq!(imported.engine.logical_root(&options), original);
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
