//! Exact directory contracts, checked source data, deferred effects and replay.
use super::*;
use fln_core::diag::ResourceReason;
use fln_core::outcome::InconclusiveCause;
use std::os::unix::ffi::OsStringExt;

const REPLACEMENT: &str = "directoryReadReplacement";

fn helper_extern(environment: &Environment, helper: &str, foreign: bool) -> Environment {
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == helper)
        .unwrap();
    fln_elab::externs::register(
        environment,
        &name(helper),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: if foreign {
                "foreign_directory_helper".to_owned()
            } else {
                row.symbol.to_owned()
            },
        }],
    )
    .unwrap()
}

fn environment(raw: &Environment, omit: Option<&str>) -> Environment {
    let helpers = fs::DIRECTORY_HELPERS
        .into_iter()
        .filter(|helper| Some(*helper) != omit)
        .fold(raw.clone(), |environment, helper| {
            helper_extern(&environment, helper, false)
        });
    register_one(&helpers, Operation::ReadDir, false)
}

fn registered_reader(environment: &Environment) -> Engine {
    let Some(ConstantInfo::Opaque(target)) = environment.find(&Operation::ReadDir.source_name())
    else {
        panic!("the actual pinned readDir is opaque");
    };
    let original = name(REPLACEMENT);
    let mut base = target.base.clone();
    base.name = original.clone();
    let admitted = Engine::from_environment(environment.clone())
        .admit_declaration(
            Declaration::Defn(DefinitionVal {
                base,
                value: target.value.clone(),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![original.clone()],
            }),
            &KVMap::new(),
            EngineAdmissionLimits::for_stack_bytes(STACK),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        admitted.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    let environment = fln_elab::implemented_by::register(
        &admitted.engine.environment,
        &original,
        &Operation::ReadDir.source_name(),
    )
    .unwrap();
    Engine::from_environment(environment)
}

fn string(value: &Obj) -> String {
    let (size, _, _, bytes) = value.try_string_view().unwrap();
    String::from_utf8(bytes[..size - 1].to_vec()).unwrap()
}

fn logical_entries(exit: &VmExit) -> Vec<(String, String)> {
    let result = returned(exit);
    assert_constructor(result, 0, 2);
    assert_eq!(child(result, 1).unbox(), 0);
    let array = child(result, 0);
    assert_constructor(&array, 0, 1);
    let mut list = child(&array, 0);
    let mut entries = Vec::new();
    loop {
        assert!(!list.is_scalar(), "a logical List, never a native Array");
        if list.header().tag == 0 {
            assert_constructor(&list, 0, 0);
            break;
        }
        assert_constructor(&list, 1, 2);
        let entry = child(&list, 0);
        assert_constructor(&entry, 0, 2);
        let root = child(&entry, 0);
        assert_constructor(&root, 0, 1);
        entries.push((string(&child(&root, 0)), string(&child(&entry, 1))));
        assert!(entries.len() <= 1000, "bounded retained directory fixture");
        list = child(&list, 1);
    }
    entries
}

fn expected_entries(directory: &Path) -> Vec<(String, String)> {
    std::fs::read_dir(directory)
        .unwrap()
        .map(|entry| {
            (
                directory.to_str().unwrap().to_owned(),
                entry.unwrap().file_name().to_string_lossy().into_owned(),
            )
        })
        .collect()
}

#[test]
fn directory_contracts_require_exact_shapes_helpers_and_replacement_authority() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    fs::assert_pin_models(&raw);
    let exact = environment(&raw, None);
    let limits = IngressLimits::default();
    let mut work = 0;
    assert!(
        fs::primitive_matches(&exact, Operation::ReadDir, &mut None, &mut work, limits).unwrap()
    );
    assert!(matches!(
        fs::primitive_matches(
            &exact,
            Operation::ReadDir,
            &mut None,
            &mut 0,
            IngressLimits {
                max_nodes: work - 1,
                ..limits
            },
        ),
        Err(IngressError::ResourceLimit { .. })
    ));
    assert!(!fs::primitive_matches(&raw, Operation::ReadDir, &mut None, &mut 0, limits).unwrap());
    let mut bad = vec![register_one(&exact, Operation::ReadDir, true)];
    for helper in fs::DIRECTORY_HELPERS {
        bad.push(environment(&raw, Some(helper)));
        bad.push(helper_extern(&exact, helper, true));
    }
    for invalid in bad {
        assert!(
            fs::primitive_matches(&invalid, Operation::ReadDir, &mut None, &mut 0, limits).is_err()
        );
        let engine = registered_reader(&invalid);
        let mut preparation = Preparation::new(&engine.environment, limits);
        assert!(
            preparation
                .implementation_target(&name(REPLACEMENT))
                .is_err()
        );
    }
    let engine = registered_reader(&exact);
    let mut preparation = Preparation::new(&engine.environment, limits);
    assert_eq!(
        preparation
            .implementation_target(&name(REPLACEMENT))
            .unwrap(),
        Some(Operation::ReadDir.source_name())
    );
    assert!(
        preparation
            .fs_call(&c("System.FilePath.readDir"), &[])
            .unwrap()
            .is_some()
    );
    let binding = preparation
        .fs_intrinsic_binding(&Operation::ReadDir.private_name())
        .unwrap();
    assert_eq!(binding.arguments, [ValueType::String]);
    assert_eq!(binding.argument_ownership, [ArgumentOwnership::Borrowed]);
    assert_eq!(binding.result_ownership, ResultOwnership::Owned);

    // readDir has no native Handle prerequisite. Do not accidentally route
    // its path through the separate opaque Handle representation.
    let without_handle = raw
        .constants()
        .fold(Environment::new(), |environment, (label, info)| {
            if label == &name("IO.FS.Handle") {
                environment
            } else {
                environment.add_decl(info.clone()).unwrap()
            }
        });
    assert!(
        fs::primitive_matches(
            &environment(&without_handle, None),
            Operation::ReadDir,
            &mut None,
            &mut 0,
            limits
        )
        .unwrap()
    );
}

#[test]
fn directory_contracts_refuse_dual_checked_projection_and_array_dependency_mutants() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    for target in ["IO.FS.DirEntry.fileName", "Array.size", "List.length"] {
        let label = name(target);
        let Some(ConstantInfo::Defn(original)) = raw.find(&label) else {
            panic!("actual {target}");
        };
        let mut changed = original.clone();
        fn replace_result(expression: &Expr, value: &Expr) -> Expr {
            match expression.node() {
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(
                    binder_name.clone(),
                    binder_type.clone(),
                    replace_result(body, value),
                    *binder_info,
                ),
                ExprNode::MData { expr, .. } => replace_result(expr, value),
                _ => value.clone(),
            }
        }
        changed.value = replace_result(
            &original.value,
            &if target == "IO.FS.DirEntry.fileName" {
                Expr::lit(Literal::Str("counterfeit-name".to_owned()))
            } else {
                nat::literal(0)
            },
        );
        let without = raw
            .constants()
            .fold(Environment::new(), |environment, (name, info)| {
                if name == &label {
                    environment
                } else {
                    environment.add_decl(info.clone()).unwrap()
                }
            });
        let admitted = Engine::from_environment(without)
            .admit_declaration(
                Declaration::Defn(changed),
                &KVMap::new(),
                EngineAdmissionLimits::for_stack_bytes(STACK),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            admitted.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        assert!(
            matches!(
                fs::primitive_matches(
                    &environment(&admitted.engine.environment, None),
                    Operation::ReadDir,
                    &mut None,
                    &mut 0,
                    IngressLimits::default(),
                ),
                Err(IngressError::UnsupportedNode { .. })
            ),
            "checked mutant {target}"
        );
    }
}

#[test]
fn directory_sources_preserve_logical_paths_names_and_native_order() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw, None));
    let root = engine.logical_root(&KVMap::new());
    let directory = directory("read-directory");
    for filename in ["z-last", "a-first", "λ🙂"] {
        std::fs::write(directory.join(filename), b"retained").unwrap();
    }
    std::fs::write(
        directory.join(std::ffi::OsString::from_vec(b"raw-\xff-end".to_vec())),
        b"retained",
    )
    .unwrap();
    let supplied = directory.join(".");
    let batch = run(
        &engine,
        &format!(
            "#eval System.FilePath.readDir (System.FilePath.mk {})",
            quoted(&supplied)
        ),
    );
    let execution = evaluation(&batch);
    assert_eq!(
        logical_entries(&execution.exit),
        expected_entries(&supplied)
    );
    let program = assert_rows(execution, &[Operation::ReadDir]);
    for wanted in ["extern:Array.size", "extern:Array.getInternal"] {
        assert!(program.functions().iter().flat_map(|function| &function.code).any(|instruction| matches!(instruction, Instruction::Intrinsic { row, .. } if row == wanted)));
    }
    for (value, expected) in [("entries.size", "4"), ("entries.toList.length", "4")] {
        let batch = run(
            &engine,
            &format!(
                "#eval (show IO Nat from do\n  let entries ← System.FilePath.readDir (System.FilePath.mk {})\n  (EST.pure ({value}) : IO Nat))",
                quoted(&supplied),
            ),
        );
        assert_eq!(
            nat_decimal(&child(returned(&evaluation(&batch).exit), 0)).as_deref(),
            Some(expected)
        );
    }
    let entries = expected_entries(&supplied);
    for (value, expected) in [
        ("entry.root.toString", supplied.to_str().unwrap().to_owned()),
        ("entry.fileName", entries[0].1.clone()),
    ] {
        let batch = run(
            &engine,
            &format!(
                "#eval (show IO String from do\n  let entries ← System.FilePath.readDir (System.FilePath.mk {})\n  match entries.toList with\n  | [] => (EST.pure \"\" : IO String)\n  | entry :: _ => (EST.pure ({value}) : IO String))",
                quoted(&supplied),
            ),
        );
        assert_eq!(
            string(&child(returned(&evaluation(&batch).exit), 0)),
            expected
        );
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn directory_saved_replacement_actions_replay_live_entries_and_obey_conversion_fuel() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = registered_reader(&environment(&raw, None));
    let parent = directory("deferred-directory");
    let late = parent.join("created-after-compilation");
    let saved = run(
        &engine,
        &format!(
            "def readDirectory := {REPLACEMENT}\ndef savedDirectory : IO (Array IO.FS.DirEntry) := readDirectory (System.FilePath.mk {})",
            quoted(&late),
        ),
    );
    for execution in &saved.batch.executions {
        assert!(returned(&execution.exit).closure_shell_parts().is_some());
    }
    assert!(
        !late.exists(),
        "constructing a read action does not enumerate or create its path"
    );
    std::fs::create_dir(&late).unwrap();
    let batch = run(&saved.batch.engine, "#eval savedDirectory");
    let execution = evaluation(&batch);
    assert!(logical_entries(&execution.exit).is_empty());
    let VmExit::Returned(completed) = &execution.exit else {
        unreachable!();
    };
    let baseline_steps = completed.usage.steps;
    let program = assert_rows(execution, &[Operation::ReadDir]);
    assert_eq!(
        flbc::encode_canonical(&program, flbc::CodecLimits::default()).unwrap(),
        execution.flbc_artifact
    );
    for index in 0..64 {
        std::fs::write(late.join(format!("entry-{index}")), b"retained").unwrap();
    }
    let stopped = execute_golem_with_options(
        &program,
        &KVMap::new(),
        VmExecutionLimits {
            max_steps: baseline_steps,
            ..VmExecutionLimits::default()
        },
    );
    let Outcome::Inconclusive(stop) = &stopped else {
        panic!("larger live results must exhaust conversion fuel: {stopped:?}");
    };
    let InconclusiveCause::ResourceExhausted { usage } = &stop.cause else {
        panic!("conversion fuel must report resource exhaustion: {stop:?}");
    };
    assert_eq!(usage.reason, ResourceReason::ExecutionSteps);
    assert_eq!(usage.allowed, baseline_steps);
    assert_eq!(usage.observed, baseline_steps + 1);
    let replay =
        execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::user_program())
            .into_complete()
            .unwrap();
    assert_eq!(logical_entries(&replay), expected_entries(&late));
    let again = run(&saved.batch.engine, "#eval savedDirectory");
    assert_eq!(
        logical_entries(&evaluation(&again).exit),
        expected_entries(&late)
    );
}

#[test]
fn directory_native_errors_remain_checked_catchable_values() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw, None));
    let directory = directory("directory-source-errors");
    let file = directory.join("ordinary-file");
    std::fs::write(&file, b"retained").unwrap();
    for (path, tag, code, details) in [
        (
            directory.join("missing").to_str().unwrap().to_owned(),
            11,
            2,
            "No such file or directory",
        ),
        (file.to_str().unwrap().to_owned(), 15, 20, "Not a directory"),
        ("bad\0path".to_owned(), 12, 22, "string contains NUL bytes"),
    ] {
        let quoted = format!("{path:?}").replace("\\0", "\\x00");
        let source = format!("#eval System.FilePath.readDir (System.FilePath.mk {quoted})");
        let batch = run(&engine, &source);
        assert_error(&evaluation(&batch).exit, tag, code, Some(&path), details);
        let recovered = run(
            &engine,
            &format!(
                "#eval (show IO Nat from do\n  try\n    let _ ← System.FilePath.readDir (System.FilePath.mk {quoted})\n    (EST.pure 0 : IO Nat)\n  catch _ =>\n    (EST.pure 42 : IO Nat))",
            ),
        );
        assert_eq!(
            nat_decimal(&child(returned(&evaluation(&recovered).exit), 0)).as_deref(),
            Some("42")
        );
    }
    assert_eq!(std::fs::read(file).unwrap(), b"retained");
}

#[test]
fn directory_actual_pinned_io_import_executes_and_replays_live_entries() {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
        return;
    };
    std::thread::Builder::new().stack_size(STACK).spawn(move || {
        use crate::source_check::modules::execution::SourceProgramLimits;
        use crate::source_check::modules::imported::SourceOleanImportLimits;
        use std::collections::BTreeMap;
        use std::num::NonZeroUsize;

        const BYTES: usize = 512 * 1024 * 1024;
        let root = name("Init.System.IO");
        let mut pending = vec![root.clone()];
        let mut artifacts = BTreeMap::new();
        while let Some(module) = pending.pop() {
            if artifacts.contains_key(&module) { continue; }
            let path = library.join(module.to_display_string().replace('.', "/")).with_extension("olean");
            let public = std::fs::read(&path).unwrap();
            pending.extend(crate::olean_module_imports(&public, OleanDecodeLimits::new(BYTES)).unwrap());
            let optional = |path: PathBuf| match std::fs::read(&path) {
                Ok(bytes) => Some(bytes),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
                Err(error) => panic!("{}: {error}", path.display()),
            };
            artifacts.insert(module, (
                public,
                optional(path.with_extension("olean.server")),
                optional(path.with_extension("olean.private")),
            ));
        }
        let modules: Vec<_> = artifacts.iter().map(|(name, (public, server, private))| OleanModuleInput {
            name,
            artifact: public,
            server_artifact: server.as_deref(),
            private_artifact: private.as_deref(),
        }).collect();
        let mut limits = SourceOleanImportLimits::new(OleanCheckLimits::new(BYTES, Budget::for_stack_bytes(STACK)));
        limits.jobs = OleanFrontierJobs { threads: NonZeroUsize::new(1).unwrap(), worker_stack_bytes: STACK };
        let imported = Engine::from_environment(Environment::new()).import_olean_modules_for_source(
            &modules, std::slice::from_ref(&root), &KVMap::new(), limits,
        ).expect("the actual IO closure imports").into_complete().expect("both checking engines admit the actual IO closure");
        assert_eq!(imported.checked.modules.len(), artifacts.len());
        let logical_root = imported.engine.logical_root(&KVMap::new());
        let directory = directory("actual-import-directory");
        for filename in ["z-last", "a-first", "λ🙂"] {
            std::fs::write(directory.join(filename), b"retained actual-import fixture").unwrap();
        }
        let source = format!(
            "prelude\nimport Init.System.IO\n#eval System.FilePath.readDir (System.FilePath.mk {})\n#eval (show IO Nat from do\n  let entries ← System.FilePath.readDir (System.FilePath.mk {})\n  return entries.size)",
            quoted(&directory), quoted(&directory),
        );
        let main = name("DirectoryImportProbe");
        let program = imported.execute_source_modules(
            &[SourceModuleInput { name: &main, source: source.as_bytes() }],
            &main,
            &KVMap::new(),
            SourceProgramLimits::new(EngineExecutionLimits::new(Budget::for_stack_bytes(STACK))),
            None,
        ).expect("ordinary source imports and reads its owned directory").into_complete().expect("directory source evaluation completes");
        let batch = &program.modules[0].commands;
        let read = &batch.batch.executions[batch.batch.source_evaluation_indices[0]];
        assert_eq!(read.checker.ground, CheckerAdmissionGround::BodyCheckedAgainstDeclaredType);
        assert_eq!(logical_entries(&read.exit), expected_entries(&directory));
        assert_eq!(nat_decimal(&child(returned(&evaluation(batch).exit), 0)).as_deref(), Some("3"));
        let replay = assert_rows(read, &[Operation::ReadDir]);
        std::fs::write(directory.join("added-after-compilation"), b"retained replay fixture").unwrap();
        let exit = execute_golem_with_options(&replay, &KVMap::new(), VmExecutionLimits::default()).into_complete().unwrap();
        assert_eq!(logical_entries(&exit), expected_entries(&directory));
        assert_eq!(imported.engine.logical_root(&KVMap::new()), logical_root);
    }).unwrap().join().unwrap();
}
