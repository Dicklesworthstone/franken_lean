//! Exact path-operation contracts, checked source actions, and fresh FLBC replay.
use super::*;

const OPERATIONS: [Operation; 5] = [
    Operation::CreateDir,
    Operation::RemoveDir,
    Operation::RemoveFile,
    Operation::Rename,
    Operation::HardLink,
];

fn environment(raw: &Environment) -> Environment {
    OPERATIONS
        .into_iter()
        .fold(register(raw), |environment, operation| {
            register_one(&environment, operation, false)
        })
}

#[test]
fn mutation_contracts_require_exact_paths_opaques_and_each_native_row() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    fs::assert_pin_models(&raw);
    let limits = IngressLimits::default();
    for operation in OPERATIONS {
        assert!(!fs::primitive_matches(&raw, operation, &mut None, &mut 0, limits).unwrap());
        let exact = register_one(&raw, operation, false);
        let mut work = 0;
        assert!(fs::primitive_matches(&exact, operation, &mut None, &mut work, limits).unwrap());
        assert!(
            fs::primitive_matches(
                &register_one(&raw, operation, true),
                operation,
                &mut None,
                &mut 0,
                limits
            )
            .is_err()
        );
        assert!(matches!(
            fs::primitive_matches(
                &exact,
                operation,
                &mut None,
                &mut 0,
                IngressLimits {
                    max_nodes: work - 1,
                    ..limits
                }
            ),
            Err(IngressError::ResourceLimit { .. })
        ));
        let mut preparation = Preparation::new(&exact, limits);
        assert!(
            preparation
                .fs_call(&Expr::const_(operation.source_name(), vec![]), &[])
                .unwrap()
                .is_some()
        );
        let binding = preparation
            .fs_intrinsic_binding(&operation.private_name())
            .unwrap();
        assert_eq!(
            binding.arguments,
            vec![ValueType::String; operation.source_arity()]
        );
        assert_eq!(
            binding.argument_ownership,
            vec![ArgumentOwnership::Borrowed; operation.source_arity()]
        );
        assert_eq!(binding.result_ownership, ResultOwnership::Owned);
    }

    // A same-typed alternate body must never authorize effects merely because
    // its name and extern annotation look like the pin's declaration.
    let label = Operation::RemoveFile.source_name();
    let ConstantInfo::Opaque(original) = raw.find(&label).unwrap() else {
        panic!("pinned removeFile")
    };
    let mut changed = original.clone();
    changed.value = c("IO.FS.removeDir");
    let without = raw
        .constants()
        .fold(Environment::new(), |env, (name, info)| {
            if name == &label {
                env
            } else {
                env.add_decl(info.clone()).unwrap()
            }
        });
    let admitted = Engine::from_environment(without)
        .admit_declaration(
            Declaration::Opaque(changed),
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
    assert!(matches!(
        fs::primitive_matches(
            &environment(&admitted.engine.environment),
            Operation::RemoveFile,
            &mut None,
            &mut 0,
            limits
        ),
        Err(IngressError::UnsupportedNode { .. })
    ));
}

#[test]
fn checked_path_mutations_are_deferred_and_cleanup_replays_fresh_effects() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = directory("mutations-λ🙂");
    let child_dir = root.join("child");
    let original = child_dir.join("original");
    let linked = child_dir.join("linked");
    let renamed = child_dir.join("renamed");
    let kept = root.join("kept");
    std::fs::write(&kept, b"outside the removed directory").unwrap();
    let saved = run(
        &engine,
        &format!(
            "def createAlias := IO.FS.createDir\n\
         def renameAlias := IO.FS.rename\n\
         def createLater : IO Unit := createAlias {}\n\
         def finish : IO Unit := do\n\
         \x20 IO.FS.removeFile {}\n\
         \x20 IO.FS.removeFile {}\n\
         \x20 IO.FS.removeDir {}",
            quoted(&child_dir),
            quoted(&original),
            quoted(&renamed),
            quoted(&child_dir),
        ),
    );
    assert!(
        !child_dir.exists(),
        "compilation cannot execute a saved action"
    );
    let engine = &saved.batch.engine;
    let created = run(engine, "#eval createLater");
    assert_unit(&evaluation(&created).exit);
    assert!(child_dir.is_dir());
    assert_rows(evaluation(&created), &[Operation::CreateDir]);

    let written = run(
        engine,
        &format!("#eval IO.FS.writeFile {} \"first\"", quoted(&original)),
    );
    assert_unit(&evaluation(&written).exit);
    let linked_batch = run(
        engine,
        &format!(
            "#eval IO.FS.hardLink {} {}",
            quoted(&original),
            quoted(&linked)
        ),
    );
    assert_unit(&evaluation(&linked_batch).exit);
    assert_rows(evaluation(&linked_batch), &[Operation::HardLink]);
    std::fs::write(&original, "shared λ🙂 content").unwrap();
    assert_eq!(
        std::fs::read(&linked).unwrap(),
        "shared λ🙂 content".as_bytes()
    );
    let renamed_batch = run(
        engine,
        &format!("#eval renameAlias {} {}", quoted(&linked), quoted(&renamed)),
    );
    assert_unit(&evaluation(&renamed_batch).exit);
    assert_rows(evaluation(&renamed_batch), &[Operation::Rename]);
    assert!(!linked.exists());
    assert_eq!(
        std::fs::read(&renamed).unwrap(),
        "shared λ🙂 content".as_bytes()
    );

    let failed = run(
        engine,
        &format!("#eval IO.FS.removeDir {}", quoted(&child_dir)),
    );
    assert_constructor(returned(&evaluation(&failed).exit), 1, 2);
    assert!(
        original.exists() && renamed.exists(),
        "removeDir must not recurse"
    );
    let cleaned = run(engine, "#eval finish");
    assert_unit(&evaluation(&cleaned).exit);
    let artifact = assert_rows(
        evaluation(&cleaned),
        &[Operation::RemoveFile, Operation::RemoveDir],
    );
    assert!(!child_dir.exists());
    std::fs::create_dir(&child_dir).unwrap();
    std::fs::write(&original, b"fresh original").unwrap();
    std::fs::write(&renamed, b"fresh destination").unwrap();
    let replay = execute_golem_with_options(&artifact, &KVMap::new(), VmExecutionLimits::default())
        .into_complete()
        .unwrap();
    assert_unit(&replay);
    assert!(
        !child_dir.exists(),
        "retained bytecode must execute the new filesystem effects"
    );
    assert_eq!(
        std::fs::read(kept).unwrap(),
        b"outside the removed directory"
    );
}

fn lifecycle_source(root: &Path) -> String {
    let folder = root.join("work");
    let original = folder.join("original");
    let linked = folder.join("linked");
    let renamed = folder.join("renamed");
    format!(
        "#eval do\n\
         \x20 IO.FS.createDir {}\n\
         \x20 IO.FS.writeFile {} \"bytes λ🙂\"\n\
         \x20 IO.FS.hardLink {} {}\n\
         \x20 IO.FS.writeFile {} \"replaced destination\"\n\
         \x20 IO.FS.rename {} {}\n\
         \x20 try\n\
         \x20   IO.FS.createDir {}\n\
         \x20   return (0 : Nat)\n\
         \x20 catch _ =>\n\
         \x20   IO.FS.removeFile {}\n\
         \x20   IO.FS.removeFile {}\n\
         \x20   IO.FS.removeDir {}\n\
         \x20   return 7\n",
        quoted(&folder),
        quoted(&original),
        quoted(&original),
        quoted(&linked),
        quoted(&renamed),
        quoted(&linked),
        quoted(&renamed),
        quoted(&folder),
        quoted(&original),
        quoted(&renamed),
        quoted(&folder),
    )
}

#[test]
fn checked_path_lifecycle_and_error_recovery_match_the_pinned_reference() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB").unwrap());
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .unwrap_or_else(|| library.parent().unwrap().parent().unwrap().join("bin/lean"));
    assert!(
        reference.is_file(),
        "the pinned binary must accompany its library"
    );
    let root = directory("mutations-differential");
    let source = lifecycle_source(&root);
    let engine = Engine::from_environment(environment(&raw));
    let batch = run(&engine, &source);
    let execution = evaluation(&batch);
    let packet = returned(&execution.exit);
    assert_constructor(packet, 0, 2);
    assert_eq!(child(packet, 0).unbox(), 7);
    assert_rows(execution, &OPERATIONS);
    assert!(!root.join("work").exists());

    // Run exactly the same executable source and paths after the native
    // program restored their initial state. Only oracle imports are added.
    let fixture = root.join("Reference.lean");
    std::fs::write(
        &fixture,
        format!("prelude\nimport Init.System.IO\nimport Init.Data.Repr\n{source}"),
    )
    .unwrap();
    let output = std::process::Command::new(reference)
        .arg(&fixture)
        .env("LEAN_PATH", &library)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "7\n");
    assert!(output.stderr.is_empty());
    assert!(!root.join("work").exists());
}
