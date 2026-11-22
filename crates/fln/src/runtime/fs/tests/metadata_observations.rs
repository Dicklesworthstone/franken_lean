//! Checked metadata records, typed errors, deferred actions and native TTY rows.
use super::*;
use std::os::unix::fs::{MetadataExt, symlink};
use std::time::{Duration, UNIX_EPOCH};

fn environment(raw: &Environment) -> Environment {
    [
        Operation::Metadata,
        Operation::SymlinkMetadata,
        Operation::Open,
        Operation::IsTty,
    ]
    .into_iter()
    .fold(raw.clone(), |environment, operation| {
        register_one(&environment, operation, false)
    })
}

fn number(value: &Obj) -> u64 {
    nat_decimal(value).unwrap().parse().unwrap()
}

fn word(value: &Obj) -> u64 {
    assert_constructor(value, 0, 1);
    let bits = child(value, 0);
    assert_constructor(&bits, 0, 1);
    let finite = child(&bits, 0);
    assert_constructor(&finite, 0, 2);
    number(&child(&finite, 0))
}

fn timestamp(value: &Obj) -> (i128, u64) {
    assert_constructor(value, 0, 2);
    let integer = child(value, 0);
    let tag = integer.header().tag;
    assert!(tag <= 1);
    assert_constructor(&integer, tag, 1);
    let magnitude = i128::from(number(&child(&integer, 0)));
    let seconds = if tag == 0 { magnitude } else { -magnitude - 1 };
    (seconds, word(&child(value, 1)))
}

fn metadata_value(exit: &VmExit) -> Obj {
    let result = returned(exit);
    assert_constructor(result, 0, 2);
    assert_eq!(child(result, 1).unbox(), 0);
    let metadata = child(result, 0);
    assert_constructor(&metadata, 0, 5);
    metadata
}

fn assert_metadata(exit: &VmExit, expected: &std::fs::Metadata, kind: u8) {
    let value = metadata_value(exit);
    assert_eq!(
        timestamp(&child(&value, 0)),
        (i128::from(expected.atime()), expected.atime_nsec() as u64)
    );
    assert_eq!(
        timestamp(&child(&value, 1)),
        (i128::from(expected.mtime()), expected.mtime_nsec() as u64)
    );
    assert_eq!(word(&child(&value, 2)), expected.size());
    assert_constructor(&child(&value, 3), kind, 0);
    assert_eq!(word(&child(&value, 4)), expected.nlink());
}

#[test]
fn metadata_contracts_require_exact_data_and_independent_native_authority() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    fs::assert_pin_models(&raw);
    let limits = IngressLimits::default();
    for operation in [
        Operation::Metadata,
        Operation::SymlinkMetadata,
        Operation::IsTty,
    ] {
        assert!(!fs::primitive_matches(&raw, operation, &mut None, &mut 0, limits).unwrap());
        let exact = register_one(&raw, operation, false);
        let mut work = 0;
        assert!(fs::primitive_matches(&exact, operation, &mut None, &mut work, limits).unwrap());
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
        let mut preparation = Preparation::new(&exact, limits);
        assert!(
            preparation
                .fs_call(&Expr::const_(operation.source_name(), Vec::new()), &[])
                .unwrap()
                .is_some()
        );
        let binding = preparation
            .fs_intrinsic_binding(&operation.private_name())
            .unwrap();
        assert_eq!(binding.argument_ownership, [ArgumentOwnership::Borrowed]);
        assert_eq!(binding.result_ownership, ResultOwnership::Owned);
        assert_eq!(binding.effect, EffectClass::Io);
        let lookalike =
            Name::from_components([operation.source_name().to_display_string().as_str()]);
        assert!(
            preparation
                .fs_call(&Expr::const_(lookalike, vec![]), &[])
                .unwrap()
                .is_none()
        );
    }
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
            &register_one(&without_handle, Operation::Metadata, false),
            Operation::Metadata,
            &mut None,
            &mut 0,
            limits
        )
        .unwrap()
    );
}

#[test]
fn metadata_refuses_same_typed_checked_projection_changes() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    for (target, family, replacement) in [
        ("IO.FS.Metadata.byteSize", "IO.FS.Metadata", 4),
        ("IO.FS.Metadata.accessed", "IO.FS.Metadata", 1),
    ] {
        let label = name(target);
        let Some(ConstantInfo::Defn(original)) = raw.find(&label) else {
            panic!("actual metadata projection {target}");
        };
        let mut changed = original.clone();
        changed.value = Expr::lam(
            Name::anonymous(),
            c(family),
            Expr::proj(name(family), replacement, b(0).unwrap()),
            BinderInfo::Default,
        );
        let without = raw
            .constants()
            .fold(Environment::new(), |environment, (candidate, info)| {
                if candidate == &label {
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
        for operation in [Operation::Metadata, Operation::SymlinkMetadata] {
            assert!(matches!(
                fs::primitive_matches(
                    &register_one(&admitted.engine.environment, operation, false),
                    operation,
                    &mut None,
                    &mut 0,
                    IngressLimits::default()
                ),
                Err(IngressError::UnsupportedNode { .. })
            ));
        }
    }
}

#[test]
fn metadata_sources_rebuild_logical_records_and_full_timestamp_values() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let logical_root = engine.logical_root(&KVMap::new());
    let root = directory("metadata-source-λ");
    let file = root.join("file");
    let hard = root.join("hard");
    let link = root.join("link");
    std::fs::write(&file, b"seven!!").unwrap();
    std::fs::hard_link(&file, &hard).unwrap();
    symlink(&file, &link).unwrap();
    std::fs::File::open(&file)
        .unwrap()
        .set_times(
            std::fs::FileTimes::new()
                .set_accessed(UNIX_EPOCH - Duration::from_secs(1))
                .set_modified(UNIX_EPOCH + Duration::new(2_200_000_000, 123_456_789)),
        )
        .unwrap();
    for (operation, path, expected, kind) in [
        (
            Operation::Metadata,
            &file,
            std::fs::metadata(&file).unwrap(),
            1,
        ),
        (
            Operation::Metadata,
            &root,
            std::fs::metadata(&root).unwrap(),
            0,
        ),
        (
            Operation::Metadata,
            &link,
            std::fs::metadata(&link).unwrap(),
            1,
        ),
        (
            Operation::SymlinkMetadata,
            &link,
            std::fs::symlink_metadata(&link).unwrap(),
            2,
        ),
    ] {
        let batch = run(
            &engine,
            &format!(
                "#eval {} (System.FilePath.mk {})",
                operation.source_name().to_display_string(),
                quoted(path)
            ),
        );
        let execution = evaluation(&batch);
        assert_metadata(&execution.exit, &expected, kind);
        assert_rows(execution, &[operation]);
    }
    // Source projections execute on rebuilt records, not native scalar offsets.
    let batch = run(
        &engine,
        &format!(
            "#eval (show IO UInt64 from do\n  let m ← System.FilePath.metadata (System.FilePath.mk {})\n  (EST.pure m.byteSize : IO UInt64))",
            quoted(&file)
        ),
    );
    assert_eq!(word(&child(returned(&evaluation(&batch).exit), 0)), 7);
    assert_eq!(engine.logical_root(&KVMap::new()), logical_root);
}

#[test]
fn metadata_saved_actions_replay_live_observations_and_keep_errors_catchable() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = directory("metadata-deferred");
    let late = root.join("late");
    let saved = run(
        &engine,
        &format!(
            "def observeMetadata := System.FilePath.metadata\ndef savedMetadata : IO IO.FS.Metadata := observeMetadata (System.FilePath.mk {})",
            quoted(&late)
        ),
    );
    for execution in &saved.batch.executions {
        assert!(returned(&execution.exit).closure_shell_parts().is_some());
    }
    assert!(!late.exists());
    std::fs::write(&late, b"one").unwrap();
    let first = run(&saved.batch.engine, "#eval savedMetadata");
    let execution = evaluation(&first);
    assert_metadata(&execution.exit, &std::fs::metadata(&late).unwrap(), 1);
    let program = assert_rows(execution, &[Operation::Metadata]);
    std::fs::write(&late, b"a much longer value").unwrap();
    let replay =
        execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::user_program())
            .into_complete()
            .unwrap();
    assert_metadata(&replay, &std::fs::metadata(&late).unwrap(), 1);

    let missing = root.join("missing");
    let dangling = root.join("dangling");
    symlink(&missing, &dangling).unwrap();
    for operation in [Operation::Metadata, Operation::SymlinkMetadata] {
        for (path, tag, code, details) in [
            (
                missing.to_str().unwrap().to_owned(),
                11,
                (-2_i32) as u32,
                "no such file or directory",
            ),
            ("bad\0path".to_owned(), 12, 22, "string contains NUL bytes"),
        ] {
            let quoted = format!("{path:?}").replace("\\0", "\\x00");
            let invocation = format!(
                "{} (System.FilePath.mk {quoted})",
                operation.source_name().to_display_string()
            );
            let failed = run(&engine, &format!("#eval {invocation}"));
            assert_error(&evaluation(&failed).exit, tag, code, Some(&path), details);
            let recovered = run(
                &engine,
                &format!(
                    "#eval (show IO Nat from do\n  try\n    let _ ← {invocation}\n    (EST.pure 0 : IO Nat)\n  catch _ =>\n    (EST.pure 42 : IO Nat))"
                ),
            );
            assert_eq!(
                number(&child(returned(&evaluation(&recovered).exit), 0)),
                42
            );
        }
    }
    let unlinked = run(
        &engine,
        &format!(
            "#eval System.FilePath.symlinkMetadata (System.FilePath.mk {})",
            quoted(&dangling)
        ),
    );
    assert_metadata(
        &evaluation(&unlinked).exit,
        &std::fs::symlink_metadata(&dangling).unwrap(),
        2,
    );
    let followed = run(
        &engine,
        &format!(
            "#eval System.FilePath.metadata (System.FilePath.mk {})",
            quoted(&dangling)
        ),
    );
    assert_error(
        &evaluation(&followed).exit,
        11,
        (-2_i32) as u32,
        Some(dangling.to_str().unwrap()),
        "no such file or directory",
    );
}

#[test]
fn ordinary_path_exists_and_is_dir_helpers_execute_the_metadata_leaf() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = directory("metadata-ordinary-helpers");
    let file = root.join("file");
    let missing = root.join("missing");
    std::fs::write(&file, b"retained").unwrap();
    for (helper, path, expected) in [
        ("System.FilePath.pathExists", &file, true),
        ("System.FilePath.pathExists", &missing, false),
        ("System.FilePath.isDir", &root, true),
        ("System.FilePath.isDir", &file, false),
        ("System.FilePath.isDir", &missing, false),
    ] {
        let batch = run(
            &engine,
            &format!("#eval {helper} (System.FilePath.mk {})", quoted(path)),
        );
        let execution = evaluation(&batch);
        let result = returned(&execution.exit);
        assert_constructor(result, 0, 2);
        assert_eq!(child(result, 0).unbox(), usize::from(expected));
        assert_eq!(child(result, 1).unbox(), 0);
        assert_rows(execution, &[Operation::Metadata]);
    }
}

#[test]
fn terminal_source_alias_preserves_base_io_result_and_native_handle_lifetime() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = directory("terminal-source");
    let file = root.join("file");
    std::fs::write(&file, b"preserved").unwrap();
    let batch = run(
        &engine,
        &format!(
            "def observeTerminal := IO.FS.Handle.isTty\ndef terminalProbe (path : System.FilePath) : IO Bool := do\n  let handle ← IO.FS.Handle.mk path IO.FS.Mode.read\n  BaseIO.toIO (observeTerminal handle)\n#eval terminalProbe (System.FilePath.mk {})",
            quoted(&file)
        ),
    );
    let execution = evaluation(&batch);
    let value = returned(&execution.exit);
    assert_constructor(value, 0, 2);
    assert!(child(value, 0).is_scalar());
    assert_eq!(child(value, 0).unbox(), 0);
    assert_eq!(child(value, 1).unbox(), 0);
    assert_rows(execution, &[Operation::Open, Operation::IsTty]);
    assert_eq!(std::fs::read(file).unwrap(), b"preserved");
}
