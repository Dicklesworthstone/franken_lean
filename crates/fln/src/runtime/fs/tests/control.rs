//! Checked Handle controls over pinned declarations and replayable FLBC.

use super::*;

const CONTROLS: [Operation; 5] = [
    Operation::Rewind,
    Operation::Truncate,
    Operation::Lock,
    Operation::TryLock,
    Operation::Unlock,
];

fn environment(raw: &Environment) -> Environment {
    CONTROLS
        .into_iter()
        .chain([Operation::Flush, Operation::GetLine])
        .fold(register(raw), |environment, operation| {
            register_one(&environment, operation, false)
        })
}

#[test]
fn handle_controls_require_independent_exact_checked_contracts() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    fs::assert_pin_models(&raw);
    let exact = environment(&raw);
    let limits = IngressLimits::default();
    for operation in CONTROLS {
        assert!(
            !fs::primitive_matches(&register(&raw), operation, &mut None, &mut 0, limits).unwrap(),
            "{operation:?} needs its own extern authority"
        );
        assert!(
            fs::primitive_matches(
                &register_one(&raw, operation, true),
                operation,
                &mut None,
                &mut 0,
                limits,
            )
            .is_err()
        );
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
                },
            ),
            Err(IngressError::ResourceLimit { .. })
        ));
    }

    // An independently checked body of the same type does not acquire the
    // native meaning of rewind merely by retaining its name and extern row.
    let label = Operation::Rewind.source_name();
    let ConstantInfo::Opaque(original) = raw.find(&label).unwrap() else {
        panic!("pinned Handle.rewind")
    };
    let mut changed = original.clone();
    changed.value = c("IO.FS.Handle.flush");
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
            Operation::Rewind,
            &mut None,
            &mut 0,
            limits,
        ),
        Err(IngressError::UnsupportedNode { .. })
    ));
}

#[test]
fn checked_cursor_actions_are_deferred_reusable_and_replay_real_truncation() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = directory("handle-cursor");
    let file = root.join("cursor.txt");
    std::fs::write(&file, "original suffix").unwrap();
    let saved = run(
        &engine,
        &format!(
            "def rewindAlias := IO.FS.Handle.rewind\n\
             def truncateAlias := IO.FS.Handle.truncate\n\
             def savedCursor : IO String := do\n\
             \x20 let h ← IO.FS.Handle.mk {} IO.FS.Mode.readWrite\n\
             \x20 let rewind := rewindAlias h\n\
             \x20 let trim := truncateAlias h\n\
             \x20 h.putStr \"longer replacement\"\n\
             \x20 rewind\n\
             \x20 h.putStr \"λ\"\n\
             \x20 h.flush\n\
             \x20 trim\n\
             \x20 rewind\n\
             \x20 h.getLine",
            quoted(&file)
        ),
    );
    assert_eq!(std::fs::read(&file).unwrap(), b"original suffix");
    let batch = run(&saved.batch.engine, "#eval savedCursor");
    let execution = evaluation(&batch);
    assert_text(&child(returned(&execution.exit), 0), "λ");
    assert_eq!(child(returned(&execution.exit), 1).unbox(), 0);
    assert_eq!(std::fs::read(&file).unwrap(), "λ".as_bytes());
    let program = assert_rows(
        execution,
        &[
            Operation::Open,
            Operation::PutStr,
            Operation::Rewind,
            Operation::Flush,
            Operation::Truncate,
            Operation::GetLine,
        ],
    );
    std::fs::write(&file, "different starting contents").unwrap();
    assert!(matches!(
        execute_golem_with_options(
            &program,
            &KVMap::new(),
            VmExecutionLimits {
                max_steps: 0,
                ..VmExecutionLimits::default()
            },
        ),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(
        std::fs::read(&file).unwrap(),
        b"different starting contents"
    );
    let replay = execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
        .into_complete()
        .unwrap();
    assert_text(&child(returned(&replay), 0), "λ");
    assert_eq!(std::fs::read(&file).unwrap(), "λ".as_bytes());
}

fn locking_source(file: &Path) -> String {
    let path = quoted(file);
    format!(
        "def lockAlias := @IO.FS.Handle.lock\n\
         def tryLockAlias := @IO.FS.Handle.tryLock\n\
         def unlockAlias := IO.FS.Handle.unlock\n\
         #eval (show IO Nat from do\n\
         \x20 let first ← IO.FS.Handle.mk {path} IO.FS.Mode.readWrite\n\
         \x20 let second ← IO.FS.Handle.mk {path} IO.FS.Mode.readWrite\n\
         \x20 let shared := lockAlias first false\n\
         \x20 let release := unlockAlias first\n\
         \x20 shared\n\
         \x20 let a ← tryLockAlias second false\n\
         \x20 let b ← second.tryLock\n\
         \x20 release\n\
         \x20 let c ← second.tryLock\n\
         \x20 let d ← first.tryLock\n\
         \x20 second.unlock\n\
         \x20 first.lock\n\
         \x20 let e ← tryLockAlias first true\n\
         \x20 release\n\
         \x20 release\n\
         \x20 return if a then (if b then 0 else (if c then (if d then 0 else (if e then 7 else 0)) else 0)) else 0)"
    )
}

#[test]
fn checked_lock_aliases_defaults_contention_and_release_match_the_pin() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let root = directory("handle-locks");
    let file = root.join("lock.txt");
    std::fs::write(&file, "preserved").unwrap();
    let source = locking_source(&file);
    let batch = run(&Engine::from_environment(environment(&raw)), &source);
    let execution = evaluation(&batch);
    assert_eq!(child(returned(&execution.exit), 0).unbox(), 7);
    let program = assert_rows(
        execution,
        &[
            Operation::Open,
            Operation::Lock,
            Operation::TryLock,
            Operation::Unlock,
        ],
    );
    let replay = execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
        .into_complete()
        .unwrap();
    assert_eq!(child(returned(&replay), 0).unbox(), 7);
    assert_eq!(std::fs::read(&file).unwrap(), b"preserved");

    let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB").unwrap());
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .unwrap_or_else(|| library.parent().unwrap().parent().unwrap().join("bin/lean"));
    assert!(
        reference.is_file(),
        "the pinned binary accompanies its library"
    );
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
    assert_eq!(std::fs::read(&file).unwrap(), b"preserved");
}

#[test]
fn checked_read_only_truncation_keeps_ordinary_io_recovery() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let root = directory("handle-read-only");
    let file = root.join("read-only.txt");
    std::fs::write(&file, "preserved suffix").unwrap();
    let batch = run(
        &Engine::from_environment(environment(&raw)),
        &format!(
            "#eval (show IO Nat from do\n\
             \x20 let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n\
             \x20 h.rewind\n\
             \x20 try\n\
             \x20   h.truncate\n\
             \x20   return 0\n\
             \x20 catch _ => return 7)",
            quoted(&file)
        ),
    );
    let execution = evaluation(&batch);
    assert_eq!(child(returned(&execution.exit), 0).unbox(), 7);
    assert_rows(
        execution,
        &[Operation::Open, Operation::Rewind, Operation::Truncate],
    );
    assert_eq!(std::fs::read(&file).unwrap(), b"preserved suffix");
}
