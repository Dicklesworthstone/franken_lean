//! Checked source and replayed FLBC over actual pinned dependency declarations.
//! This fixture does not claim full Init.System.IO module admission.

use super::*;

fn environment(raw: &Environment) -> Environment {
    register_one(&register(raw), Operation::Flush, false)
}

#[test]
fn flush_requires_its_own_exact_checked_contract() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    fs::assert_pin_models(&raw);
    let limits = IngressLimits::default();
    assert!(
        !fs::primitive_matches(&register(&raw), Operation::Flush, &mut None, &mut 0, limits,)
            .unwrap()
    );
    assert!(
        fs::primitive_matches(
            &register_one(&raw, Operation::Flush, true),
            Operation::Flush,
            &mut None,
            &mut 0,
            limits,
        )
        .is_err()
    );
    let exact = environment(&raw);
    let mut work = 0;
    assert!(fs::primitive_matches(&exact, Operation::Flush, &mut None, &mut work, limits).unwrap());
    assert!(matches!(
        fs::primitive_matches(
            &exact,
            Operation::Flush,
            &mut None,
            &mut 0,
            IngressLimits {
                max_nodes: work - 1,
                ..limits
            },
        ),
        Err(IngressError::ResourceLimit { .. })
    ));

    // A different, well-typed Handle -> IO Unit body cannot authorize flush.
    let label = Operation::Flush.source_name();
    let ConstantInfo::Opaque(original) = raw.find(&label).unwrap() else {
        panic!("the pinned opaque flush declaration")
    };
    let mut changed = original.clone();
    changed.value = c("IO.FS.Handle.rewind");
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
            Operation::Flush,
            &mut None,
            &mut 0,
            limits,
        ),
        Err(IngressError::UnsupportedNode { .. })
    ));
}

#[test]
fn checked_flush_aliases_are_deferred_reusable_and_visible_before_handle_close() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let directory = directory("flush");
    let file = directory.join("buffered.txt");
    let path = quoted(&file);
    let saved = run(
        &engine,
        &format!(
            "def flushAlias := IO.FS.Handle.flush\n\
             def savedFlush : IO IO.FS.Handle := do\n\
             \x20 let h ← IO.FS.Handle.mk {path} IO.FS.Mode.write\n\
             \x20 let flush := flushAlias h\n\
             \x20 h.putStr \"first λ\\x00\"\n\
             \x20 flush\n\
             \x20 h.putStr \"second 🙂\"\n\
             \x20 flush\n\
             \x20 return h"
        ),
    );
    assert!(
        !file.exists(),
        "constructing the saved action must not open its file"
    );
    let batch = run(&saved.batch.engine, "#eval savedFlush");
    let execution = evaluation(&batch);
    let packet = returned(&execution.exit);
    assert_constructor(packet, 0, 2);
    let handle = child(packet, 0);
    assert!(handle.is_file_handle());
    assert_eq!(child(packet, 1).unbox(), 0);
    let expected = "first λ\0second 🙂".as_bytes();
    assert_eq!(
        std::fs::read(&file).unwrap(),
        expected,
        "both flushes must publish buffered bytes while the handle remains live"
    );
    let program = assert_rows(
        execution,
        &[Operation::Open, Operation::PutStr, Operation::Flush],
    );
    let replay = execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
        .into_complete()
        .unwrap();
    let replay_handle = child(returned(&replay), 0);
    assert!(replay_handle.is_file_handle());
    assert_eq!(std::fs::read(&file).unwrap(), expected);
    assert!(handle.is_file_handle());
}

#[cfg(target_os = "linux")]
#[test]
fn checked_flush_errors_follow_ordinary_io_recovery() {
    use std::os::unix::fs::{FileTypeExt, MetadataExt};

    let Ok(device) = std::fs::symlink_metadata("/dev/full") else {
        return;
    };
    if !device.file_type().is_char_device() || device.rdev() != 0x107 {
        return;
    }
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let batch = run(
        &engine,
        "#eval do\n\
         \x20 let h ← IO.FS.Handle.mk \"/dev/full\" IO.FS.Mode.write\n\
         \x20 h.putStr \"buffered\"\n\
         \x20 try\n\
         \x20   h.flush\n\
         \x20   return (0 : Nat)\n\
         \x20 catch _ => return 7",
    );
    let execution = evaluation(&batch);
    assert_rows(
        execution,
        &[Operation::Open, Operation::PutStr, Operation::Flush],
    );
    let packet = returned(&execution.exit);
    assert_constructor(packet, 0, 2);
    assert_eq!(child(packet, 0).unbox(), 7);
    assert_eq!(child(packet, 1).unbox(), 0);
}
