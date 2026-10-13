//! Checked source and FLBC execution over the actual pinned dependency slice.
//! This raw fixture is not full Init.System.IO module admission.

use super::*;
use fln_env::constants::{ConstantVal, ReducibilityHints};

fn environment(raw: &Environment) -> Environment {
    register_one(&register(raw), Operation::GetLine, false)
}

fn assert_line(exit: &VmExit, expected: &str) {
    let packet = returned(exit);
    assert_constructor(packet, 0, 2);
    assert_text(&child(packet, 0), expected);
    assert!(child(packet, 1).is_scalar());
    assert_eq!(child(packet, 1).unbox(), 0);
}

fn sequence(path: &Path, skip: usize) -> String {
    let mut source = format!(
        "#eval do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  let alias := h\n  let read := IO.FS.Handle.getLine alias\n",
        quoted(path)
    );
    for _ in 0..skip {
        source.push_str("  let _ ← read\n");
    }
    source.push_str("  read");
    source
}

#[test]
fn get_line_requires_its_own_extern_exact_string_models_and_private_layout() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    fs::assert_pin_models(&raw);
    let limits = IngressLimits::default();
    assert!(
        !fs::primitive_matches(
            &register(&raw),
            Operation::GetLine,
            &mut None,
            &mut 0,
            limits
        )
        .unwrap()
    );
    let exact = environment(&raw);
    let mut work = 0;
    assert!(
        fs::primitive_matches(&exact, Operation::GetLine, &mut None, &mut work, limits).unwrap()
    );
    assert!(matches!(
        fs::primitive_matches(
            &exact,
            Operation::GetLine,
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
            &register_one(&raw, Operation::GetLine, true),
            Operation::GetLine,
            &mut None,
            &mut 0,
            limits
        )
        .is_err()
    );
    assert!(
        fln_elab::externs::ExternTable::read(&exact)
            .unwrap()
            .get(&name("IO.getStdout"))
            .is_none()
    );

    let mut preparation = Preparation::new(&exact, limits);
    assert!(
        preparation
            .fs_call(&c("IO.FS.Handle.getLine"), &[])
            .unwrap()
            .is_some()
    );
    let binding = preparation
        .fs_intrinsic_binding(&Operation::GetLine.private_name())
        .unwrap();
    assert_eq!(binding.arguments, [ValueType::Abi]);
    assert_eq!(binding.argument_ownership, [ArgumentOwnership::Borrowed]);
    assert_eq!(binding.result_ownership, ResultOwnership::Owned);
    assert_eq!(binding.row, "extern:IO.FS.Handle.getLine");
    assert_eq!(
        preparation.fs.read_layout.as_ref().unwrap().transport_name,
        name(READ_TRANSPORT)
    );
    assert!(
        preparation
            .fs_call(&c("IO.FS.Handle.mk"), &[])
            .unwrap()
            .is_some()
    );
    assert_ne!(
        preparation.fs.read_layout.as_ref().unwrap().transport,
        preparation.fs.layout.as_ref().unwrap().transport
    );
    let lookalike = Name::from_components(["IO.FS.Handle.getLine"]);
    assert_ne!(lookalike, Operation::GetLine.source_name());
    assert!(
        preparation
            .fs_call(&Expr::const_(lookalike, Vec::new()), &[])
            .unwrap()
            .is_none()
    );

    for target in ["String", "String.ofByteArray", "ByteArray", "ByteArray.mk"] {
        let changed = raw
            .constants()
            .fold(Environment::new(), |environment, (label, info)| {
                let mut info = info.clone();
                if label == &name(target) {
                    match &mut info {
                        ConstantInfo::Induct(value) => value.num_params += 1,
                        ConstantInfo::Ctor(value) => value.num_fields += 1,
                        _ => unreachable!("the exact String and ByteArray families"),
                    }
                }
                environment.add_decl(info).unwrap()
            });
        assert!(
            matches!(
                fs::primitive_matches(
                    &environment(&changed),
                    Operation::GetLine,
                    &mut None,
                    &mut 0,
                    limits
                ),
                Err(IngressError::UnsupportedNode { .. })
            ),
            "mutated {target}"
        );
    }
    let collision = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(READ_TRANSPORT),
            level_params: Vec::new(),
            type_: Expr::sort(Level::one()),
        },
        value: c("Nat"),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(READ_TRANSPORT)],
    });
    // A real checked user name cannot acquire the private transport layout.
    let admitted = Engine::from_environment(exact)
        .admit_declaration(
            collision,
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
    let mut preparation = Preparation::new(&admitted.engine.environment, limits);
    assert!(
        preparation
            .fs_call(&c("IO.FS.Handle.getLine"), &[])
            .is_err()
    );
}

#[test]
fn get_line_rejects_checked_same_type_primitive_and_error_selector_changes() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    for target in ["IO.FS.Handle.getLine", "Nat.beq"] {
        let label = name(target);
        let changed = match raw.find(&label).unwrap() {
            ConstantInfo::Opaque(original) => {
                let mut value = original.clone();
                // readToEnd has the same type, but consumes all lines and has
                // different invalid-UTF8 semantics. A checked body is not an
                // authority grant for the native getLine implementation.
                value.value = Expr::lam(
                    Name::anonymous(),
                    c("IO.FS.Handle"),
                    Expr::app(c("IO.FS.Handle.readToEnd"), b(0).unwrap()),
                    BinderInfo::Default,
                );
                Declaration::Opaque(value)
            }
            ConstantInfo::Defn(original) => {
                let mut value = original.clone();
                value.value = Expr::lam(
                    Name::anonymous(),
                    c("Nat"),
                    Expr::lam(
                        Name::anonymous(),
                        c("Nat"),
                        c("Bool.true"),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                );
                Declaration::Defn(value)
            }
            _ => unreachable!("the pinned mutation targets"),
        };
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
                changed,
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
        let exact = environment(&admitted.engine.environment);
        assert!(
            matches!(
                fs::primitive_matches(
                    &exact,
                    Operation::GetLine,
                    &mut None,
                    &mut 0,
                    IngressLimits::default()
                ),
                Err(IngressError::UnsupportedNode { .. })
            ),
            "same-type {target}"
        );
    }
}

#[test]
fn ordinary_get_line_aliases_share_the_cursor_and_match_pinned_utf8_recovery() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = engine.logical_root(&KVMap::new());
    let directory = directory("read-lines");
    let file = directory.join("lines.bin");
    // Exact cases measured against the pin, including recovery groups where
    // Rust's from_utf8_lossy would produce a different replacement count.
    let pieces: &[(&[u8], &str)] = &[
        (b"lf\n", "lf\n"),
        (b"crlf\r\n", "crlf\r\n"),
        ("nul\0λ🙂\n".as_bytes(), "nul\0λ🙂\n"),
        (
            b"overlong:\xc0\xaf\xe0\x80\xaf\xf0\x80\x80\xaf\n",
            "overlong:���\n",
        ),
        (
            b"continuation:\x80\xbfA\xe2(\xa1B\xf0\x9fC\n",
            "continuation:�A�(�B�C\n",
        ),
        (b"surrogate:\xed\xa0\x80\xed\xbf\xbf\n", "surrogate:��\n"),
        (
            b"range:\xf4\x90\x80\x80\xf5\x80\x80\x80\xff\x80\x80\n",
            "range:���\n",
        ),
        (b"tail:\xe2\x82", "tail:�"),
        (b"", ""),
        (b"", ""),
    ];
    let bytes: Vec<_> = pieces
        .iter()
        .flat_map(|(bytes, _)| bytes.iter().copied())
        .collect();
    std::fs::write(&file, &bytes).unwrap();
    for (index, (_, expected)) in pieces.iter().enumerate() {
        let source = sequence(&file, index);
        let batch = run(&engine, &source);
        let execution = evaluation(&batch);
        assert_line(&execution.exit, expected);
        assert_rows(execution, &[Operation::Open, Operation::GetLine]);
    }
    let batch = run(
        &engine,
        &format!(
            "#eval do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  h.getLine",
            quoted(&file)
        ),
    );
    assert_line(&evaluation(&batch).exit, "lf\n");
    assert_eq!(std::fs::read(&file).unwrap(), bytes);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn saved_read_actions_remain_deferred_and_replay_opens_fresh_handles() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = engine.logical_root(&KVMap::new());
    let directory = directory("deferred-read");
    let file = directory.join("created-later.txt");
    let path = quoted(&file);
    let source = format!(
        "def savedRead : IO String := do\n  let h ← IO.FS.Handle.mk {path} IO.FS.Mode.read\n  IO.FS.Handle.getLine h\ndef readAlias := IO.FS.Handle.getLine"
    );
    let saved = run(&engine, &source);
    assert!(
        !file.exists(),
        "constructing an action never opens the path"
    );
    for execution in &saved.batch.executions {
        assert!(returned(&execution.exit).closure_shell_parts().is_some());
        assert!(execution.io_evaluation_outcome().unwrap().is_none());
    }
    std::fs::write(&file, b"first\nsecond\n").unwrap();
    let batch = run(&saved.batch.engine, "#eval savedRead\n#eval savedRead");
    for index in &batch.batch.source_evaluation_indices {
        assert_line(&batch.batch.executions[*index].exit, "first\n");
    }
    let execution = evaluation(&batch);
    let program = assert_rows(execution, &[Operation::Open, Operation::GetLine]);
    for expected in ["replacement\n", "λ\0replay\n"] {
        std::fs::write(&file, expected.as_bytes()).unwrap();
        let exit =
            execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
                .into_complete()
                .unwrap();
        assert_line(&exit, expected);
    }
    let repeated = run(&saved.batch.engine, "#eval savedRead\n#eval savedRead");
    assert_eq!(execution.flbc_artifact, evaluation(&repeated).flbc_artifact);

    std::fs::write(&file, b"one\ntwo\n").unwrap();
    let source = format!(
        "def retainedRead : IO (IO String) := fun world => match IO.FS.Handle.mk (System.FilePath.mk {path}) IO.FS.Mode.read world with | .ok h next => @EST.Out.ok IO.Error IO.RealWorld (IO String) (readAlias h) next | .error error next => @EST.Out.error IO.Error IO.RealWorld (IO String) error next\n#eval do\n  let read ← retainedRead\n  let _ ← read\n  read"
    );
    let retained = run(&saved.batch.engine, &source);
    assert_line(&evaluation(&retained).exit, "two\n");
    let explicit = format!(
        "#eval (show IO String from fun world => match IO.FS.Handle.mk (System.FilePath.mk {path}) IO.FS.Mode.read world with | .ok h next => IO.FS.Handle.getLine h next | .error error next => @EST.Out.error IO.Error IO.RealWorld String error next)"
    );
    assert_line(&evaluation(&run(&engine, &explicit)).exit, "one\n");
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn native_read_errors_use_checked_error_packets_and_ordinary_catch() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = engine.logical_root(&KVMap::new());
    let directory = directory("read-errors");
    let file = directory.join("existing.txt");
    std::fs::write(&file, b"kept\n").unwrap();
    let path = quoted(&file);
    let bad = format!("#eval do\n  let h ← IO.FS.Handle.mk {path} IO.FS.Mode.append\n  h.getLine");
    assert_error(
        &evaluation(&run(&engine, &bad)).exit,
        12,
        9,
        None,
        "Bad file descriptor",
    );
    let caught = format!(
        "#eval do\n  let bad ← IO.FS.Handle.mk {path} IO.FS.Mode.append\n  let good ← IO.FS.Handle.mk {path} IO.FS.Mode.read\n  try bad.getLine catch _ => good.getLine"
    );
    assert_line(&evaluation(&run(&engine, &caught)).exit, "kept\n");
    assert_eq!(std::fs::read(&file).unwrap(), b"kept\n");
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn read_resource_stops_are_inconclusive_and_cannot_be_caught_as_io_errors() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = engine.logical_root(&KVMap::new());
    let directory = directory("read-resource");
    let fallback = directory.join("fallback.txt");
    std::fs::write(&fallback, b"must not be returned\n").unwrap();
    for (label, byte, len) in [
        ("input", b'a', 16 * 1024 * 1024 + 1),
        ("output", 0xff, 6 * 1024 * 1024),
    ] {
        let file = directory.join(label);
        std::fs::write(&file, vec![byte; len]).unwrap();
        let source = format!(
            "#eval do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  let fallback ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  try h.getLine catch _ => fallback.getLine",
            quoted(&file),
            quoted(&fallback)
        );
        let outcome = engine
            .execute_source_commands_with_checks(
                source.as_bytes(),
                &KVMap::new(),
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .unwrap();
        assert!(
            matches!(outcome, Outcome::Inconclusive(_)),
            "{label} ceiling is a resource outcome"
        );
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
