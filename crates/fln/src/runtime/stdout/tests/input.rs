//! Actual pin models and source declaration checking; raw dependencies here
//! are deliberately not described as full Init.System.IO module admission.
//! The pin's #eval isolates stdin through withIsolatedStreams. The process
//! tests below exercise FrankenLean's explicit native IO entry and FLBC, not
//! that isolated evaluator's input behavior. Pin syntax/type evidence is in
//! validation/stdio-input-draft/oracle/run-0001/results.json: BaseIO-first
//! unannotated do is refused, while explicit IO result types are accepted.
use super::*;
use std::io::Write;
use std::process::{Command, Stdio};

fn register_getter(
    environment: &Environment,
    getter: stdout::Getter,
    foreign: bool,
) -> Environment {
    let source = getter.source_name();
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == source.to_display_string())
        .unwrap();
    fln_elab::externs::register(
        environment,
        &source,
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: if foreign {
                "foreign_stream_getter".into()
            } else {
                row.symbol.into()
            },
        }],
    )
    .unwrap()
}

fn source_environment() -> Option<Environment> {
    use fln_elab::instances::imported;
    let mut environment = raw_pin_environment()?;
    let library = std::path::PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB").unwrap());
    for module in ["Init/Prelude", "Init/System/IO"] {
        let path = library.join(module).with_extension("olean");
        let parts = [
            std::fs::read(&path).unwrap(),
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap(),
        ];
        let module_data = decode_olean_module_artifacts(
            &parts[0],
            &parts[1],
            &parts[2],
            OleanDecodeLimits::new(STACK),
        )
        .unwrap();
        let view = if module_data.module.is_module {
            fln_olean::region::OleanView::parse_with_dependencies(
                &parts[2],
                &[parts[0].as_slice(), parts[1].as_slice()],
            )
        } else {
            fln_olean::region::OleanView::parse(&parts[0])
        }
        .unwrap();
        let blocks = view
            .extension_payloads(OleanWalkBudget::default(), STACK)
            .unwrap();
        let decoded = metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap();
        let classes: &[&str] = if module == "Init/Prelude" {
            &[
                "Bind",
                "Monad",
                "MonadExceptOf",
                "MonadExcept",
                "MonadLift",
                "MonadLiftT",
            ]
        } else {
            &[]
        };
        let instances: &[&str] = if module == "Init/Prelude" {
            &[
                "Monad.toBind",
                "instMonadExceptOfMonadExceptOf",
                "instMonadLiftTOfMonadLift",
                "instMonadLiftT",
            ]
        } else {
            &[
                "instMonadEIO",
                "instMonadBaseIO",
                "instMonadExceptOfEIO",
                "instMonadLiftBaseIOEIO",
            ]
        };
        let classes: Vec<_> = classes.iter().map(|label| name(label)).collect();
        let instances: Vec<_> = instances.iter().map(|label| name(label)).collect();
        let mut activation = imported::ImportActivation::new(environment);
        let mut class_count = 0;
        for row in decoded
            .classes
            .into_iter()
            .filter(|row| classes.contains(&row.name))
        {
            activation = activation
                .register_class(
                    &row.name,
                    &imported::ClassParameters {
                        out_params: row.out_params,
                        out_level_params: row.out_level_params,
                    },
                )
                .unwrap();
            class_count += 1;
        }
        assert_eq!(class_count, classes.len());
        let mut instance_count = 0;
        for row in decoded
            .instances
            .into_iter()
            .filter(|row| instances.contains(&row.declaration))
        {
            assert!(
                matches!(row.value.node(), ExprNode::Const { name, .. } if name == &row.declaration)
            );
            activation = activation
                .register_instance(
                    &row.declaration,
                    &imported::InstanceParameters {
                        priority: row.priority,
                        synth_order: row.synth_order,
                        scope: row.scope,
                        keys: row.keys.into_iter().map(instance_key).collect(),
                    },
                )
                .unwrap();
            instance_count += 1;
        }
        assert_eq!(instance_count, instances.len());
        for row in decoded
            .reducibility
            .into_iter()
            .filter(|row| [name("outParam"), name("semiOutParam")].contains(&row.declaration))
        {
            assert_eq!(row.status, metadata::ReducibilityStatus::Reducible);
            activation = activation
                .register_reducibility(
                    &row.declaration,
                    fln_elab::reducibility::Reducibility::Reducible,
                )
                .unwrap();
        }
        environment = activation.finish().unwrap();
    }
    Some(environment)
}

fn evaluation(batch: &SourceCommandBatchExecution) -> &DefinitionExecution {
    for execution in &batch.batch.executions {
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
    }
    &batch.batch.executions[*batch.batch.source_evaluation_indices.last().unwrap()]
}
fn text(exit: &VmExit) -> String {
    let VmExit::Returned(value) = exit else {
        panic!("{exit:?}")
    };
    assert_constructor(&value.value, 0, 2);
    assert_eq!(child(&value.value, 1).unbox(), 0);
    let string = child(&value.value, 0);
    let (size, _, _, bytes) = string.try_string_view().unwrap();
    String::from_utf8(bytes[..size - 1].to_vec()).unwrap()
}
fn process(test: &str, input: &[u8]) -> bool {
    if std::env::var_os("FLN_STDIN_SOURCE_CHILD").is_some() {
        return true;
    }
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", test, "--nocapture", "--test-threads=1"])
        .env("FLN_STDIN_SOURCE_CHILD", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout)
            .contains("test result: ok. 1 passed; 0 failed; 0 ignored;")
    );
    false
}

#[test]
fn stdin_and_stdout_require_independent_exact_getters_even_with_warm_layout() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let limits = IngressLimits::default();
    for first in [stdout::Getter::Stdin, stdout::Getter::Stdout] {
        let second = if first == stdout::Getter::Stdin {
            stdout::Getter::Stdout
        } else {
            stdout::Getter::Stdin
        };
        let exact = register_getter(&raw, first, false);
        let mut preparation = Preparation::new(&exact, limits);
        assert!(
            preparation
                .stdout_call(&Expr::const_(first.source_name(), vec![]), &[])
                .unwrap()
                .is_some()
        );
        assert!(
            preparation
                .stdout_call(&Expr::const_(second.source_name(), vec![]), &[])
                .unwrap()
                .is_none()
        );
        let foreign = register_getter(&exact, second, true);
        let mut preparation = Preparation::new(&foreign, limits);
        assert!(
            preparation
                .stdout_call(&Expr::const_(first.source_name(), vec![]), &[])
                .unwrap()
                .is_some()
        );
        assert!(
            preparation
                .stdout_call(&Expr::const_(second.source_name(), vec![]), &[])
                .is_err()
        );
        let lookalike = Name::from_components([first.source_name().to_display_string().as_str()]);
        assert!(
            preparation
                .stdout_call(&Expr::const_(lookalike, vec![]), &[])
                .unwrap()
                .is_none()
        );
        for label in [
            "String",
            "String.ofByteArray",
            "ByteArray",
            "ByteArray.mk",
            "IO.getStdin",
        ] {
            let changed = raw.constants().fold(Environment::new(), |env, (n, info)| {
                let mut info = info.clone();
                if n == &name(label) {
                    match &mut info {
                        ConstantInfo::Induct(value) => value.num_params += 1,
                        ConstantInfo::Ctor(value) => value.num_fields += 1,
                        ConstantInfo::Opaque(value) => value.value = c("Bool.false"),
                        _ => unreachable!(),
                    }
                }
                env.add_decl(info).unwrap()
            });
            let getter = if label == "IO.getStdin" {
                stdout::Getter::Stdin
            } else {
                first
            };
            assert!(
                stdout::getter_matches(
                    &register_getter(&changed, getter, false),
                    getter,
                    &mut None,
                    &mut 0,
                    limits
                )
                .is_err(),
                "{label}"
            );
        }
    }
}

#[test]
fn ordinary_stdin_actions_share_cursor_defer_replay_and_echo_captured_bytes() {
    let Some(raw) = source_environment() else {
        return;
    };
    let test = "runtime::stdout::tests::input::ordinary_stdin_actions_share_cursor_defer_replay_and_echo_captured_bytes";
    if !process(
        test,
        "λ🙂\0first\r\nsecond\nreplay\necho\0λ\r\ntail\0🙂\r\n".as_bytes(),
    ) {
        return;
    }
    let environment = register_getter(
        &register_getter(&raw, stdout::Getter::Stdin, false),
        stdout::Getter::Stdout,
        false,
    );
    let engine = Engine::from_environment(environment);
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "#eval do\n  let stdin ← IO.getStdin\n  stdin.getLine",
        "#eval do\n  let stdin ← IO.getStdin\n  let line ← stdin.getLine\n  IO.print line",
    ] {
        // Match the pinned frontend: choosing BaseIO at the first action
        // cannot silently turn a later IO action into BaseIO. Refusal must
        // happen before native execution, leaving the piped cursor untouched.
        match engine.execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        ) {
            Err(EngineExecutionError::BatchCommand { error, .. }) => {
                assert!(matches!(*error, EngineExecutionError::Frontend(_)));
            }
            other => {
                panic!("unannotated BaseIO-first source must refuse during elaboration: {other:?}")
            }
        }
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    let deferred = run(
        &engine,
        "def savedRead : IO String := do\n  let stdin ← IO.getStdin\n  stdin.getLine\ndef savedStdin := IO.getStdin",
    );
    for execution in &deferred.batch.executions {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("deferred action")
        };
        assert!(value.value.closure_shell_parts().is_some());
        assert!(execution.io_evaluation_outcome().unwrap().is_none());
    }
    let source = "#eval (show IO String from do\n  let stdin ← savedStdin\n  let alias := stdin\n  let read := alias.getLine\n  let _ ← read\n  read)";
    let batch = run(&deferred.batch.engine, source);
    assert_eq!(text(&evaluation(&batch).exit), "second\n");
    let one = run(&deferred.batch.engine, "#eval savedRead");
    assert_eq!(text(&evaluation(&one).exit), "replay\n");
    let program = flbc::decode_canonical(
        &evaluation(&one).flbc_artifact,
        flbc::CodecLimits::default(),
    )
    .unwrap();
    let replay = execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
        .into_complete()
        .unwrap();
    assert_eq!(text(&replay), "echo\0λ\r\n");
    let capture = StdoutCapture::begin(1024).unwrap();
    let echo = run(
        &engine,
        "#eval (show IO Unit from do\n  let stdin ← IO.getStdin\n  let line ← stdin.getLine\n  IO.print line)",
    );
    assert_unit_packet(&evaluation(&echo).exit);
    let captured = capture.finish();
    assert_eq!(captured.bytes, "tail\0🙂\r\n".as_bytes());
    assert!(captured.error.is_none());
    for _ in 0..2 {
        assert_eq!(
            text(&evaluation(&run(&deferred.batch.engine, "#eval savedRead")).exit),
            ""
        );
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    if let Some(directory) = std::env::var_os("FLN_STDIO_INPUT_SOURCE_FIXTURE_DIR") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            directory.join("checked-echo.flbc"),
            &evaluation(&echo).flbc_artifact,
        )
        .unwrap();
        std::fs::write(
            directory.join("checked-read.flbc"),
            &evaluation(&one).flbc_artifact,
        )
        .unwrap();
    }
}

#[test]
fn stdout_get_line_reconstructs_real_error_and_catch_can_read_stdin() {
    let Some(raw) = source_environment() else {
        return;
    };
    let test = "runtime::stdout::tests::input::stdout_get_line_reconstructs_real_error_and_catch_can_read_stdin";
    if !process(test, b"recovered\n") {
        return;
    }
    let engine = Engine::from_environment(register_getter(
        &register_getter(&raw, stdout::Getter::Stdin, false),
        stdout::Getter::Stdout,
        false,
    ));
    let bad = run(
        &engine,
        "#eval (show IO String from do\n  let stdout ← IO.getStdout\n  stdout.getLine)",
    );
    let Some(IoEvaluationOutcome::Raised {
        exit: VmExit::Returned(error),
        ..
    }) = evaluation(&bad).io_evaluation_outcome().unwrap()
    else {
        panic!("stdout getLine must reconstruct a logical error")
    };
    assert_constructor(&error.value, 12, 3);
    let source = "#eval (show IO String from do\n  let stdout ← IO.getStdout\n  let stdin ← IO.getStdin\n  try stdout.getLine catch _ => stdin.getLine)";
    assert_eq!(text(&evaluation(&run(&engine, source)).exit), "recovered\n");
}
