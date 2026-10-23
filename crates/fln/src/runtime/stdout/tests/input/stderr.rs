//! Checked stderr actions over actual pinned IO declarations. These tests load
//! raw dependencies, not a fully admitted Init module, and require that fixture
//! when FLN_REQUIRE_REFERENCE is set. No Reference executable is invoked here.
use super::*;

fn source_fixture() -> Environment {
    let mut environment = source_environment().unwrap();
    let library = std::path::PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB").unwrap());
    for module in ["Init/Core", "Init/Data/String/Bootstrap"] {
        let path = library.join(module).with_extension("olean");
        let parts = [
            std::fs::read(&path).unwrap(),
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap(),
        ];
        let decoded = decode_olean_module_artifacts(
            &parts[0],
            &parts[1],
            &parts[2],
            OleanDecodeLimits::new(STACK),
        )
        .unwrap();
        let view = if decoded.module.is_module {
            fln_olean::region::OleanView::parse_with_dependencies(
                &parts[2],
                &[&parts[0], &parts[1]],
            )
        } else {
            fln_olean::region::OleanView::parse(&parts[0])
        }
        .unwrap();
        let blocks: Vec<_> = view
            .extension_payloads(OleanWalkBudget::default(), STACK)
            .unwrap()
            .into_iter()
            .filter(|block| block.name == name(metadata::EXTERN_EXTENSION))
            .collect();
        let metadata = metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap();
        for info in decoded.constants {
            if let Some(previous) = environment.find(info.name()) {
                assert_eq!(previous, &info);
            } else {
                environment = environment.add_decl(info).unwrap();
            }
        }
        for row in metadata
            .externs
            .into_iter()
            .filter(|row| row.declaration == name("String.push"))
        {
            let entries = row
                .entries
                .into_iter()
                .map(|entry| match entry {
                    metadata::ExternEntry::Standard { backend, symbol } => {
                        fln_elab::externs::ExternEntry::Standard { backend, symbol }
                    }
                    _ => panic!("actual String.push standard extern"),
                })
                .collect();
            environment =
                fln_elab::externs::register(&environment, &row.declaration, entries).unwrap();
        }
    }
    environment
}

#[test]
fn stderr_requires_independent_authority_even_after_a_warm_stream_layout() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let limits = IngressLimits::default();
    let stderr = stdout::Getter::Stderr;
    for first in [stdout::Getter::Stdin, stdout::Getter::Stdout] {
        let exact = register_getter(&raw, first, false);
        for second in [None, Some(true), Some(false)] {
            let environment = match second {
                None => exact.clone(),
                Some(foreign) => register_getter(&exact, stderr, foreign),
            };
            let mut preparation = Preparation::new(&environment, limits);
            assert!(
                preparation
                    .stdout_call(&Expr::const_(first.source_name(), vec![]), &[])
                    .unwrap()
                    .is_some()
            );
            let result = preparation.stdout_call(&c("IO.getStderr"), &[]);
            match second {
                None => assert!(result.unwrap().is_none()),
                Some(true) => assert!(result.is_err()),
                Some(false) => assert!(result.unwrap().is_some()),
            }
            // Display-equal names cannot borrow a warm binding's authority.
            let lookalike = Name::from_components(["IO.getStderr"]);
            assert_ne!(lookalike, stderr.source_name());
            assert!(
                preparation
                    .stdout_call(&Expr::const_(lookalike, vec![]), &[])
                    .unwrap()
                    .is_none()
            );
        }
    }
    let mut changed_count = 0;
    let changed = raw
        .constants()
        .fold(Environment::new(), |environment, (label, info)| {
            let mut info = info.clone();
            if label == &stderr.source_name() {
                let ConstantInfo::Opaque(value) = &mut info else {
                    panic!("pinned opaque getter")
                };
                value.value = c("Bool.false");
                changed_count += 1;
            }
            environment.add_decl(info).unwrap()
        });
    assert_eq!(changed_count, 1);
    assert!(
        stdout::getter_matches(
            &register_getter(&changed, stderr, false),
            stderr,
            &mut None,
            &mut 0,
            limits
        )
        .is_err()
    );
    let exact = register_getter(&raw, stderr, false);
    let mut work = 0;
    assert!(stdout::getter_matches(&exact, stderr, &mut None, &mut work, limits).unwrap());
    assert!(work > 0);
    assert!(matches!(
        stdout::getter_matches(
            &exact,
            stderr,
            &mut None,
            &mut 0,
            IngressLimits {
                max_nodes: work - 1,
                ..limits
            }
        ),
        Err(IngressError::ResourceLimit { .. })
    ));
}

#[test]
fn presented_evaluations_do_not_escape_their_command_streams() {
    if std::env::var_os("FLN_REFERENCE_LIB").is_none() {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
        return;
    }
    let environment = source_fixture();
    let environment = register_getter(
        &register_getter(&environment, stdout::Getter::Stdout, false),
        stdout::Getter::Stderr,
        false,
    );
    let engine = Engine::from_environment(environment);
    let root = engine.logical_root(&KVMap::new());
    let capture = StdoutCapture::begin(4096).unwrap();
    let result = engine
        .execute_source_commands_with_presentation(
            b"#eval IO.print \"first\"\n#eval IO.eprintln \"second\"\n#eval IO.print \"third\"",
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            crate::EvaluationPresentation::PreferRaw,
        )
        .unwrap()
        .into_complete()
        .expect("all three checked IO actions complete");
    assert_eq!(result.batch.executions.len(), 3);
    for execution in &result.batch.executions {
        assert_unit_packet(&execution.exit);
    }
    assert_eq!(
        result
            .batch
            .executions
            .iter()
            .map(|execution| execution.evaluation_output())
            .collect::<Vec<_>>(),
        [Some("first"), Some("second\n"), Some("third")]
    );
    let captured = capture.finish();
    assert_eq!(captured.error, None);
    assert!(
        captured.bytes.is_empty(),
        "evaluation output escaped its command: {:?}",
        captured.bytes
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn presented_output_exhaustion_is_typed_and_restores_the_enclosing_sink() {
    if std::env::var_os("FLN_REFERENCE_LIB").is_none() {
        assert!(std::env::var_os("FLN_REQUIRE_REFERENCE").is_none());
        eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
        return;
    }
    let raw = source_fixture();
    let environment = register_getter(
        &register_getter(&raw, stdout::Getter::Stdout, false),
        stdout::Getter::Stderr,
        false,
    );
    let engine = Engine::from_environment(environment);
    let root = engine.logical_root(&KVMap::new());
    let outer = StdoutCapture::begin(4096).unwrap();
    for (source, allowance, observed) in [
        ("#eval IO.print \"x\"", 0, 1),
        ("#eval IO.print \"abc\"\n#eval IO.eprint \"de\"", 4, 2),
    ] {
        let mut limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        limits.max_evaluation_output_bytes = allowance;
        let outcome = engine
            .execute_source_commands_with_presentation(
                source.as_bytes(),
                &KVMap::new(),
                limits,
                crate::EvaluationPresentation::PreferRaw,
            )
            .unwrap();
        let Outcome::Inconclusive(reason) = outcome else {
            panic!("output exhaustion must not become acceptance or rejection")
        };
        let fln_core::outcome::InconclusiveCause::ResourceExhausted { usage } = reason.cause else {
            panic!("output exhaustion must retain resource usage")
        };
        assert_eq!(usage.observed, observed);
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    let retry = engine
        .execute_source_commands_with_presentation(
            b"#eval IO.eprintln \"ok\"",
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            crate::EvaluationPresentation::PreferRaw,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(retry.batch.executions[0].evaluation_output(), Some("ok\n"));
    let result = outer.finish();
    assert_eq!(result.error, None);
    assert!(result.bytes.is_empty());
}

#[test]
fn checked_stderr_sources_are_deferred_separate_and_replayable() {
    const CHILD: &str = "FLN_STDERR_SOURCE_CHILD";
    const CASE: &str = "runtime::stdout::tests::input::stderr::checked_stderr_sources_are_deferred_separate_and_replayable";
    const MESSAGE: &str = "stderr-replay-λ🙂\0tail\n";
    if std::env::var(CHILD).as_deref() != Ok(CASE) {
        if std::env::var_os("FLN_REFERENCE_LIB").is_none() {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "the pinned Reference library is required"
            );
            eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
            return;
        }
        let output = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", CASE, "--nocapture", "--test-threads=1"])
            .env(CHILD, CASE)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let expected = format!(
            "{}stderr-line-☃\nstderr-callback\nstderr-callback\n",
            MESSAGE.repeat(3)
        );
        assert_eq!(output.stderr, expected.as_bytes());
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(!stdout.contains("stderr-replay"));
        assert!(!stdout.contains("stderr-deferred"));
        assert!(stdout.contains("1 passed; 0 failed; 0 ignored"));
        return;
    }
    let raw = source_fixture();
    let environment = register_getter(
        &register_getter(&raw, stdout::Getter::Stdout, false),
        stdout::Getter::Stderr,
        false,
    );
    let engine = Engine::from_environment(environment);
    let root = engine.logical_root(&KVMap::new());
    let capture = StdoutCapture::begin(1024).unwrap();
    let deferred = run(
        &engine,
        "def savedStderr : BaseIO IO.FS.Stream := IO.getStderr\ndef savedEprint : IO Unit := IO.eprint \"stderr-deferred\n\"",
    );
    for execution in &deferred.batch.executions {
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let VmExit::Returned(value) = &execution.exit else {
            panic!("deferred stderr action")
        };
        assert!(value.value.closure_shell_parts().is_some());
        assert!(execution.io_evaluation_outcome().unwrap().is_none());
    }
    let batch = run(&engine, "#eval IO.getStderr");
    let Some(IoEvaluationOutcome::Returned {
        exit: VmExit::Returned(stream),
        ..
    }) = evaluation(&batch).io_evaluation_outcome().unwrap()
    else {
        panic!("checked stderr getter result")
    };
    assert_constructor(&stream.value, 0, 6);
    for field in 0..6 {
        assert!(child(&stream.value, field).closure_shell_parts().is_some());
    }
    let batch = run(
        &engine,
        "#eval @IO.eprint String instToStringString \"stderr-replay-λ🙂\\x00tail\\n\"",
    );
    let execution = evaluation(&batch);
    assert_unit_packet(&execution.exit);
    let program =
        flbc::decode_canonical(&execution.flbc_artifact, flbc::CodecLimits::default()).unwrap();
    assert!(program.functions().iter().flat_map(|function| &function.code).any(|instruction|
        matches!(instruction, Instruction::Intrinsic { row, .. } if row == "extern:IO.getStderr")));
    for _ in 0..2 {
        assert_unit_packet(
            &execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
                .into_complete()
                .unwrap(),
        );
    }
    let batch = run(&engine, "#eval IO.eprintln \"stderr-line-☃\"");
    assert_unit_packet(&evaluation(&batch).exit);
    let batch = run(
        &deferred.batch.engine,
        "#eval (show IO Unit from do\n  let stderr ← savedStderr\n  let write := stderr.putStr\n  write \"stderr-callback\\n\"\n  write \"stderr-callback\\n\")",
    );
    assert_unit_packet(&evaluation(&batch).exit);
    let batch = run(&engine, "#eval IO.print \"stdout-only\"");
    assert_unit_packet(&evaluation(&batch).exit);
    let output = capture.finish();
    assert_eq!(output.bytes, b"stdout-only");
    assert_eq!(output.error, None);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
