//! Real validated FLBC effects under explicit per-thread stdout capture.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as R, CodecLimits, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership, ValidatedProgram,
};
use fln_core::outcome::Outcome;
use fln_rt::obj::{StdoutCapture, StdoutCaptureError};
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute};

fn r(n: u16) -> Register {
    Register::new(n)
}
fn f(n: u32) -> FunctionId {
    FunctionId::new(n)
}

fn fixture(text: &str, tail: bool, continuation: bool, wrong_world: bool) -> ValidatedProgram {
    let mut code = vec![
        I::Intrinsic {
            dst: r(0),
            row: "extern:IO.getStdout".to_owned(),
            args: Vec::new(),
            argument_ownership: Vec::new(),
            result_ownership: ResultOwnership::Owned,
        },
        I::CtorField {
            dst: r(1),
            src: r(0),
            expected_tag: 0,
            expected_fields: 6,
            field: 4,
        },
        I::String {
            dst: r(2),
            value: text.to_owned(),
        },
        I::Nat {
            dst: r(3),
            value: u64::from(wrong_world),
        },
    ];
    let (closure, args) = if continuation {
        code.push(I::Closure {
            dst: r(4),
            function: f(1),
            captures: Vec::new(),
            capture_ownership: Vec::new(),
        });
        (r(4), vec![r(1), r(2), r(3)])
    } else {
        (r(1), vec![r(2), r(3)])
    };
    let argument_ownership = vec![A::Borrowed; args.len()];
    if tail {
        code.push(I::TailApply {
            closure,
            args,
            argument_ownership,
            result_ownership: R::Owned,
        });
    } else {
        code.push(I::Apply {
            dst: r(5),
            closure,
            args,
            argument_ownership,
            result_ownership: R::Owned,
        });
        code.push(I::Return { src: r(5) });
    }
    let mut functions = vec![Function {
        id: f(0),
        arity: 0,
        parameter_ownership: Vec::new(),
        result_ownership: R::Owned,
        register_count: 6,
        code,
    }];
    if continuation {
        functions.push(Function {
            id: f(1),
            arity: 1,
            parameter_ownership: vec![A::Borrowed],
            result_ownership: R::Owned,
            register_count: 1,
            code: vec![I::Return { src: r(0) }],
        });
    }
    let program = flbc::validate(Program::new(f(0), functions)).unwrap();
    let bytes = flbc::encode_canonical(&program, CodecLimits::default()).unwrap();
    flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap()
}

fn scalar_fixture(first: &str, second: Option<(&str, u64)>) -> ValidatedProgram {
    let mut code = vec![
        I::Intrinsic {
            dst: r(0),
            row: "extern:IO.getStdout".to_owned(),
            args: Vec::new(),
            argument_ownership: Vec::new(),
            result_ownership: ResultOwnership::Owned,
        },
        I::CtorField {
            dst: r(1),
            src: r(0),
            expected_tag: 0,
            expected_fields: 6,
            field: 4,
        },
        I::String {
            dst: r(2),
            value: first.to_owned(),
        },
        I::Nat {
            dst: r(3),
            value: 0,
        },
        I::Apply {
            dst: r(4),
            closure: r(1),
            args: vec![r(2), r(3)],
            argument_ownership: vec![A::Borrowed; 2],
            result_ownership: R::Owned,
        },
    ];
    if let Some((text, world)) = second {
        code.extend([
            I::String {
                dst: r(5),
                value: text.to_owned(),
            },
            I::Nat {
                dst: r(6),
                value: world,
            },
            I::Apply {
                dst: r(7),
                closure: r(1),
                args: vec![r(5), r(6)],
                argument_ownership: vec![A::Borrowed; 2],
                result_ownership: R::Owned,
            },
        ]);
    }
    code.extend([
        I::Nat {
            dst: r(8),
            value: 42,
        },
        I::Return { src: r(8) },
    ]);
    flbc::validate(Program::new(
        f(0),
        vec![Function {
            id: f(0),
            arity: 0,
            parameter_ownership: Vec::new(),
            result_ownership: R::Scalar,
            register_count: 9,
            code,
        }],
    ))
    .unwrap()
}

/// Optional retained artifacts for the real CLI process gate. These are
/// validated runtime fixtures, never source declarations or module admission.
fn retain_cli_fixtures() {
    let Some(directory) = std::env::var_os("FLN_STDOUT_CAPTURE_FIXTURE_DIR") else {
        return;
    };
    let directory = std::path::PathBuf::from(directory);
    std::fs::create_dir_all(&directory).unwrap();
    let oversized = "\0".repeat(3 * 1024 * 1024);
    for (name, program) in [
        ("StdoutUnicode.flbc", scalar_fixture("native λ🙂\0\n", None)),
        (
            "StdoutThenRefusal.flbc",
            scalar_fixture("before\n", Some(("MUST NOT APPEAR", 1))),
        ),
        (
            "StdoutOverLimit.flbc",
            scalar_fixture("before\n", Some((&oversized, 0))),
        ),
    ] {
        let bytes = flbc::encode_canonical(&program, CodecLimits::default()).unwrap();
        let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
        assert_eq!(
            bytes,
            flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap()
        );
        let path = directory.join(name);
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .unwrap();
        std::io::Write::write_all(&mut file, &bytes).unwrap();
        eprintln!(
            "Retained validated runtime fixture (no source/module admission): {}",
            path.display()
        );
    }
}

#[test]
fn stdout_capture_executes_apply_tail_and_returned_native_continuations_once() {
    for tail in [false, true] {
        for continuation in [false, true] {
            let capture = StdoutCapture::begin(100).unwrap();
            let program = fixture("native λ🙂\0\n", tail, continuation, false);
            let result = execute(&program, ExecutionLimits::default(), None);
            assert!(
                matches!(result, Outcome::Complete(VmExit::Returned(_))),
                "{result:?}"
            );
            let output = capture.finish();
            assert_eq!(output.error, None);
            assert_eq!(output.bytes, "native λ🙂\0\n".as_bytes());
        }
    }
    let capture = StdoutCapture::begin(100).unwrap();
    let result = execute(
        &scalar_fixture("native λ🙂\0\n", None),
        ExecutionLimits::default(),
        None,
    );
    match result {
        Outcome::Complete(VmExit::Returned(value)) => assert_eq!(value.value.unbox(), 42),
        other => panic!("scalar fixture: {other:?}"),
    }
    assert_eq!(capture.finish().bytes, "native λ🙂\0\n".as_bytes());
    retain_cli_fixtures();
}

#[test]
fn stdout_capture_keeps_prior_writes_when_flbc_refuses_a_later_call() {
    let capture = StdoutCapture::begin(100).unwrap();
    assert!(matches!(
        execute(
            &fixture("before\n", false, false, false),
            ExecutionLimits::default(),
            None
        ),
        Outcome::Complete(VmExit::Returned(_))
    ));
    assert!(matches!(
        execute(
            &fixture("MUST NOT APPEAR", true, true, true),
            ExecutionLimits::default(),
            None
        ),
        Outcome::Complete(VmExit::Refused { .. })
    ));
    let output = capture.finish();
    assert_eq!(output.bytes, b"before\n");
    assert_eq!(output.error, None);
    let capture = StdoutCapture::begin(100).unwrap();
    let result = execute(
        &scalar_fixture("before\n", Some(("MUST NOT APPEAR", 1))),
        ExecutionLimits::default(),
        None,
    );
    assert!(matches!(result, Outcome::Complete(VmExit::Refused { .. })));
    assert_eq!(capture.finish().bytes, b"before\n");
}

#[test]
fn stdout_capture_budget_is_a_nonanswer_for_direct_and_continuation_paths() {
    for continuation in [false, true] {
        let capture = StdoutCapture::begin(7).unwrap();
        assert!(matches!(
            execute(
                &fixture("ok", false, continuation, false),
                ExecutionLimits::default(),
                None
            ),
            Outcome::Complete(VmExit::Returned(_))
        ));
        let result = execute(
            &fixture("\0", true, continuation, false),
            ExecutionLimits::default(),
            None,
        );
        assert!(matches!(result, Outcome::Inconclusive(_)), "{result:?}");
        let output = capture.finish();
        assert_eq!(output.bytes, b"ok");
        assert_eq!(
            output.error,
            Some(StdoutCaptureError::Limit {
                limit: 7,
                requested: 8
            })
        );
    }
}
