//! Real piped stdin through canonical runtime fixtures, not source admission.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, OwnershipLimits, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::outcome::Outcome;
use fln_rt::obj::{Obj, StdoutCapture};
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::io::Write;
use std::process::{Command, Stdio};

fn r(i: u16) -> Register {
    Register::new(i)
}
fn f(i: u32) -> FunctionId {
    FunctionId::new(i)
}
fn getter(dst: u16, stdin: bool) -> I {
    I::Intrinsic {
        dst: r(dst),
        row: if stdin {
            "extern:IO.getStdin"
        } else {
            "extern:IO.getStdout"
        }
        .into(),
        args: vec![],
        argument_ownership: vec![],
        result_ownership: R::Owned,
    }
}
fn field(dst: u16, src: u16, count: u16, index: u16) -> I {
    I::CtorField {
        dst: r(dst),
        src: r(src),
        expected_tag: 0,
        expected_fields: count,
        field: index,
    }
}
fn function(id: u32, arity: u16, registers: u16, code: Vec<I>) -> Function {
    Function {
        id: f(id),
        arity,
        parameter_ownership: vec![A::Borrowed; usize::from(arity)],
        result_ownership: C::Owned,
        register_count: registers,
        code,
    }
}
fn program(kind: usize, stdin: bool, world: u64, ownership: Vec<A>) -> ValidatedProgram {
    let mut code = vec![
        getter(0, stdin),
        field(1, 0, 6, 3),
        I::Nat {
            dst: r(2),
            value: world,
        },
    ];
    let mut others = vec![];
    match kind {
        0 | 4 => {
            code.push(I::Apply {
                dst: r(3),
                closure: r(1),
                args: vec![r(2)],
                argument_ownership: ownership,
                result_ownership: C::Owned,
            });
            if kind == 4 {
                code.extend([
                    field(4, 3, 7, 0),
                    getter(5, false),
                    field(6, 5, 6, 4),
                    I::Apply {
                        dst: r(7),
                        closure: r(6),
                        args: vec![r(4), r(2)],
                        argument_ownership: vec![A::Borrowed; 2],
                        result_ownership: C::Owned,
                    },
                    I::Return { src: r(4) },
                ]);
            } else {
                code.push(I::Return { src: r(3) });
            }
        }
        1 => code.push(I::TailApply {
            closure: r(1),
            args: vec![r(2)],
            argument_ownership: ownership,
            result_ownership: C::Owned,
        }),
        2 => {
            code.extend([
                I::Closure {
                    dst: r(3),
                    function: f(1),
                    captures: vec![],
                    capture_ownership: vec![],
                },
                I::Apply {
                    dst: r(4),
                    closure: r(3),
                    args: vec![r(1), r(2)],
                    argument_ownership: vec![A::Borrowed; 2],
                    result_ownership: C::Owned,
                },
                I::Return { src: r(4) },
            ]);
            others.push(function(1, 1, 1, vec![I::Return { src: r(0) }]));
        }
        3 => {
            code = vec![
                I::Closure {
                    dst: r(0),
                    function: f(1),
                    captures: vec![],
                    capture_ownership: vec![],
                },
                I::Return { src: r(0) },
            ];
            others.push(function(
                1,
                1,
                4,
                vec![
                    getter(1, stdin),
                    field(2, 1, 6, 3),
                    I::TailApply {
                        closure: r(2),
                        args: vec![r(0)],
                        argument_ownership: vec![A::Borrowed],
                        result_ownership: C::Owned,
                    },
                ],
            ));
        }
        _ => unreachable!(),
    }
    let mut functions = vec![function(0, 0, 8, code)];
    functions.extend(others);
    let raw = flbc::validate(Program::new(f(0), functions)).unwrap();
    let bytes = flbc::encode_canonical(&raw, CodecLimits::default()).unwrap();
    flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap()
}
fn owned(raw: &ValidatedProgram) -> ValidatedProgram {
    let candidate = flbc::insert_ownership(raw, OwnershipLimits::default()).unwrap();
    flbc::validate_ownership_candidate(
        raw,
        candidate.program().clone(),
        candidate.witness().clone(),
        OwnershipLimits::default(),
    )
    .unwrap();
    flbc::decode_canonical(
        &flbc::encode_canonical(candidate.program(), CodecLimits::default()).unwrap(),
        CodecLimits::default(),
    )
    .unwrap()
}
fn refused_interface(kind: usize, extra: bool, result: C, world: u64) -> ValidatedProgram {
    let raw = program(kind, true, world, vec![A::Borrowed]);
    let mut functions = raw.functions().to_vec();
    functions[0].result_ownership = result;
    let call = functions[0]
        .code
        .iter_mut()
        .find(|instruction| matches!(instruction, I::Apply { .. } | I::TailApply { .. }))
        .unwrap();
    match call {
        I::Apply {
            args,
            argument_ownership,
            result_ownership,
            ..
        }
        | I::TailApply {
            args,
            argument_ownership,
            result_ownership,
            ..
        } => {
            if extra {
                args.push(r(2));
                argument_ownership.push(A::Borrowed);
            }
            *result_ownership = result;
        }
        _ => unreachable!(),
    }
    flbc::validate(Program::new(f(0), functions)).unwrap()
}
fn returned(program: &ValidatedProgram) -> Obj {
    match execute(program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(value)) => value.value,
        other => panic!("{other:?}"),
    }
}
fn string(value: &Obj) -> String {
    let (size, _, _, bytes) = value.try_string_view().unwrap();
    String::from_utf8(bytes[..size - 1].to_vec()).unwrap()
}
fn line(value: &Obj) -> String {
    assert_eq!(value.header().tag, 0);
    assert_eq!(value.header().other, 7);
    assert_eq!(value.try_ctor_child(1).unwrap().unbox(), 1);
    string(&value.try_ctor_child(0).unwrap())
}
fn child(test: &str, case: &str, input: &[u8]) -> bool {
    if let Ok(active) = std::env::var("FLN_STDIN_VM_CASE") {
        return active == case;
    }
    let mut process = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", test, "--nocapture", "--test-threads=1"])
        .env("FLN_STDIN_VM_CASE", case)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    process.stdin.take().unwrap().write_all(input).unwrap();
    let output = process.wait_with_output().unwrap();
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
fn export(label: &str, program: &ValidatedProgram) {
    if let Some(directory) = std::env::var_os("FLN_STDIO_INPUT_FIXTURE_DIR") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            directory.join(format!("{label}.flbc")),
            flbc::encode_canonical(program, CodecLimits::default()).unwrap(),
        )
        .unwrap();
    }
}

#[test]
fn stdin_apply_tail_and_returned_continuations_share_real_piped_cursor() {
    let test = "stdin_apply_tail_and_returned_continuations_share_real_piped_cursor";
    for kind in 0..3 {
        let case = format!("cursor-{kind}");
        if !child(test, &case, "λ🙂\0first\r\nsecond\ntail".as_bytes()) {
            continue;
        }
        let raw = program(kind, true, 0, vec![A::Borrowed]);
        let inserted = owned(&raw);
        assert_eq!(line(&returned(&raw)), "λ🙂\0first\r\n");
        assert_eq!(line(&returned(&inserted)), "second\n");
        assert_eq!(line(&returned(&raw)), "tail");
        assert_eq!(line(&returned(&raw)), "");
        assert_eq!(line(&returned(&inserted)), "");
        export(&case, &raw);
        return;
    }
}

#[test]
fn stdin_refusals_and_deferred_actions_leave_input_for_the_next_real_read() {
    let test = "stdin_refusals_and_deferred_actions_leave_input_for_the_next_real_read";
    if !child(test, "refusal", b"unconsumed\n") {
        return;
    }
    assert!(
        returned(&program(3, true, 0, vec![]))
            .closure_shell_parts()
            .is_some()
    );
    for kind in 0..2 {
        for (world, ownership) in [(1, A::Borrowed), (0, A::Owned), (0, A::Scalar)] {
            assert!(matches!(
                execute(
                    &program(kind, true, world, vec![ownership]),
                    ExecutionLimits::default(),
                    None
                ),
                Outcome::Complete(VmExit::Refused { .. })
            ));
        }
    }
    for kind in 0..3 {
        for (extra, result, world) in [
            (true, C::Owned, 0),
            (false, C::Scalar, 0),
            (false, C::Erased, 0),
            (false, C::Owned, 1),
        ] {
            assert!(matches!(
                execute(
                    &refused_interface(kind, extra, result, world),
                    ExecutionLimits::default(),
                    None
                ),
                Outcome::Complete(VmExit::Refused { .. })
            ));
        }
    }
    let mut zero = program(0, true, 0, vec![A::Borrowed]).functions().to_vec();
    if let I::Apply {
        args,
        argument_ownership,
        ..
    } = &mut zero[0].code[3]
    {
        args.clear();
        argument_ownership.clear();
    } else {
        panic!("the direct call fixture");
    }
    assert!(
        flbc::validate(Program::new(f(0), zero)).is_err(),
        "zero-argument Apply is rejected before VM entry"
    );
    assert_eq!(
        line(&returned(&program(0, true, 0, vec![A::Borrowed]))),
        "unconsumed\n"
    );
    let stdout = returned(&program(0, false, 0, vec![A::Borrowed]));
    assert_eq!(stdout.try_ctor_child(1).unwrap().unbox(), 0);
    assert_eq!(stdout.try_ctor_child(2).unwrap().unbox(), 12);
    assert_eq!(stdout.try_ctor_child(3).unwrap().unbox(), 9);
    assert_eq!(stdout.try_ctor_child(0).unwrap().unbox(), 0);
    // A previously unsupported naked callback result cannot be relabeled as
    // the two-field logical EST.Out by an older stream wrapper. The actual
    // seven-field transport must pass through the new checked reconstruction.
    let mut old = program(0, false, 0, vec![A::Borrowed]).functions().to_vec();
    old[0].code.pop();
    old[0]
        .code
        .extend([field(4, 3, 2, 0), I::Return { src: r(4) }]);
    let old = flbc::validate(Program::new(f(0), old)).unwrap();
    assert!(matches!(
        execute(&old, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::ConstructorProjectionShape {
                expected_fields: 2,
                actual_fields: 7
            },
            ..
        })
    ));
}

#[test]
fn stdin_read_limits_are_inconclusive_on_every_native_continuation_route() {
    let test = "stdin_read_limits_are_inconclusive_on_every_native_continuation_route";
    for kind in 0..3 {
        for (label, byte, count) in [
            ("input", b'a', 16 * 1024 * 1024 + 1),
            ("output", 0xff, 6 * 1024 * 1024),
        ] {
            let case = format!("limit-{kind}-{label}");
            if !child(test, &case, &vec![byte; count]) {
                continue;
            }
            assert!(matches!(
                execute(
                    &program(kind, true, 0, vec![A::Borrowed]),
                    ExecutionLimits::default(),
                    None
                ),
                Outcome::Inconclusive(_)
            ));
            return;
        }
    }
}

#[test]
fn stdin_echo_retains_unicode_nul_and_json_capture_bytes() {
    let test = "stdin_echo_retains_unicode_nul_and_json_capture_bytes";
    let input = "λ🙂\0echo\r\n";
    if !child(test, "echo", input.as_bytes()) {
        return;
    }
    let program = owned(&program(4, true, 0, vec![A::Borrowed]));
    let capture = StdoutCapture::begin(1024).unwrap();
    assert_eq!(string(&returned(&program)), input);
    let capture = capture.finish();
    assert_eq!(capture.bytes, input.as_bytes());
    assert!(capture.error.is_none());
    export("echo", &program);
}
