//! Genuine census-row file effects through validated/replayed FLBC. These
//! runtime fixtures do not claim source or imported-module admission.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::outcome::Outcome;
use fln_rt::obj::{FileIoError, StdoutCapture};
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

static SERIAL: AtomicUsize = AtomicUsize::new(0);
fn path(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "fln-vm-file-{}-{}-{label}",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed)
    ))
}
fn r(n: u16) -> Register {
    Register::new(n)
}
fn f(n: u32) -> FunctionId {
    FunctionId::new(n)
}

fn call(dst: u16, row: &str, args: Vec<Register>) -> I {
    I::Intrinsic {
        dst: r(dst),
        row: row.to_owned(),
        argument_ownership: vec![A::Borrowed; args.len()],
        args,
        result_ownership: R::Owned,
    }
}

fn body(path: &str, mode: u64, text: &str, later_bad_handle: bool, return_packet: bool) -> Vec<I> {
    body_at(path, mode, text, later_bad_handle, return_packet, 0)
}

fn body_at(
    path: &str,
    mode: u64,
    text: &str,
    later_bad_handle: bool,
    return_packet: bool,
    offset: u16,
) -> Vec<I> {
    let r = |index| Register::new(index + offset);
    let call = |dst, row: &str, args| call(dst + offset, row, args);
    let mut code = vec![
        I::String {
            dst: r(0),
            value: path.to_owned(),
        },
        I::Nat {
            dst: r(1),
            value: mode,
        },
        call(2, "extern:IO.FS.Handle.mk", vec![r(0), r(1)]),
    ];
    if return_packet {
        code.push(I::Return { src: r(2) });
        return code;
    }
    code.extend([
        I::CtorField {
            dst: r(3),
            src: r(2),
            expected_tag: 0,
            expected_fields: 7,
            field: 0,
        },
        I::String {
            dst: r(4),
            value: text.to_owned(),
        },
        call(5, "extern:IO.FS.Handle.putStr", vec![r(3), r(4)]),
    ]);
    if later_bad_handle {
        code.push(I::Nat {
            dst: r(6),
            value: 0,
        });
        code.push(call(7, "extern:IO.FS.Handle.putStr", vec![r(6), r(4)]));
    }
    code.extend([
        I::Nat {
            dst: r(8),
            value: 42,
        },
        I::Return { src: r(8) },
    ]);
    code
}

fn program(code: Vec<I>, result: C) -> ValidatedProgram {
    replay(Program::new(
        f(0),
        vec![Function {
            id: f(0),
            arity: 0,
            parameter_ownership: vec![],
            result_ownership: result,
            register_count: 9,
            code,
        }],
    ))
}

fn replay(program: Program) -> ValidatedProgram {
    let checked = flbc::validate(program).unwrap();
    let bytes = flbc::encode_canonical(&checked, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        bytes,
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap()
    );
    decoded
}

fn returned(program: &ValidatedProgram) -> fln_vm::interpreter::CompletedExecution {
    match execute(program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(value)) => value,
        other => panic!("expected actual completed file execution: {other:?}"),
    }
}

#[test]
fn file_rows_execute_direct_apply_tail_and_deferred_actions_with_final_close() {
    let content = "λ🙂\0tail\n";
    for kind in 0..4 {
        let path = path("call-stages");
        let code = body(path.to_str().unwrap(), 1, content, false, false);
        let program = if kind == 0 {
            program(code, C::Scalar)
        } else {
            let entry_code = if kind == 3 {
                vec![
                    I::Closure {
                        dst: r(0),
                        function: f(1),
                        captures: vec![],
                        capture_ownership: vec![],
                    },
                    I::Return { src: r(0) },
                ]
            } else {
                let mut entry = vec![I::Closure {
                    dst: r(0),
                    function: f(1),
                    captures: vec![],
                    capture_ownership: vec![],
                }];
                entry.push(I::Nat {
                    dst: r(1),
                    value: 0,
                });
                if kind == 1 {
                    entry.extend([
                        I::Apply {
                            dst: r(2),
                            closure: r(0),
                            args: vec![r(1)],
                            argument_ownership: vec![A::Borrowed],
                            result_ownership: C::Scalar,
                        },
                        I::Return { src: r(2) },
                    ]);
                } else {
                    entry.push(I::TailApply {
                        closure: r(0),
                        args: vec![r(1)],
                        argument_ownership: vec![A::Borrowed],
                        result_ownership: C::Scalar,
                    });
                }
                entry
            };
            replay(Program::new(
                f(0),
                vec![
                    Function {
                        id: f(0),
                        arity: 0,
                        parameter_ownership: vec![],
                        result_ownership: if kind == 3 { C::Owned } else { C::Scalar },
                        register_count: 3,
                        code: entry_code,
                    },
                    Function {
                        id: f(1),
                        // One open world slot keeps the action deferred;
                        // locals start at1, retaining the parameter separately.
                        arity: 1,
                        parameter_ownership: vec![A::Borrowed],
                        result_ownership: C::Scalar,
                        register_count: 10,
                        code: body_at(path.to_str().unwrap(), 1, content, false, false, 1),
                    },
                ],
            ))
        };
        let value = returned(&program);
        if kind == 3 {
            assert!(!value.value.is_scalar());
            assert!(
                !path.exists(),
                "constructing a deferred action cannot open a file"
            );
        } else {
            assert_eq!(value.value.unbox(), 42);
            assert_eq!(std::fs::read(path).unwrap(), content.as_bytes());
        }
    }
    retain_fixtures();
}

#[test]
fn file_rows_keep_prior_writes_on_later_refusal_and_do_not_enter_stdout_capture() {
    let path = path("prefix");
    let capture = StdoutCapture::begin(1).unwrap();
    let program = program(
        body(path.to_str().unwrap(), 1, "prefix λ🙂\0", true, false),
        C::Scalar,
    );
    assert!(matches!(
        execute(&program, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::NativeFileIo {
                error: FileIoError::InvalidHandle
            },
            ..
        })
    ));
    assert_eq!(std::fs::read(path).unwrap(), "prefix λ🙂\0".as_bytes());
    let output = capture.finish();
    assert_eq!(output.error, None);
    assert!(output.bytes.is_empty());
}

#[test]
fn file_rows_validate_modes_arity_and_ownership_before_opening() {
    let path = path("unchanged");
    std::fs::write(&path, "untouched").unwrap();
    for mutation in 0..5 {
        let mut code = body(
            path.to_str().unwrap(),
            if mutation == 0 { 5 } else { 1 },
            "bad",
            false,
            false,
        );
        if let I::Intrinsic {
            args,
            argument_ownership,
            result_ownership,
            ..
        } = &mut code[2]
        {
            match mutation {
                1 => argument_ownership[0] = A::Owned,
                2 => *result_ownership = R::Scalar,
                3 => {
                    args.pop();
                    argument_ownership.pop();
                }
                4 => {
                    args.push(r(1));
                    argument_ownership.push(A::Borrowed);
                }
                _ => {}
            }
        }
        let program = program(code, C::Scalar);
        assert!(
            matches!(
                execute(&program, ExecutionLimits::default(), None),
                Outcome::Complete(VmExit::Refused { .. })
            ),
            "mutation {mutation}"
        );
        assert_eq!(std::fs::read(&path).unwrap(), b"untouched");
    }
}

#[test]
fn file_rows_return_native_errors_as_validated_neutral_data() {
    let missing = path("missing-parent").join("child");
    let result = returned(&program(
        body(missing.to_str().unwrap(), 0, "", false, true),
        C::Owned,
    ));
    assert_eq!(result.value.header().other, 7);
    assert_eq!(result.value.try_ctor_child(0).unwrap().unbox(), 0);
    assert_eq!(result.value.try_ctor_child(1).unwrap().unbox(), 0);
    assert_eq!(result.value.try_ctor_child(2).unwrap().unbox(), 11);
    assert_eq!(result.value.try_ctor_child(3).unwrap().unbox(), 2);
    assert_eq!(result.value.try_ctor_child(4).unwrap().unbox(), 1);
    let filename = result.value.try_ctor_child(5).unwrap();
    let (n, _, _, bytes) = filename.try_string_view().unwrap();
    assert_eq!(&bytes[..n - 1], missing.to_str().unwrap().as_bytes());
}

fn retain_fixtures() {
    let Some(directory) = std::env::var_os("FLN_FS_WRITE_FIXTURE_DIR") else {
        return;
    };
    let directory = PathBuf::from(directory);
    std::fs::create_dir_all(&directory).unwrap();
    let directory = directory.canonicalize().unwrap();
    for (name, mode, later_bad, content) in [
        ("FsWriteUnicode", 1, false, "λ🙂\0tail\n"),
        ("FsWriteThenRefusal", 1, true, "prefix\n"),
        ("FsWriteBadMode", 5, false, "MUST NOT WRITE"),
    ] {
        let output = directory.join(format!("{name}.output"));
        if mode == 5 {
            write_new(&output, b"untouched");
        }
        let fixture = program(
            body(output.to_str().unwrap(), mode, content, later_bad, false),
            C::Scalar,
        );
        let bytes = flbc::encode_canonical(&fixture, CodecLimits::default()).unwrap();
        write_new(&directory.join(format!("{name}.flbc")), &bytes);
    }
    write_new(&directory.join("PROVENANCE.txt"), b"Validated runtime FLBC fixtures for genuine Handle.mk/putStr rows. No source/module admission claim. FsWriteUnicode=>42 and exact UTF-8/NUL file bytes; FsWriteThenRefusal=>typed refusal with prefix file retained; FsWriteBadMode=>typed refusal and original file unchanged. All .output paths are inside this retained directory.\n");
}

fn write_new(path: &Path, bytes: &[u8]) {
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .unwrap();
    file.write_all(bytes).unwrap();
}
