//! Genuine counted-read rows over real files and canonical FLBC replay.
//! These runtime fixtures make no source or imported-module admission claim.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_rt::obj::{FileReadError, Obj};
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

const CEILING: usize = 64 * 1024;
static SERIAL: AtomicUsize = AtomicUsize::new(0);
fn path(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "fln-vm-read-bytes-{}-{}-{label}",
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
fn field(dst: u16, src: u16, index: u16) -> I {
    I::CtorField {
        dst: r(dst),
        src: r(src),
        expected_tag: 0,
        expected_fields: 7,
        field: index,
    }
}
fn replay(program: Program) -> ValidatedProgram {
    let validated = flbc::validate(program).unwrap();
    let encoded = flbc::encode_canonical(&validated, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&encoded, CodecLimits::default()).unwrap();
    assert_eq!(
        encoded,
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap()
    );
    decoded
}
fn entry(code: Vec<I>) -> Function {
    Function {
        id: f(0),
        arity: 0,
        parameter_ownership: vec![],
        result_ownership: C::Owned,
        register_count: 32,
        code,
    }
}
fn prelude(path: &Path, mode: u64, count: u64) -> Vec<I> {
    vec![
        I::String {
            dst: r(0),
            value: path.to_str().unwrap().to_owned(),
        },
        I::Nat {
            dst: r(1),
            value: mode,
        },
        call(2, "extern:IO.FS.Handle.mk", vec![r(0), r(1)]),
        field(3, 2, 0),
        I::Nat {
            dst: r(4),
            value: count,
        },
        I::Intrinsic {
            dst: r(5),
            row: "extern:USize.ofBitVec".to_owned(),
            args: vec![r(4)],
            argument_ownership: vec![A::Owned],
            result_ownership: R::Scalar,
        },
    ]
}
fn fixture(path: &Path, mode: u64, count: u64, kind: usize, packet: bool) -> Program {
    let mut code = prelude(path, mode, count);
    let mut extra = Vec::new();
    if kind == 0 {
        code.push(call(6, "extern:IO.FS.Handle.read", vec![r(3), r(5)]));
        if packet {
            code.push(I::Return { src: r(6) });
        } else {
            code.extend([field(7, 6, 0), I::Return { src: r(7) }]);
        }
    } else {
        code.extend([
            I::Closure {
                dst: r(6),
                function: f(1),
                captures: vec![r(3), r(5)],
                capture_ownership: vec![A::Borrowed; 2],
            },
            I::Nat {
                dst: r(7),
                value: 0,
            },
        ]);
        extra.push(Function {
            id: f(1),
            arity: 3,
            parameter_ownership: vec![A::Borrowed; 3],
            result_ownership: C::Owned,
            register_count: 5,
            code: vec![
                call(3, "extern:IO.FS.Handle.read", vec![r(0), r(1)]),
                field(4, 3, 0),
                I::Return { src: r(4) },
            ],
        });
        match kind {
            1 => code.extend([
                I::Apply {
                    dst: r(8),
                    closure: r(6),
                    args: vec![r(7)],
                    argument_ownership: vec![A::Borrowed],
                    result_ownership: C::Owned,
                },
                I::Return { src: r(8) },
            ]),
            2 => code.push(I::TailApply {
                closure: r(6),
                args: vec![r(7)],
                argument_ownership: vec![A::Borrowed],
                result_ownership: C::Owned,
            }),
            3 => {
                extra.push(Function {
                    id: f(2),
                    arity: 1,
                    parameter_ownership: vec![A::Borrowed],
                    result_ownership: C::Owned,
                    register_count: 1,
                    code: vec![I::Return { src: r(0) }],
                });
                code.extend([
                    I::Closure {
                        dst: r(9),
                        function: f(2),
                        captures: vec![],
                        capture_ownership: vec![],
                    },
                    I::Apply {
                        dst: r(8),
                        closure: r(9),
                        args: vec![r(6), r(7)],
                        argument_ownership: vec![A::Borrowed; 2],
                        result_ownership: C::Owned,
                    },
                    I::Return { src: r(8) },
                ]);
            }
            4 => code.push(I::Return { src: r(6) }),
            _ => unreachable!(),
        }
    }
    let mut functions = vec![entry(code)];
    functions.extend(extra);
    Program::new(f(0), functions)
}
fn returned(program: Program) -> Obj {
    match execute(&replay(program), ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(result)) => result.value,
        other => panic!("expected real binary read: {other:?}"),
    }
}
fn bytes(value: &Obj) -> Vec<u8> {
    let (width, size, capacity, bytes) = value.try_sarray_view().expect("native ByteArray");
    assert_eq!(width, 1);
    assert_eq!(size, bytes.len());
    assert!(size <= capacity);
    bytes
}

#[test]
fn counted_read_replays_direct_apply_tail_and_returned_continuations_and_defers_actions() {
    let path = path("calls");
    let input = [0, 0xff, 0x80, b'\n', 0xe2, 0x82, b'Z'];
    std::fs::write(&path, input).unwrap();
    for kind in 0..4 {
        assert_eq!(
            bytes(&returned(fixture(&path, 0, 4, kind, false))),
            input[..4]
        );
    }
    let closure = returned(fixture(&path, 0, 4, 4, false));
    let (_, captures) = closure.closure_shell_parts().unwrap();
    let handle = captures
        .iter()
        .find(|value| value.is_file_handle())
        .unwrap();
    let count = Obj::mk_ctor(0, vec![], &4usize.to_ne_bytes());
    let first = handle
        .try_file_read(&count, &Obj::mk_nat(0), CEILING)
        .unwrap();
    assert_eq!(
        bytes(&first.try_ctor_child(0).unwrap()),
        input[..4],
        "stored action leaves cursor untouched"
    );
    retain_fixtures();
}

#[test]
fn counted_read_reused_action_advances_one_shared_cursor_without_decoding_bytes() {
    let path = path("reuse");
    let input = [0, 0xff, 0x80, b'\n', 0xe2, 0x82, b'Z'];
    std::fs::write(&path, input).unwrap();
    let mut program = fixture(&path, 0, 3, 1, false);
    let code = &mut program.functions[0].code;
    code.pop();
    for dst in [10, 11, 12, 13] {
        code.push(I::Apply {
            dst: r(dst),
            closure: r(6),
            args: vec![r(7)],
            argument_ownership: vec![A::Borrowed],
            result_ownership: C::Owned,
        });
    }
    code.extend([
        I::Ctor {
            dst: r(14),
            tag: 0,
            fields: vec![r(8), r(10), r(11), r(12), r(13)],
            scalar_bytes: vec![],
        },
        I::Return { src: r(14) },
    ]);
    let result = returned(program);
    for (index, expected) in [&input[..3], &input[3..6], &input[6..], &[][..], &[][..]]
        .into_iter()
        .enumerate()
    {
        assert_eq!(bytes(&result.try_ctor_child(index).unwrap()), expected);
    }
}

#[test]
fn counted_read_zero_and_short_read_succeed_and_write_only_error_is_not_a_resource() {
    let path = path("short-and-error");
    std::fs::write(&path, b"raw\0\xff").unwrap();
    assert_eq!(
        bytes(&returned(fixture(&path, 0, 9, 0, false))),
        b"raw\0\xff"
    );
    assert_eq!(bytes(&returned(fixture(&path, 4, 0, 0, false))), []);
    let packet = returned(fixture(&path, 4, 1, 0, true));
    assert_eq!(packet.try_ctor_child(0).unwrap().unbox(), 0);
    assert_eq!(packet.try_ctor_child(1).unwrap().unbox(), 0);
    assert_eq!(packet.try_ctor_child(2).unwrap().unbox(), 12);
    assert_eq!(packet.try_ctor_child(3).unwrap().unbox(), 9);
    assert_eq!(packet.try_ctor_child(4).unwrap().unbox(), 0);
    assert_eq!(std::fs::read(&path).unwrap(), b"raw\0\xff");
}

#[test]
fn counted_read_request_ceiling_is_pre_effect_inconclusive_in_every_callable_route() {
    let path = path("limit");
    std::fs::write(&path, [0xff; CEILING]).unwrap();
    assert_eq!(
        bytes(&returned(fixture(&path, 0, CEILING as u64, 0, false))).len(),
        CEILING
    );
    for kind in 0..4 {
        let program = replay(fixture(&path, 0, CEILING as u64 + 1, kind, false));
        let result = execute(&program, ExecutionLimits::default(), None);
        let Outcome::Inconclusive(limit) = result else {
            panic!("resource is a nonanswer: {result:?}")
        };
        match limit.cause {
            InconclusiveCause::ResourceExhausted { usage } => {
                assert_eq!(
                    usage.reason,
                    ResourceReason::Memory {
                        limit_bytes: CEILING as u64
                    }
                );
                assert_eq!(usage.allowed, CEILING as u64);
                assert_eq!(usage.observed, CEILING as u64 + 1);
            }
            other => panic!("expected counted read resource: {other:?}"),
        }
        assert!(format!("{:?}", limit.progress).contains("consuming 0 file bytes"));
    }
}

#[test]
fn counted_read_refuses_nat_counts_bad_handles_and_wrong_row_calling_contracts() {
    let path = path("bad-contracts");
    std::fs::write(&path, b"keep").unwrap();
    for mutation in 0..7 {
        let mut program = fixture(&path, 0, 1, 0, true);
        let I::Intrinsic {
            args,
            argument_ownership,
            result_ownership,
            ..
        } = &mut program.functions[0].code[6]
        else {
            panic!("read site")
        };
        match mutation {
            0 => args[1] = r(1), // A tagged Nat is not a boxed USize.
            1 => args[0] = r(1),
            2 => argument_ownership[0] = A::Owned,
            3 => argument_ownership[1] = A::Owned,
            4 => *result_ownership = R::Scalar,
            5 => {
                args.pop();
                argument_ownership.pop();
            }
            6 => {
                args.push(r(1));
                argument_ownership.push(A::Borrowed);
            }
            _ => unreachable!(),
        }
        let result = execute(&replay(program), ExecutionLimits::default(), None);
        match (mutation, result) {
            (
                0,
                Outcome::Complete(VmExit::Refused {
                    refusal:
                        VmRefusal::NativeFileRead {
                            error: FileReadError::InvalidCount,
                        },
                    ..
                }),
            ) => {}
            (
                1,
                Outcome::Complete(VmExit::Refused {
                    refusal:
                        VmRefusal::NativeFileRead {
                            error: FileReadError::InvalidHandle,
                        },
                    ..
                }),
            ) => {}
            (2..=6, Outcome::Complete(VmExit::Refused { .. })) => {}
            (_, other) => panic!("mutation {mutation} must refuse: {other:?}"),
        }
    }
}

fn retain_fixtures() {
    let Some(directory) = std::env::var_os("FLN_FS_READ_BYTES_FIXTURE_DIR") else {
        return;
    };
    let directory = PathBuf::from(directory);
    std::fs::create_dir_all(&directory).unwrap();
    let directory = directory.canonicalize().unwrap();
    for (name, mode, count, error) in [
        ("FsReadBytesRaw", 0, 4, false),
        ("FsReadBytesShort", 0, 100, false),
        ("FsReadBytesZero", 4, 0, false),
        ("FsReadBytesError", 4, 1, true),
        ("FsReadBytesLimit", 0, CEILING as u64 + 1, false),
    ] {
        let input = directory.join(format!("{name}.input"));
        write_new(&input, &[0, 0xff, 0x80, b'\n', 0xe2, 0x82, b'Z']);
        let mut program = fixture(&input, mode, count, 0, error);
        program.functions[0].result_ownership = C::Scalar;
        let code = &mut program.functions[0].code;
        code.pop();
        if error {
            code.push(field(31, 6, 2));
        } else {
            code.push(call(31, "extern:ByteArray.size", vec![r(7)]));
        }
        code.push(I::Return { src: r(31) });
        let encoded = flbc::encode_canonical(&replay(program), CodecLimits::default()).unwrap();
        write_new(&directory.join(format!("{name}.flbc")), &encoded);
    }
    write_new(&directory.join("PROVENANCE.txt"), b"Genuine Handle.mk/read/USize.ofBitVec/ByteArray.size runtime rows with canonical FLBC replay. No source or module admission claim. Raw=>4, short=>7, zero/write-only=>0, write-only read=>IO.Error tag12. Limit=>Inconclusive before fread at65536-byte request ceiling. Exact raw bytes and all input files retained.\n");
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
