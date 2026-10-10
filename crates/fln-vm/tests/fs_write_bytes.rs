//! Binary file effects through genuine census rows and canonical FLBC replay.
//! These runtime fixtures make no source or imported-module admission claim.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::outcome::Outcome;
use fln_rt::obj::{FileIoError, Obj};
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

const WRITE: &str = "extern:IO.FS.Handle.write";
static SERIAL: AtomicUsize = AtomicUsize::new(0);

fn path(label: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!(
        "fln-vm-write-bytes-{}-{nonce}-{}-{label}",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed)
    ))
}
fn r(index: u16) -> Register {
    Register::new(index)
}
fn f(index: u32) -> FunctionId {
    FunctionId::new(index)
}
fn call(dst: Register, row: &str, args: Vec<Register>) -> I {
    I::Intrinsic {
        dst,
        row: row.to_owned(),
        argument_ownership: vec![A::Borrowed; args.len()],
        args,
        result_ownership: R::Owned,
    }
}

fn body(path: &Path, mode: u64, bytes: &[u8], offset: u16) -> Vec<I> {
    let r = |index| Register::new(index + offset);
    let mut code = vec![
        I::String {
            dst: r(0),
            value: path.to_str().unwrap().to_owned(),
        },
        I::Nat {
            dst: r(1),
            value: mode,
        },
        call(r(2), "extern:IO.FS.Handle.mk", vec![r(0), r(1)]),
        I::CtorField {
            dst: r(3),
            src: r(2),
            expected_tag: 0,
            expected_fields: 7,
            field: 0,
        },
    ];
    let items = bytes
        .iter()
        .enumerate()
        .map(|(index, byte)| {
            let dst = r(16 + u16::try_from(index).unwrap());
            code.push(I::Nat {
                dst,
                value: u64::from(*byte),
            });
            dst
        })
        .collect();
    code.extend([
        I::Array { dst: r(4), items },
        I::Intrinsic {
            dst: r(5),
            row: "extern:ByteArray.mk".to_owned(),
            args: vec![r(4)],
            argument_ownership: vec![A::Owned],
            result_ownership: R::Owned,
        },
        call(r(6), WRITE, vec![r(3), r(5)]),
        I::Return { src: r(6) },
    ]);
    code
}

fn function(id: u32, arity: u16, code: Vec<I>) -> Function {
    Function {
        id: f(id),
        arity,
        parameter_ownership: vec![A::Borrowed; usize::from(arity)],
        result_ownership: C::Owned,
        register_count: 40,
        code,
    }
}
fn replay(functions: Vec<Function>) -> ValidatedProgram {
    let checked = flbc::validate(Program::new(f(0), functions)).unwrap();
    let bytes = flbc::encode_canonical(&checked, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        bytes,
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap()
    );
    decoded
}
fn returned(program: &ValidatedProgram) -> Obj {
    match execute(program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(value)) => value.value,
        other => panic!("expected completed binary file effect: {other:?}"),
    }
}
fn success(packet: &Obj) {
    assert_eq!(packet.header().tag, 0);
    assert_eq!(packet.header().other, 7);
    assert_eq!(packet.try_ctor_child(0).unwrap().unbox(), 0);
    assert_eq!(packet.try_ctor_child(1).unwrap().unbox(), 1);
}

#[test]
fn binary_write_row_replays_direct_apply_tail_and_deferred_actions() {
    let input = [0, 0xff, 0x80, b'\n', 0xe2, 0x82, b'Z'];
    for kind in 0..4 {
        let path = path("call-stages");
        let program = if kind == 0 {
            replay(vec![function(0, 0, body(&path, 1, &input, 0))])
        } else {
            let mut entry = vec![I::Closure {
                dst: r(0),
                function: f(1),
                captures: vec![],
                capture_ownership: vec![],
            }];
            if kind == 3 {
                entry.push(I::Return { src: r(0) });
            } else {
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
                            result_ownership: C::Owned,
                        },
                        I::Return { src: r(2) },
                    ]);
                } else {
                    entry.push(I::TailApply {
                        closure: r(0),
                        args: vec![r(1)],
                        argument_ownership: vec![A::Borrowed],
                        result_ownership: C::Owned,
                    });
                }
            }
            replay(vec![
                function(0, 0, entry),
                function(1, 1, body(&path, 1, &input, 1)),
            ])
        };
        let value = returned(&program);
        if kind == 3 {
            assert!(value.closure_shell_parts().is_some());
            assert!(
                !path.exists(),
                "constructing an action cannot open or write a file"
            );
        } else {
            success(&value);
            assert_eq!(std::fs::read(&path).unwrap(), input);
        }
    }
}

#[test]
fn binary_write_keeps_borrowed_buffer_aliases_and_prior_effects_after_later_refusal() {
    let input = [0, 0xff, b'X'];
    let path = path("reuse");
    let mut code = body(&path, 1, &input, 0);
    code.pop();
    code.extend([
        I::Copy {
            dst: r(7),
            src: r(5),
        },
        I::Drop { src: r(5) },
        call(r(6), WRITE, vec![r(3), r(7)]),
        I::Return { src: r(6) },
    ]);
    success(&returned(&replay(vec![function(0, 0, code.clone())])));
    assert_eq!(std::fs::read(&path).unwrap(), input.repeat(2));
    code.pop();
    code.extend([call(r(8), WRITE, vec![r(1), r(7)]), I::Return { src: r(8) }]);
    assert!(matches!(
        execute(
            &replay(vec![function(0, 0, code)]),
            ExecutionLimits::default(),
            None
        ),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::NativeFileIo {
                error: FileIoError::InvalidHandle
            },
            ..
        })
    ));
    assert_eq!(std::fs::read(&path).unwrap(), input.repeat(2));
}

#[test]
fn binary_write_empty_succeeds_and_read_only_failure_is_a_neutral_io_error() {
    let path = path("read-only");
    std::fs::write(&path, b"keep\0\xff").unwrap();
    success(&returned(&replay(vec![function(
        0,
        0,
        body(&path, 0, &[], 0),
    )])));
    let error = returned(&replay(vec![function(0, 0, body(&path, 0, &[0xff, 0], 0))]));
    assert_eq!(error.try_ctor_child(0).unwrap().unbox(), 0);
    assert_eq!(error.try_ctor_child(1).unwrap().unbox(), 0);
    assert_eq!(error.try_ctor_child(2).unwrap().unbox(), 12);
    assert_eq!(error.try_ctor_child(3).unwrap().unbox(), 9);
    assert_eq!(error.try_ctor_child(4).unwrap().unbox(), 0);
    assert_eq!(std::fs::read(&path).unwrap(), b"keep\0\xff");
}

#[test]
fn binary_write_rejects_wrong_values_and_calling_contracts_before_writing() {
    let path = path("bad-contracts");
    std::fs::write(&path, b"untouched").unwrap();
    for mutation in 0..7 {
        let mut code = body(&path, 3, &[0xff, 0], 0);
        let write = code
            .iter_mut()
            .find(|instruction| matches!(instruction, I::Intrinsic { row, .. } if row == WRITE))
            .unwrap();
        let I::Intrinsic {
            args,
            argument_ownership,
            result_ownership,
            ..
        } = write
        else {
            unreachable!()
        };
        match mutation {
            0 => args[1] = r(0),
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
        let result = execute(
            &replay(vec![function(0, 0, code)]),
            ExecutionLimits::default(),
            None,
        );
        match (mutation, result) {
            (
                0,
                Outcome::Complete(VmExit::Refused {
                    refusal:
                        VmRefusal::NativeFileIo {
                            error: FileIoError::InvalidByteArray,
                        },
                    ..
                }),
            ) => {}
            (
                1,
                Outcome::Complete(VmExit::Refused {
                    refusal:
                        VmRefusal::NativeFileIo {
                            error: FileIoError::InvalidHandle,
                        },
                    ..
                }),
            ) => {}
            (2..=6, Outcome::Complete(VmExit::Refused { .. })) => {}
            (_, other) => panic!("mutation {mutation} must refuse: {other:?}"),
        }
        assert_eq!(std::fs::read(&path).unwrap(), b"untouched");
    }
}
