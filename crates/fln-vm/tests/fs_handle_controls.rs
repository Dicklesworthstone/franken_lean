//! Handle controls retain native effects and refusal boundaries through FLBC.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_rt::obj::{FileIoError, Obj};
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

static SERIAL: AtomicUsize = AtomicUsize::new(0);
const REWIND: &str = "extern:IO.FS.Handle.rewind";
const TRUNCATE: &str = "extern:IO.FS.Handle.truncate";
const LOCK: &str = "extern:IO.FS.Handle.lock";
const TRY_LOCK: &str = "extern:IO.FS.Handle.tryLock";
const UNLOCK: &str = "extern:IO.FS.Handle.unlock";
const CONTROLS: [&str; 5] = [REWIND, TRUNCATE, LOCK, TRY_LOCK, UNLOCK];

fn path(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "fln-vm-handle-{}-{}-{label}",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed)
    ))
}

fn r(index: u16) -> Register {
    Register::new(index)
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

fn program(row: &str, path: Option<&Path>, exclusive: u64) -> Program {
    let mut code = if let Some(path) = path {
        vec![
            I::String {
                dst: r(0),
                value: path.to_str().unwrap().to_owned(),
            },
            I::Nat {
                dst: r(1),
                value: 3,
            },
            call(2, "extern:IO.FS.Handle.mk", vec![r(0), r(1)]),
            I::CtorField {
                dst: r(3),
                src: r(2),
                expected_tag: 0,
                expected_fields: 7,
                field: 0,
            },
        ]
    } else {
        vec![I::Nat {
            dst: r(3),
            value: 0,
        }]
    };
    code.push(I::Nat {
        dst: r(4),
        value: exclusive,
    });
    let args = if matches!(row, LOCK | TRY_LOCK) {
        vec![r(3), r(4)]
    } else {
        vec![r(3)]
    };
    code.extend([call(5, row, args), I::Return { src: r(5) }]);
    Program::new(
        FunctionId::new(0),
        vec![Function {
            id: FunctionId::new(0),
            arity: 0,
            parameter_ownership: vec![],
            result_ownership: C::Owned,
            register_count: 6,
            code,
        }],
    )
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

fn payload(program: &ValidatedProgram) -> Obj {
    let result = execute(program, ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(returned)) = result else {
        panic!("Handle control: {result:?}")
    };
    let packet = returned.value;
    assert_eq!(packet.header().other, 7);
    assert_eq!(packet.try_ctor_child(1).unwrap().unbox(), 1);
    packet.try_ctor_child(0).unwrap()
}

#[test]
fn handle_control_rows_replay_cursor_and_lock_effects() {
    let file = path("live");
    std::fs::write(&file, "preserved").unwrap();
    for row in [REWIND, LOCK, UNLOCK] {
        assert_eq!(payload(&replay(program(row, Some(&file), 1))).unbox(), 0);
        assert_eq!(std::fs::read(&file).unwrap(), b"preserved");
    }
    let try_lock = replay(program(TRY_LOCK, Some(&file), 1));
    assert_eq!(payload(&try_lock).unbox(), 1);
    let competing = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(&file)
        .unwrap();
    competing.lock().unwrap();
    assert_eq!(payload(&try_lock).unbox(), 0);
    competing.unlock().unwrap();
    assert_eq!(payload(&try_lock).unbox(), 1);
    assert_eq!(
        payload(&replay(program(TRUNCATE, Some(&file), 1))).unbox(),
        0
    );
    assert!(std::fs::read(&file).unwrap().is_empty());
}

#[test]
fn handle_controls_refuse_invalid_handles_booleans_and_ownership_before_effects() {
    let file = path("refusals");
    std::fs::write(&file, "preserved").unwrap();
    for row in CONTROLS {
        assert!(matches!(
            execute(
                &replay(program(row, None, 1)),
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
        for mutation in 0..3 {
            let mut bad = program(row, Some(&file), 1);
            let call_index = bad.functions[0].code.len() - 2;
            let I::Intrinsic {
                args,
                argument_ownership,
                result_ownership,
                ..
            } = &mut bad.functions[0].code[call_index]
            else {
                unreachable!()
            };
            match mutation {
                0 => argument_ownership[0] = A::Owned,
                1 => *result_ownership = R::Scalar,
                _ => {
                    args.clear();
                    argument_ownership.clear();
                }
            }
            assert!(matches!(
                execute(&replay(bad), ExecutionLimits::default(), None),
                Outcome::Complete(VmExit::Refused { .. })
            ));
        }
    }
    for row in [LOCK, TRY_LOCK] {
        assert!(matches!(
            execute(
                &replay(program(row, Some(&file), 2)),
                ExecutionLimits::default(),
                None
            ),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::InvalidBoolScalar {
                    argument: 1,
                    value: 2,
                    ..
                },
                ..
            })
        ));
    }
    assert_eq!(std::fs::read(file).unwrap(), b"preserved");
}

#[test]
fn handle_controls_stop_before_effects_and_recover_on_fresh_execution() {
    let file = path("limits");
    std::fs::write(&file, "preserved").unwrap();
    for row in CONTROLS {
        let program = replay(program(row, Some(&file), 1));
        assert!(matches!(
            execute(
                &program,
                ExecutionLimits {
                    max_steps: 1,
                    ..ExecutionLimits::default()
                },
                None
            ),
            Outcome::Inconclusive(_)
        ));
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), Some(&|| true)),
            Outcome::Inconclusive(stop) if matches!(stop.cause, InconclusiveCause::Cancelled { .. })
        ));
        assert_eq!(std::fs::read(&file).unwrap(), b"preserved");
    }
    assert_eq!(
        payload(&replay(program(TRUNCATE, Some(&file), 1))).unbox(),
        0
    );
    assert!(std::fs::read(file).unwrap().is_empty());
}
