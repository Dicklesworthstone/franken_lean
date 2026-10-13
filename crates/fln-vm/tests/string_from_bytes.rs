//! Checked byte-array conversion through generated extern dispatch and canonical FLBC replay.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership, CallableResultOwnership, CodecLimits, Function, FunctionId,
    Instruction, Program, Register, ResultOwnership, ValidatedProgram, encode_canonical,
};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{Authority, InconclusiveCause, Outcome};
use fln_rt::obj::{Obj, shadow};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::sync::Mutex;

const ROW: &str = "extern:String.ofByteArray";
static TEST_LOCK: Mutex<()> = Mutex::new(());

fn r(index: u16) -> Register {
    Register::new(index)
}

fn call(arguments: &[u16]) -> Instruction {
    Instruction::Intrinsic {
        dst: r(3),
        row: ROW.to_owned(),
        args: arguments.iter().copied().map(r).collect(),
        argument_ownership: vec![ArgumentOwnership::Borrowed; arguments.len()],
        result_ownership: ResultOwnership::Owned,
    }
}

fn input(bytes: &[u8]) -> Vec<Instruction> {
    let mut code = Vec::new();
    let items = bytes
        .iter()
        .enumerate()
        .map(|(index, byte)| {
            let dst = r(16 + u16::try_from(index).unwrap());
            code.push(Instruction::Nat {
                dst,
                value: u64::from(*byte),
            });
            dst
        })
        .collect();
    code.extend([
        Instruction::Array { dst: r(0), items },
        Instruction::Intrinsic {
            dst: r(1),
            row: "extern:ByteArray.mk".to_owned(),
            args: vec![r(0)],
            argument_ownership: vec![ArgumentOwnership::Owned],
            result_ownership: ResultOwnership::Owned,
        },
    ]);
    code
}

fn replay(code: Vec<Instruction>) -> ValidatedProgram {
    let validated = flbc::validate(Program::new(
        FunctionId::new(0),
        vec![Function {
            id: FunctionId::new(0),
            arity: 0,
            parameter_ownership: vec![],
            result_ownership: CallableResultOwnership::Erased,
            register_count: 64,
            code,
        }],
    ))
    .unwrap();
    let bytes = encode_canonical(&validated, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        bytes,
        encode_canonical(&decoded, CodecLimits::default()).unwrap()
    );
    decoded
}

fn returned(program: &ValidatedProgram) -> Obj {
    match execute(program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(value)) => value.value,
        other => panic!("native String conversion did not return: {other:?}"),
    }
}

fn assert_text(value: &Obj, expected: &str) {
    let (size, capacity, characters, bytes) = value
        .try_borrow_string_view()
        .expect("canonical native String");
    assert_eq!(size, expected.len() + 1);
    assert!(capacity >= size);
    assert_eq!(characters, expected.chars().count());
    assert_eq!(&bytes[..size - 1], expected.as_bytes());
    assert_eq!(bytes[size - 1], 0);
}

fn assert_clean_shadow() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "conversion success and refusal retain no ABI objects"
    );
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
    )));
}

#[test]
fn byte_array_string_conversion_replays_unicode_nul_empty_and_input_aliases() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for text in ["", "a\0z", "héllo∀🦀", "\0é\0🦀\0", "e\u{301}"] {
        let mut code = input(text.as_bytes());
        code.extend([
            Instruction::Copy {
                dst: r(2),
                src: r(1),
            },
            call(&[1]),
            Instruction::Copy {
                dst: r(4),
                src: r(3),
            },
            call(&[2]),
            Instruction::Array {
                dst: r(5),
                items: vec![r(1), r(2), r(3), r(4)],
            },
            Instruction::Return { src: r(5) },
        ]);
        let program = replay(code);
        for _ in 0..2 {
            let result = returned(&program);
            let first = result.array_child(0);
            let alias = result.array_child(1);
            assert_eq!(first.identity_token(), alias.identity_token());
            assert_eq!(first.try_borrow_sarray_view().unwrap().3, text.as_bytes());
            let second_string = result.array_child(2);
            let first_string = result.array_child(3);
            assert_text(&first_string, text);
            assert_text(&second_string, text);
            assert_ne!(
                first_string.identity_token(),
                second_string.identity_token()
            );
            assert_ne!(first.identity_token(), first_string.identity_token());
        }
    }
    assert_clean_shadow();
}

#[test]
fn byte_array_string_conversion_refuses_invalid_utf8_without_recovery() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for bytes in [
        &b"\xff"[..],
        &b"\x80"[..],
        &b"\xc0\xaf"[..],
        &b"\xe0\x80\x80"[..],
        &b"\xed\xa0\x80"[..],
        &b"\xf4\x90\x80\x80"[..],
        &b"\xe2\x82"[..],
        &b"x\0\xffz"[..],
    ] {
        let mut code = input(bytes);
        code.extend([call(&[1]), Instruction::Return { src: r(3) }]);
        let program = replay(code);
        for _ in 0..2 {
            assert!(matches!(
                execute(&program, ExecutionLimits::default(), None),
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::InvalidStringObject,
                    ..
                })
            ));
        }
    }
    assert_clean_shadow();
}

#[test]
fn byte_array_string_conversion_enforces_erased_arity_and_generated_ownership() {
    let _guard = TEST_LOCK.lock().unwrap();
    let generated = EXTERN_ROWS.iter().find(|row| row.id == ROW).unwrap();
    assert_eq!(
        (generated.kind, generated.module, generated.arity),
        ("ctor", "Init.Prelude", 2)
    );
    assert_eq!(generated.symbol, "lean_string_from_utf8_unchecked");
    for arguments in [vec![], vec![1, 1]] {
        let mut code = input(b"ok");
        code.extend([call(&arguments), Instruction::Return { src: r(3) }]);
        assert!(
            matches!(execute(&replay(code), ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused { refusal: VmRefusal::IntrinsicArity { row, expected: 1, actual }, .. })
                if row == ROW && actual == arguments.len())
        );
    }
    for ownership in [
        ArgumentOwnership::Owned,
        ArgumentOwnership::Unique,
        ArgumentOwnership::Scalar,
    ] {
        let mut code = input(b"ok");
        let mut operation = call(&[1]);
        if let Instruction::Intrinsic {
            argument_ownership, ..
        } = &mut operation
        {
            *argument_ownership = vec![ownership];
        }
        code.extend([operation, Instruction::Return { src: r(3) }]);
        assert!(
            matches!(execute(&replay(code), ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused { refusal: VmRefusal::IntrinsicOwnershipMismatch {
                expected: ArgumentOwnership::Borrowed, actual, .. }, .. }) if actual == ownership)
        );
    }
    for ownership in [
        ResultOwnership::Borrowed,
        ResultOwnership::Scalar,
        ResultOwnership::RawObject,
    ] {
        let mut code = input(b"ok");
        let mut operation = call(&[1]);
        if let Instruction::Intrinsic {
            result_ownership, ..
        } = &mut operation
        {
            *result_ownership = ownership;
        }
        code.extend([operation, Instruction::Return { src: r(3) }]);
        assert!(
            matches!(execute(&replay(code), ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused { refusal: VmRefusal::IntrinsicResultOwnershipMismatch {
                expected: ResultOwnership::Owned, actual, .. }, .. }) if actual == ownership)
        );
    }
}

#[test]
fn byte_array_string_conversion_budget_stops_publish_nothing_and_replay() {
    let _guard = TEST_LOCK.lock().unwrap();
    let text = "é\0";
    let mut code = input(text.as_bytes());
    code.extend([call(&[1]), Instruction::Return { src: r(3) }]);
    let program = replay(code);
    shadow::enable();
    for max_steps in [text.len() as u64 + 2, text.len() as u64 + 3] {
        let outcome = execute(
            &program,
            ExecutionLimits {
                max_steps,
                ..ExecutionLimits::default()
            },
            None,
        );
        assert_eq!(outcome.authority(), Authority::NonAuthoritative);
        assert!(matches!(outcome, Outcome::Inconclusive(inconclusive)
            if matches!(&inconclusive.cause, InconclusiveCause::ResourceExhausted { usage }
                if usage.reason == ResourceReason::ExecutionSteps
                    && usage.allowed == max_steps && usage.observed == max_steps + 1)));
    }
    assert_text(&returned(&program), text);
    assert_clean_shadow();
}
