//! The pinned bootstrap string helpers execute through real extern dispatch
//! and canonical FLBC decoding. Source record adapters are tested by `fln`.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{Authority, InconclusiveCause, Outcome};
use fln_rt::obj::{Obj, shadow};
use fln_vm::interpreter::{ExecutionLimits, ValueKind, VmExit, VmRefusal, execute};
use std::cell::Cell;
use std::sync::{Mutex, MutexGuard};

const POS_OF: &str = "extern:String.Internal.posOf";
const OFFSET_OF_POS: &str = "extern:String.Internal.offsetOfPos";
const PUSHN: &str = "extern:String.Internal.pushn";
const OUTPUT_LIMIT: u64 = 16 * 1024 * 1024;
static TEST_LOCK: Mutex<()> = Mutex::new(());

fn lock() -> MutexGuard<'static, ()> {
    TEST_LOCK.lock().unwrap_or_else(|error| error.into_inner())
}

fn r(index: u16) -> Register {
    Register::new(index)
}

fn nat(dst: u16, value: u64) -> I {
    I::Nat { dst: r(dst), value }
}

fn string(dst: u16, value: &str) -> I {
    I::String {
        dst: r(dst),
        value: value.to_owned(),
    }
}

fn call(dst: u16, row: &str, args: &[u16]) -> I {
    I::Intrinsic {
        dst: r(dst),
        row: row.to_owned(),
        args: args.iter().copied().map(r).collect(),
        argument_ownership: vec![A::Borrowed; args.len()],
        result_ownership: R::Owned,
    }
}

fn replay(code: Vec<I>) -> ValidatedProgram {
    let program = Program::new(
        FunctionId::new(0),
        vec![Function {
            id: FunctionId::new(0),
            arity: 0,
            parameter_ownership: Vec::new(),
            result_ownership: C::Erased,
            register_count: 32,
            code,
        }],
    );
    let validated = flbc::validate(program).unwrap();
    let bytes = flbc::encode_canonical(&validated, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap(),
        bytes
    );
    decoded
}

fn fixture(row: &str, source: I, operands: Vec<I>) -> ValidatedProgram {
    let count = u16::try_from(operands.len()).unwrap();
    let mut code = vec![source];
    code.extend(operands);
    code.push(call(8, row, &(0..=count).collect::<Vec<_>>()));
    code.push(I::Return { src: r(8) });
    replay(code)
}

fn invoke(row: &str, source: &str, operands: &[u64]) -> Obj {
    let operands = operands
        .iter()
        .enumerate()
        .map(|(index, value)| nat(index as u16 + 1, *value))
        .collect();
    returned(&fixture(row, string(0, source), operands))
}

fn returned(program: &ValidatedProgram) -> Obj {
    match execute(program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(result)) => result.value,
        other => panic!("expected a native string result: {other:?}"),
    }
}

fn text(value: &Obj) -> String {
    let (size, _, length, bytes) = value.try_string_view().expect("a native String");
    assert_eq!(bytes[size - 1], 0);
    let text = std::str::from_utf8(&bytes[..size - 1]).unwrap();
    assert_eq!(length, text.chars().count());
    text.to_owned()
}

fn assert_clean_shadow() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "string execution and stops retain no ABI objects");
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));
}

#[test]
fn pos_of_returns_the_first_unicode_byte_position_or_the_end() {
    let _guard = lock();
    let source = "aé🦀\0e\u{301}é";
    for (character, position) in [
        ('a', 0),
        ('é', 1),
        ('🦀', 3),
        ('\0', 7),
        ('\u{301}', 9),
        ('Z', 13),
    ] {
        let result = invoke(POS_OF, source, &[character as u64]);
        assert!(result.is_scalar());
        assert_eq!(result.unbox(), position);
    }
    assert_eq!(invoke(POS_OF, "", &['é' as u64]).unbox(), 0);
}

#[test]
fn offset_of_pos_rounds_interior_bytes_forward_and_clamps_arbitrary_naturals() {
    let _guard = lock();
    // Pin Basic.lean gives these examples; interior bytes select the next
    // character index, rather than a floor or an invalid-position refusal.
    for (position, offset) in [
        (0, 0),
        (1, 1),
        (2, 2),
        (3, 2),
        (4, 2),
        (5, 3),
        (7, 3),
        (8, 4),
        (50, 4),
    ] {
        assert_eq!(invoke(OFFSET_OF_POS, "L∃∀N", &[position]).unbox(), offset);
    }
    for position in 1..=6 {
        assert_eq!(invoke(OFFSET_OF_POS, "🦀", &[position]).unbox(), 1);
    }
    for (source, expected) in [("L∃∀N", 4), ("", 0)] {
        let program = fixture(
            OFFSET_OF_POS,
            string(0, source),
            vec![I::NatBig {
                dst: r(1),
                limbs_le: vec![0, 1],
            }],
        );
        assert_eq!(returned(&program).unbox(), expected);
    }
}

#[test]
fn pushn_repeats_unicode_scalars_and_preserves_embedded_nul_and_zero_count() {
    let _guard = lock();
    for (source, character, count, expected) in [
        ("indeed", '!', 2, "indeed!!"),
        ("é", '🦀', 2, "é🦀🦀"),
        ("prefix", '\0', 2, "prefix\0\0"),
        ("é🦀", 'x', 0, "é🦀"),
        ("", ' ', 4, "    "),
    ] {
        assert_eq!(
            text(&invoke(PUSHN, source, &[character as u64, count])),
            expected
        );
    }
}

#[test]
fn formatter_string_primitives_compose_through_owned_canonical_replay() {
    let _guard = lock();
    let program = replay(vec![
        string(0, "α\nβ"),
        nat(1, '\n' as u64),
        call(2, POS_OF, &[0, 1]),
        call(3, OFFSET_OF_POS, &[0, 2]),
        call(4, "extern:String.Internal.next", &[0, 2]),
        nat(5, 0),
        call(6, "extern:String.Internal.extract", &[0, 5, 2]),
        nat(7, ' ' as u64),
        nat(8, 3),
        call(9, PUSHN, &[6, 7, 8]),
        nat(10, 5),
        call(11, "extern:String.Internal.extract", &[0, 4, 10]),
        I::Array {
            dst: r(12),
            items: [0, 6, 9, 11, 2, 3, 4].into_iter().map(r).collect(),
        },
        I::Return { src: r(12) },
    ]);
    shadow::enable();
    for _ in 0..2 {
        let result = returned(&program);
        for (index, expected) in ["α\nβ", "α", "α   ", "β"].into_iter().enumerate() {
            assert_eq!(text(&result.array_child(index)), expected);
        }
        assert_eq!(result.array_child(4).unbox(), 2);
        assert_eq!(result.array_child(5).unbox(), 1);
        assert_eq!(result.array_child(6).unbox(), 3);
    }
    assert_clean_shadow();
}

#[test]
fn oversized_pushn_is_a_memory_nonanswer_without_a_partial_string() {
    let _guard = lock();
    let cases = [
        (nat(2, OUTPUT_LIMIT / 4 + 1), OUTPUT_LIMIT + 6),
        (
            I::NatBig {
                dst: r(2),
                limbs_le: vec![0, 1],
            },
            u64::MAX,
        ),
    ];
    shadow::enable();
    for (count, observed) in cases {
        let program = fixture(PUSHN, string(0, "é"), vec![nat(1, '🦀' as u64), count]);
        let stopped = execute(&program, ExecutionLimits::default(), None);
        assert_eq!(stopped.authority(), Authority::NonAuthoritative);
        assert!(matches!(
            stopped,
            Outcome::Inconclusive(ref inconclusive)
                if matches!(
                    &inconclusive.cause,
                    InconclusiveCause::ResourceExhausted { usage }
                        if usage.reason == ResourceReason::Memory { limit_bytes: OUTPUT_LIMIT }
                            && usage.allowed == OUTPUT_LIMIT
                            && usage.observed == observed
                ) && inconclusive.progress.is_some()
        ));
    }
    assert_eq!(text(&invoke(PUSHN, "é", &['🦀' as u64, 2])), "é🦀🦀");
    assert_clean_shadow();
}

#[test]
fn malformed_scalar_and_operand_types_are_typed_refusals() {
    let _guard = lock();
    for (row, operation) in [
        (POS_OF, "String.Internal.posOf"),
        (PUSHN, "String.Internal.pushn"),
    ] {
        for scalar in [0xd800, 0xdfff, 0x11_0000, 1u64 << 32] {
            let mut operands = vec![nat(1, scalar)];
            if row == PUSHN {
                operands.push(nat(2, 1));
            }
            assert!(matches!(
                execute(&fixture(row, string(0, "value"), operands), ExecutionLimits::default(), None),
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::NatOverflow { operation: actual },
                    ..
                }) if actual == operation
            ));
        }
    }
    assert!(matches!(
        execute(
            &fixture(POS_OF, nat(0, 0), vec![nat(1, 65)]),
            ExecutionLimits::default(),
            None
        ),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch {
                operation: "String.Internal.posOf",
                argument: 0,
                expected: "String",
                actual: ValueKind::Scalar,
            },
            ..
        })
    ));
    for (row, argument, operands) in [
        (OFFSET_OF_POS, 1, vec![string(1, "position")]),
        (PUSHN, 2, vec![nat(1, 65), string(2, "count")]),
    ] {
        assert!(matches!(
            execute(&fixture(row, string(0, "source"), operands), ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch { argument: actual, .. },
                ..
            }) if actual == argument
        ));
    }
}

#[test]
fn string_execution_stops_and_retries_without_publishing_or_leaking_outputs() {
    let _guard = lock();
    let program = fixture(
        PUSHN,
        string(0, "prefix"),
        vec![nat(1, 'é' as u64), nat(2, 3)],
    );
    shadow::enable();
    for allowed in [3, 4] {
        let stopped = execute(
            &program,
            ExecutionLimits {
                max_steps: allowed,
                ..ExecutionLimits::default()
            },
            None,
        );
        assert!(matches!(
            stopped,
            Outcome::Inconclusive(ref inconclusive)
                if matches!(
                    &inconclusive.cause,
                    InconclusiveCause::ResourceExhausted { usage }
                        if usage.reason == ResourceReason::ExecutionSteps
                            && usage.allowed == allowed
                            && usage.observed == allowed + 1
                )
        ));
    }
    let polls = Cell::new(0);
    let cancel_before_intrinsic = || {
        polls.set(polls.get() + 1);
        polls.get() == 4
    };
    assert!(matches!(
        execute(&program, ExecutionLimits::default(), Some(&cancel_before_intrinsic)),
        Outcome::Inconclusive(inconclusive)
            if matches!(inconclusive.cause, InconclusiveCause::Cancelled { .. })
    ));
    assert_eq!(text(&returned(&program)), "prefixééé");
    assert_clean_shadow();
}
