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
use fln_vm::extern_row::{
    ArgumentOwnership as ContractArgument, Ownership, ResultOwnership as ContractResult,
};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{ExecutionLimits, ValueKind, VmExit, VmRefusal, execute};
use std::cell::Cell;
use std::sync::{Mutex, MutexGuard};

const POS_OF: &str = "extern:String.Internal.posOf";
const OFFSET_OF_POS: &str = "extern:String.Internal.offsetOfPos";
const PUSHN: &str = "extern:String.Internal.pushn";
const INTERCALATE: &str = "extern:String.Internal.intercalate";
const OUTPUT_LIMIT: u64 = 16 * 1024 * 1024;
static TEST_LOCK: Mutex<()> = Mutex::new(());

fn lock() -> MutexGuard<'static, ()> {
    TEST_LOCK.lock().unwrap_or_else(|error| error.into_inner())
}

fn r(index: u16) -> Register {
    Register::new(index)
}

fn nat(dst: u16, value: u64) -> I {
    if value <= (usize::MAX >> 1) as u64 {
        I::Nat { dst: r(dst), value }
    } else {
        I::NatBig {
            dst: r(dst),
            limbs_le: vec![value],
        }
    }
}

fn string(dst: u16, value: &str) -> I {
    I::String {
        dst: r(dst),
        value: value.to_owned(),
    }
}

fn call(dst: u16, row: &str, args: &[u16]) -> I {
    let generated = EXTERN_ROWS.iter().find(|entry| entry.id == row).unwrap();
    let ownership = Ownership::parse(generated.ownership).unwrap();
    I::Intrinsic {
        dst: r(dst),
        row: row.to_owned(),
        args: args.iter().copied().map(r).collect(),
        argument_ownership: ownership
            .argument_ownership(args.len())
            .unwrap()
            .into_iter()
            .map(|value| match value {
                ContractArgument::Borrowed => A::Borrowed,
                ContractArgument::Owned => A::Owned,
                ContractArgument::Scalar => A::Scalar,
                ContractArgument::Unique => A::Unique,
            })
            .collect(),
        result_ownership: match ownership.result_ownership().unwrap() {
            ContractResult::Owned => R::Owned,
            ContractResult::Borrowed => R::Borrowed,
            ContractResult::Scalar => R::Scalar,
            ContractResult::RawObject => R::RawObject,
        },
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

fn intercalate_program(separator: &str, entries: &[&str], scalar_nil: bool) -> ValidatedProgram {
    let mut code = vec![string(0, separator)];
    code.push(if scalar_nil {
        nat(1, 0)
    } else {
        I::Ctor {
            dst: r(1),
            tag: 0,
            fields: vec![],
            scalar_bytes: vec![],
        }
    });
    for entry in entries.iter().rev() {
        code.push(string(2, entry));
        code.push(I::Ctor {
            dst: r(1),
            tag: 1,
            fields: vec![r(2), r(1)],
            scalar_bytes: vec![],
        });
    }
    code.extend([
        call(8, INTERCALATE, &[0, 1]),
        // The row borrows both inputs. A second call observes the same list,
        // including each empty entry and embedded NUL in the first result.
        call(9, INTERCALATE, &[0, 1]),
        call(10, "extern:String.Internal.append", &[8, 9]),
        I::Return { src: r(10) },
    ]);
    replay(code)
}

#[test]
fn intercalate_keeps_unicode_empty_entries_and_embedded_nuls_in_list_order() {
    let _guard = lock();
    shadow::enable();
    // Expected values observed on the exact pin; both forms of fieldless nil
    // occur at the Golem/imported-IR boundary and retain the same list shape.
    for scalar_nil in [false, true] {
        for (separator, entries, expected) in [
            ("λ", vec!["a", "", "😀\0", "z"], "aλλ😀\0λz"),
            ("", vec!["", "a", ""], "a"),
            ("x", vec![], ""),
            ("not inserted", vec!["λ\0"], "λ\0"),
            ("\0", vec!["", "", ""], "\0\0"),
        ] {
            let result = returned(&intercalate_program(separator, &entries, scalar_nil));
            assert_eq!(text(&result), format!("{expected}{expected}"));
        }
    }
    assert_clean_shadow();
}

#[test]
fn intercalate_refuses_malformed_list_spines_and_non_string_elements() {
    let _guard = lock();
    shadow::enable();
    for malformed in [
        nat(1, 1),
        I::Ctor {
            dst: r(1),
            tag: 2,
            fields: vec![],
            scalar_bytes: vec![],
        },
        I::Ctor {
            dst: r(1),
            tag: 1,
            fields: vec![r(2)],
            scalar_bytes: vec![],
        },
        I::Ctor {
            dst: r(1),
            tag: 1,
            fields: vec![r(2), r(3)],
            scalar_bytes: vec![],
        },
    ] {
        let program = replay(vec![
            string(0, ","),
            nat(2, 0),
            nat(3, 0),
            malformed,
            call(8, INTERCALATE, &[0, 1]),
            I::Return { src: r(8) },
        ]);
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch { .. },
                ..
            })
        ));
    }
    let late_tail = replay(vec![
        string(0, ","),
        string(2, "valid head"),
        nat(3, 1),
        I::Ctor {
            dst: r(1),
            tag: 1,
            fields: vec![r(2), r(3)],
            scalar_bytes: vec![],
        },
        call(8, INTERCALATE, &[0, 1]),
        I::Return { src: r(8) },
    ]);
    assert!(matches!(
        execute(&late_tail, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch { .. },
            ..
        })
    ));
    assert_clean_shadow();
}

#[test]
fn intercalate_bounds_total_join_size_before_allocating_or_publishing_a_string() {
    let _guard = lock();
    let separator = "x".repeat(65_537);
    let entries = vec![""; 257];
    let program = intercalate_program(&separator, &entries, false);
    shadow::enable();
    let result = execute(&program, ExecutionLimits::default(), None);
    assert_eq!(result.authority(), Authority::NonAuthoritative);
    assert!(matches!(result, Outcome::Inconclusive(ref stop)
        if matches!(&stop.cause, InconclusiveCause::ResourceExhausted { usage }
            if usage.reason == ResourceReason::Memory { limit_bytes: OUTPUT_LIMIT }
                && usage.allowed == OUTPUT_LIMIT && usage.observed == 65_537 * 256)));
    assert_clean_shadow();
}

#[test]
fn intercalate_bounds_empty_list_spines_independently_of_output_bytes() {
    let _guard = lock();
    let mut code = vec![string(0, ""), nat(1, 0), string(2, "")];
    for _ in 0..65_537 {
        code.push(I::Ctor {
            dst: r(1),
            tag: 1,
            fields: vec![r(2), r(1)],
            scalar_bytes: vec![],
        });
    }
    code.extend([call(8, INTERCALATE, &[0, 1]), I::Return { src: r(8) }]);
    let program = replay(code);
    shadow::enable();
    let outcome = execute(&program, ExecutionLimits::default(), None);
    assert_eq!(outcome.authority(), Authority::NonAuthoritative);
    assert!(matches!(outcome, Outcome::Inconclusive(ref stop)
        if matches!(&stop.cause, InconclusiveCause::ResourceExhausted { usage }
            if usage.reason == ResourceReason::ExecutionSteps
                && usage.allowed == 65_536 && usage.observed == 65_537)
            && stop.progress.as_ref().is_some_and(|progress|
                progress.text().contains("String.Internal.intercalate native list traversal"))));
    assert_clean_shadow();
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

fn substring_program(row: &str, begin: u64, end: u64, operands: Vec<I>) -> ValidatedProgram {
    let count = u16::try_from(operands.len()).unwrap();
    let mut code = vec![
        string(0, "aλ😀z"),
        nat(1, begin),
        nat(2, end),
        I::Ctor {
            dst: r(3),
            tag: 0,
            fields: vec![r(0), r(1), r(2)],
            scalar_bytes: vec![],
        },
    ];
    code.extend(operands);
    let args: Vec<_> = std::iter::once(3).chain(4..4 + count).collect();
    code.push(call(8, row, &args));
    code.push(I::Return { src: r(8) });
    replay(code)
}

fn substring(row: &str, begin: u64, end: u64, operands: &[u64]) -> Obj {
    returned(&substring_program(
        row,
        begin,
        end,
        operands
            .iter()
            .enumerate()
            .map(|(i, value)| nat(i as u16 + 4, *value))
            .collect(),
    ))
}

fn raw_positions(value: &Obj) -> (String, String, String) {
    (
        text(&value.try_ctor_child(0).expect("substring string")),
        fln_vm::interpreter::nat_decimal(&value.try_ctor_child(1).expect("substring start"))
            .unwrap(),
        fln_vm::interpreter::nat_decimal(&value.try_ctor_child(2).expect("substring stop"))
            .unwrap(),
    )
}

/// Expected values were measured by the pinned v4.32.0 exported Lean
/// implementations, including the unusual invalid/interior byte positions.
#[test]
fn native_substrings_copy_and_navigate_relative_utf8_positions() {
    let _guard = lock();
    shadow::enable();
    for (begin, end, expected) in [
        (0, 1, "a"),
        (1, 3, "λ"),
        (3, 7, "😀"),
        (1, 7, "λ😀"),
        (3, 3, ""),
        (2, 7, ""),
        (1, 4, "λ😀z"),
        (99, 100, ""),
        (7, 1, ""),
    ] {
        assert_eq!(
            text(&substring(
                "extern:Substring.Raw.Internal.toString",
                begin,
                end,
                &[]
            )),
            expected
        );
    }
    for (begin, end, expected) in [(1, 7, 955), (3, 3, 128512), (8, 8, 65), (2, 7, 65)] {
        assert_eq!(
            substring("extern:Substring.Raw.Internal.front", begin, end, &[]).unbox(),
            expected
        );
    }
    for (position, expected) in [(0, 955), (1, 65), (2, 128512), (6, 122), (7, 65), (99, 65)] {
        // get deliberately reads past the substring's end in the backing string.
        assert_eq!(
            substring("extern:Substring.Raw.Internal.get", 1, 3, &[position]).unbox(),
            expected
        );
    }
    for (position, expected) in [(0, 0), (1, 0), (2, 0), (3, 2), (6, 2), (7, 6), (99, 98)] {
        assert_eq!(
            substring("extern:Substring.Raw.Internal.prev", 1, 7, &[position]).unbox(),
            expected
        );
    }
    for (source, expected) in [("", 65), ("λ😀", 955), ("\0z", 0)] {
        assert_eq!(
            invoke("extern:String.Internal.front", source, &[]).unbox(),
            expected
        );
    }
    assert_clean_shadow();
}

#[test]
fn native_substring_slices_keep_the_backing_string_and_clamp_at_the_stop() {
    let _guard = lock();
    shadow::enable();
    for (count, expected) in [(0, 1), (1, 3), (2, 7), (3, 7), (100, 7)] {
        let value = substring("extern:Substring.Raw.Internal.drop", 1, 7, &[count]);
        assert_eq!(
            raw_positions(&value),
            ("aλ😀z".to_owned(), expected.to_string(), "7".to_owned())
        );
    }
    for (begin, end, backing, expected_begin, expected_end) in [
        (0, 6, "aλ😀z", 1, 7),
        (1, 6, "aλ😀z", 2, 7),
        (0, 99, "aλ😀z", 1, 7),
        (4, 2, "", 0, 0),
        (99, 100, "aλ😀z", 7, 7),
    ] {
        let value = substring("extern:Substring.Raw.Internal.extract", 1, 7, &[begin, end]);
        assert_eq!(
            raw_positions(&value),
            (
                backing.to_owned(),
                expected_begin.to_string(),
                expected_end.to_string()
            )
        );
    }
    for (begin, end, empty) in [(1, 7, false), (3, 3, true), (7, 1, true)] {
        assert_eq!(
            substring("extern:Substring.Raw.Internal.isEmpty", begin, end, &[]).unbox(),
            usize::from(empty)
        );
    }
    // The count is a Nat, never a truncated machine integer. A finite slice
    // can saturate without visiting that enormous count on the host stack.
    {
        let program = substring_program(
            "extern:Substring.Raw.Internal.drop",
            1,
            7,
            vec![I::NatBig {
                dst: r(4),
                limbs_le: vec![0, 1 << 36],
            }],
        );
        assert_eq!(
            raw_positions(&returned(&program)),
            ("aλ😀z".to_owned(), "7".to_owned(), "7".to_owned())
        );
    }
    assert_clean_shadow();
}

#[test]
fn native_substring_equality_repairs_positions_and_compares_contents() {
    let _guard = lock();
    shadow::enable();
    for (begin, end, other, a, b, expected) in [
        (1, 7, "λ😀", 0, 6, true),
        (1, 7, "λX", 0, 3, false),
        (2, 7, "", 0, 0, true),
        (7, 1, "", 0, 0, true),
    ] {
        let program = replay(vec![
            string(0, "aλ😀z"),
            nat(1, begin),
            nat(2, end),
            I::Ctor {
                dst: r(3),
                tag: 0,
                fields: vec![r(0), r(1), r(2)],
                scalar_bytes: vec![],
            },
            string(4, other),
            nat(5, a),
            nat(6, b),
            I::Ctor {
                dst: r(7),
                tag: 0,
                fields: vec![r(4), r(5), r(6)],
                scalar_bytes: vec![],
            },
            call(8, "extern:Substring.Raw.Internal.beq", &[3, 7]),
            I::Return { src: r(8) },
        ]);
        assert_eq!(returned(&program).unbox(), usize::from(expected));
    }
    assert_clean_shadow();
}

#[test]
fn raw_position_arithmetic_keeps_arbitrary_precision_and_truncated_subtraction() {
    let _guard = lock();
    for (row, expected) in [
        ("extern:String.Pos.Raw.Internal.sub", "17"),
        (
            "extern:String.Pos.Raw.Internal.min",
            "1267650600228229401496703205376",
        ),
    ] {
        let program = replay(vec![
            I::NatBig {
                dst: r(0),
                limbs_le: vec![17, 1 << 36],
            },
            I::NatBig {
                dst: r(1),
                limbs_le: vec![0, 1 << 36],
            },
            call(2, row, &[0, 1]),
            I::Return { src: r(2) },
        ]);
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&returned(&program)).as_deref(),
            Some(expected)
        );
    }
    let program = replay(vec![
        nat(0, 3),
        nat(1, 7),
        call(2, "extern:String.Pos.Raw.Internal.sub", &[0, 1]),
        I::Return { src: r(2) },
    ]);
    assert_eq!(returned(&program).unbox(), 0);
}

#[test]
fn substring_copy_uses_the_pin_scalar_tag_boundary_for_each_endpoint() {
    let _guard = lock();
    // 2^63 fits usize on the pin but is already a heap Nat. The native
    // extractor returns the complete backing string if either endpoint is
    // heap-valued, including when the other endpoint would select a suffix.
    for (begin, end) in [(1u64 << 63, (1u64 << 63) + 1), (1, 1u64 << 63)] {
        assert_eq!(
            text(&substring(
                "extern:Substring.Raw.Internal.toString",
                begin,
                end,
                &[]
            )),
            "aλ😀z"
        );
    }
}

#[test]
fn malformed_substring_records_are_refused_and_nat_limits_remain_nonanswers() {
    let _guard = lock();
    shadow::enable();
    for value in [
        nat(3, 0),
        I::Ctor {
            dst: r(3),
            tag: 1,
            fields: vec![],
            scalar_bytes: vec![],
        },
        I::Ctor {
            dst: r(3),
            tag: 0,
            fields: vec![],
            scalar_bytes: vec![],
        },
    ] {
        let program = replay(vec![
            value,
            call(8, "extern:Substring.Raw.Internal.toString", &[3]),
            I::Return { src: r(8) },
        ]);
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch { .. },
                ..
            })
        ));
    }
    let program = substring_program(
        "extern:Substring.Raw.Internal.drop",
        1,
        7,
        vec![I::NatBig {
            dst: r(4),
            limbs_le: vec![0, 1 << 36],
        }],
    );
    let limits = ExecutionLimits {
        max_nat_magnitude_bytes: 8,
        ..ExecutionLimits::default()
    };
    assert!(matches!(
        execute(&program, limits, None),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(raw_positions(&returned(&program)).1, "7");
    assert_clean_shadow();
}

#[test]
fn checked_string_positions_distinguish_character_boundaries_from_the_end() {
    let _guard = lock();
    shadow::enable();
    for (position, valid, character) in [
        (0, true, Some('a')),
        (1, true, Some('λ')),
        (2, false, None),
        (3, true, Some('😀')),
        (4, false, None),
        (5, false, None),
        (6, false, None),
        (7, true, Some('\0')),
        (8, true, None),
        (9, false, None),
        (1 << 63, false, None),
    ] {
        assert_eq!(
            invoke("extern:String.Pos.Raw.isValid", "aλ😀\0", &[position]).unbox(),
            usize::from(valid),
        );
        for row in ["extern:String.Pos.Raw.get?", "extern:String.get?"] {
            let option = invoke(row, "aλ😀\0", &[position]);
            match character {
                Some(character) => {
                    assert_eq!(option.header().tag, 1);
                    assert_eq!(option.header().other, 1);
                    assert_eq!(
                        option.try_ctor_child(0).unwrap().unbox(),
                        character as usize
                    );
                }
                None => {
                    assert_eq!(option.header().tag, 0);
                    assert_eq!(option.header().other, 0);
                }
            }
        }
    }
    assert_eq!(invoke("extern:String.Pos.Raw.isValid", "", &[0]).unbox(), 1);
    assert_eq!(
        invoke("extern:String.Pos.Raw.get?", "", &[0]).header().tag,
        0
    );
    for row in ["extern:String.Pos.Raw.get!", "extern:String.get!"] {
        assert_eq!(invoke(row, "aλ😀", &[1]).unbox(), 'λ' as usize);
    }
    assert_clean_shadow();
}

#[test]
fn string_get_bang_reports_the_pinned_recoverable_panic_and_respects_capture_limits() {
    const TEST: &str =
        "string_get_bang_reports_the_pinned_recoverable_panic_and_respects_capture_limits";
    const CHILD: &str = "FLN_STRING_GET_BANG_TEST";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", TEST, "--nocapture", "--test-threads=1"])
            .env(CHILD, "1")
            .env("LEAN_BACKTRACE", "0")
            .env_remove("LEAN_ABORT_ON_PANIC")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        return;
    }
    let _guard = lock();
    const MESSAGE: &[u8] = b"Error: invalid `String.Pos` at `String.get!`\n";
    for row in ["extern:String.Pos.Raw.get!", "extern:String.get!"] {
        for position in [2, 3, 1 << 63] {
            let capture = fln_rt::obj::StdoutCapture::begin_isolated(MESSAGE.len(), true).unwrap();
            assert_eq!(invoke(row, "aλ", &[position]).unbox(), 'A' as usize);
            let output = capture.finish();
            assert_eq!(output.error, None);
            assert_eq!(output.bytes, MESSAGE);
        }
        let program = fixture(row, string(0, "aλ"), vec![nat(1, 2)]);
        let capture = fln_rt::obj::StdoutCapture::begin_isolated(MESSAGE.len() - 1, true).unwrap();
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), None),
            Outcome::Inconclusive(_)
        ));
        let output = capture.finish();
        assert!(output.bytes.is_empty());
        assert_eq!(
            output.error,
            Some(fln_rt::obj::StdoutCaptureError::Limit {
                limit: MESSAGE.len() - 1,
                requested: MESSAGE.len(),
            })
        );
    }
}

#[test]
fn slice_hashes_share_string_hashes_without_copying_or_truncating_the_word() {
    let _guard = lock();
    shadow::enable();
    // Measured with the exact pinned executable, not computed by the port.
    for (source, begin, end, slice, expected) in [
        ("aλ😀z", 1, 7, "λ😀", 8_638_642_137_254_647_478u64),
        ("\0abc\0", 0, 5, "\0abc\0", 5_466_980_230_118_552_491),
        ("abc", 1, 1, "", 9_877_294_847_684_254_529),
        (
            "abcdefghijk",
            0,
            11,
            "abcdefghijk",
            16_840_220_840_137_896_361,
        ),
    ] {
        let program = replay(vec![
            string(0, source),
            nat(1, begin),
            nat(2, end),
            I::Ctor {
                dst: r(3),
                tag: 0,
                fields: vec![r(0), r(1), r(2)],
                scalar_bytes: vec![],
            },
            call(4, "extern:String.Slice.hash", &[3]),
            string(5, slice),
            call(6, "extern:String.hash", &[5]),
            call(7, "extern:UInt64.decEq", &[4, 6]),
            call(8, "extern:UInt64.toNat", &[4]),
            I::Array {
                dst: r(9),
                items: vec![r(7), r(8)],
            },
            I::Return { src: r(9) },
        ]);
        let result = returned(&program);
        assert_eq!(result.array_child(0).unbox(), 1);
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&result.array_child(1)).unwrap(),
            expected.to_string()
        );
    }
    // The first hash has its high bit set. Returning a tagged Nat here would
    // discard that bit; UInt64.toNat must recover all 64 bits after replay.
    let hash = invoke("extern:String.hash", "", &[]);
    assert_eq!(
        hash.try_ctor_scalar_u64(0).unwrap(),
        9_877_294_847_684_254_529
    );
    assert!(hash.try_ctor_scalar_u64(0).unwrap() > (usize::MAX >> 1) as u64);
    drop(hash);
    assert_clean_shadow();
}

#[test]
fn slice_comparison_uses_lexicographic_bytes_and_memcmp_honors_raw_byte_windows() {
    let _guard = lock();
    for (left, right, expected) in [
        ("λ", "😀", true),
        ("a", "ab", true),
        ("ab", "a", false),
        ("", "", false),
        ("a\0b", "a\0c", true),
    ] {
        let program = replay(vec![
            string(0, left),
            nat(1, 0),
            nat(2, left.len() as u64),
            I::Ctor {
                dst: r(3),
                tag: 0,
                fields: vec![r(0), r(1), r(2)],
                scalar_bytes: vec![],
            },
            string(4, right),
            nat(5, right.len() as u64),
            I::Ctor {
                dst: r(6),
                tag: 0,
                fields: vec![r(4), r(1), r(5)],
                scalar_bytes: vec![],
            },
            call(7, "extern:String.Slice.instDecidableLt", &[3, 6]),
            I::Return { src: r(7) },
        ]);
        assert_eq!(returned(&program).unbox(), usize::from(expected));
    }
    for (left, right, begin, other, length, expected) in [
        ("aλ😀z", "λ😀", 1, 0, 6, true),
        ("aλ😀z", "λX", 1, 0, 3, false),
        ("λ", "λ", 1, 1, 1, true),
        ("abc", "", 3, 0, 0, true),
        ("a\0b", "a\0c", 1, 1, 1, true),
    ] {
        let program = replay(vec![
            string(0, left),
            string(1, right),
            nat(2, begin),
            nat(3, other),
            nat(4, length),
            call(
                5,
                "extern:String.Slice.Pattern.Internal.memcmpStr",
                &[0, 1, 2, 3, 4],
            ),
            I::Return { src: r(5) },
        ]);
        assert_eq!(returned(&program).unbox(), usize::from(expected));
    }
}

#[test]
fn malformed_slice_bounds_and_missing_memcmp_proofs_never_read_outside_buffers() {
    let _guard = lock();
    for (begin, end) in [(2, 7), (3, 4), (7, 1), (0, 9), (1 << 63, 1 << 63)] {
        let program = substring_program("extern:String.Slice.hash", begin, end, vec![]);
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused { .. })
        ));
    }
    for (begin, end, length) in [(0, 0, 4), (4, 0, 0), (0, 4, 0), (2, 2, 2), (1 << 63, 0, 0)] {
        let program = replay(vec![
            string(0, "abc"),
            string(1, "abc"),
            nat(2, begin),
            nat(3, end),
            nat(4, length),
            call(
                5,
                "extern:String.Slice.Pattern.Internal.memcmpStr",
                &[0, 1, 2, 3, 4],
            ),
            I::Return { src: r(5) },
        ]);
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused { .. })
        ));
    }
}
