//! Native Array and ByteArray operations through generated ABI contracts,
//! ownership insertion and canonical FLBC replay.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, OwnershipLimits, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{Authority, InconclusiveCause, Outcome};
use fln_rt::obj::{Obj, StdoutCapture, StdoutCaptureError, shadow};
use fln_vm::extern_row::{ArgumentOwnership as CA, Ownership, ResultOwnership as CR};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::cell::Cell;
use std::io::Write;
use std::process::{Command, Stdio};
use std::sync::Mutex;

const OUTPUT_LIMIT: u64 = 16 * 1024 * 1024;
const BOUNDS_MESSAGE: &[u8] = b"Error: index out of bounds\n";
static TEST_LOCK: Mutex<()> = Mutex::new(());

const fn r(index: u16) -> Register {
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
fn huge(dst: u16) -> I {
    I::NatBig {
        dst: r(dst),
        limbs_le: vec![0, 0, 1],
    }
}
fn string(dst: u16, value: &str) -> I {
    I::String {
        dst: r(dst),
        value: value.to_owned(),
    }
}
fn array(dst: u16, items: &[u16]) -> I {
    I::Array {
        dst: r(dst),
        items: items.iter().copied().map(r).collect(),
    }
}
fn call(dst: u16, name: &str, args: &[u16]) -> I {
    let row = EXTERN_ROWS.iter().find(|row| row.id == name).unwrap();
    let ownership = Ownership::parse(row.ownership).unwrap();
    I::Intrinsic {
        dst: r(dst),
        row: name.to_owned(),
        args: args.iter().copied().map(r).collect(),
        argument_ownership: ownership
            .argument_ownership(args.len())
            .unwrap()
            .into_iter()
            .map(|argument| match argument {
                CA::Borrowed => A::Borrowed,
                CA::Owned => A::Owned,
                CA::Unique => A::Unique,
                CA::Scalar => A::Scalar,
            })
            .collect(),
        result_ownership: match ownership.result_ownership().unwrap() {
            CR::Borrowed => R::Borrowed,
            CR::Owned => R::Owned,
            CR::Scalar => R::Scalar,
            CR::RawObject => R::RawObject,
        },
    }
}
fn byte_input(bytes: &[u8]) -> Vec<I> {
    let mut code = Vec::new();
    let mut items = Vec::new();
    for (index, byte) in bytes.iter().enumerate() {
        let register = 16 + u16::try_from(index).unwrap();
        code.push(nat(register, u64::from(*byte)));
        items.push(register);
    }
    code.extend([array(0, &items), call(1, "extern:ByteArray.mk", &[0])]);
    code
}
fn replay(code: Vec<I>, owned: bool) -> ValidatedProgram {
    let mut program = flbc::validate(Program::new(
        FunctionId::new(0),
        vec![Function {
            id: FunctionId::new(0),
            arity: 0,
            parameter_ownership: vec![],
            result_ownership: C::Erased,
            register_count: 64,
            code,
        }],
    ))
    .unwrap();
    if owned {
        let candidate = flbc::insert_ownership(&program, OwnershipLimits::default()).unwrap();
        flbc::validate_ownership_candidate(
            &program,
            candidate.program().clone(),
            candidate.witness().clone(),
            OwnershipLimits::default(),
        )
        .unwrap();
        program = candidate.program().clone();
    }
    let bytes = flbc::encode_canonical(&program, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap(),
        bytes
    );
    decoded
}
fn returned(program: &ValidatedProgram) -> Obj {
    match execute(program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(result)) => result.value,
        other => panic!("expected native array result: {other:?}"),
    }
}
fn text(value: &Obj) -> String {
    let (size, _, _, bytes) = value.try_string_view().unwrap();
    String::from_utf8(bytes[..size - 1].to_vec()).unwrap()
}
fn bytes(value: &Obj) -> Vec<u8> {
    value.try_borrow_sarray_view().unwrap().3.to_vec()
}
fn clean_shadow() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "native arrays and stops retain no ABI objects");
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
    )));
}

#[test]
fn replicate_retains_heap_values_and_set_preserves_shared_snapshots() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for owned in [false, true] {
        let program = replay(
            vec![
                string(0, "payload λ"),
                nat(1, 3),
                I::Copy {
                    dst: r(10),
                    src: r(0),
                },
                call(2, "extern:Array.replicate", &[1, 0]),
                I::Copy {
                    dst: r(11),
                    src: r(2),
                },
                string(3, "changed"),
                nat(4, 1),
                call(5, "extern:Array.set!", &[2, 4, 3]),
                call(6, "extern:Array.getInternalBorrowed", &[5, 4]),
                nat(7, 0),
                call(8, "extern:Array.getInternal", &[11, 7]),
                array(9, &[10, 11, 5, 6, 8]),
                I::Return { src: r(9) },
            ],
            owned,
        );
        let value = returned(&program);
        let original = value.array_child(1);
        let updated = value.array_child(2);
        assert_eq!(original.array_view().0, 3);
        assert_eq!(updated.array_view().0, 3);
        assert_ne!(original.identity_token(), updated.identity_token());
        for index in 0..3 {
            assert_eq!(text(&original.array_child(index)), "payload λ");
            assert_eq!(
                text(&updated.array_child(index)),
                if index == 1 { "changed" } else { "payload λ" }
            );
        }
        assert_eq!(text(&value.array_child(3)), "changed");
        assert_eq!(text(&value.array_child(4)), "payload λ");
        assert_eq!(
            value.array_child(0).identity_token(),
            original.array_child(2).identity_token()
        );
        drop((original, updated, value));
        let empty = replay(
            vec![
                nat(0, 0),
                string(1, "unused payload"),
                call(2, "extern:Array.replicate", &[0, 1]),
                I::Return { src: r(2) },
            ],
            owned,
        );
        assert_eq!(returned(&empty).array_view().0, 0);
    }
    clean_shadow();
}

#[test]
fn boxed_usize_composes_with_array_reads_and_copy_on_write_updates() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for owned in [false, true] {
        let program = replay(
            vec![
                string(0, "zero"),
                string(1, "one"),
                array(2, &[0, 1]),
                call(3, "extern:Array.usize", &[2]),
                nat(4, 1),
                call(5, "extern:USize.ofNat", &[4]),
                call(6, "extern:Array.uget", &[2, 5]),
                call(7, "extern:Array.ugetBorrowed", &[2, 5]),
                I::Copy {
                    dst: r(11),
                    src: r(2),
                },
                string(8, "new"),
                call(9, "extern:Array.uset", &[2, 5, 8]),
                array(10, &[11, 3, 6, 7, 9]),
                I::Return { src: r(10) },
            ],
            owned,
        );
        let value = returned(&program);
        assert_eq!(value.array_child(1).try_ctor_scalar_u64(0), Some(2));
        assert_eq!(text(&value.array_child(2)), "one");
        assert_eq!(text(&value.array_child(3)), "one");
        assert_eq!(text(&value.array_child(0).array_child(1)), "one");
        assert_eq!(text(&value.array_child(4).array_child(1)), "new");
        drop(value);
        for row in ["extern:Array.uget", "extern:Array.ugetBorrowed"] {
            let program = replay(
                vec![
                    string(0, "only"),
                    array(1, &[0]),
                    nat(2, u64::MAX),
                    call(3, "extern:USize.ofNat", &[2]),
                    call(4, row, &[1, 3]),
                    I::Return { src: r(4) },
                ],
                owned,
            );
            assert!(matches!(
                execute(&program, ExecutionLimits::default(), None),
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::ArrayIndexOutOfBounds {
                        index: usize::MAX,
                        size: 1
                    },
                    ..
                })
            ));
        }
    }
    clean_shadow();
}

#[test]
fn boxed_usize_composes_with_byte_array_reads_and_updates() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for owned in [false, true] {
        let mut code = byte_input(&[0, 128, 255]);
        code.extend([
            call(2, "extern:ByteArray.usize", &[1]),
            nat(3, 1),
            call(4, "extern:USize.ofNat", &[3]),
            call(5, "extern:ByteArray.uget", &[1, 4]),
            I::Copy {
                dst: r(9),
                src: r(1),
            },
            nat(6, 42),
            call(7, "extern:ByteArray.uset", &[1, 4, 6]),
            array(8, &[9, 2, 5, 7]),
            I::Return { src: r(8) },
        ]);
        let value = returned(&replay(code, owned));
        assert_eq!(bytes(&value.array_child(0)), [0, 128, 255]);
        assert_eq!(value.array_child(1).try_ctor_scalar_u64(0), Some(3));
        assert_eq!(value.array_child(2).unbox(), 128);
        assert_eq!(bytes(&value.array_child(3)), [0, 42, 255]);
        drop(value);
        for row in ["extern:ByteArray.uget", "extern:ByteArray.uset"] {
            let mut code = byte_input(&[17]);
            code.extend([
                nat(2, u64::MAX),
                call(3, "extern:USize.ofNat", &[2]),
                nat(4, 19),
            ]);
            code.push(call(
                5,
                row,
                if row.ends_with("uset") {
                    &[1, 3, 4]
                } else {
                    &[1, 3]
                },
            ));
            code.push(I::Return { src: r(5) });
            assert!(matches!(
                execute(&replay(code, owned), ExecutionLimits::default(), None),
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::ArrayIndexOutOfBounds {
                        index: usize::MAX,
                        size: 1
                    },
                    ..
                })
            ));
        }
    }
    clean_shadow();
}

#[test]
fn byte_array_bang_fallbacks_do_not_accept_invalid_proof_bearing_indices() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for owned in [false, true] {
        for (index, expected, updated) in [
            (nat(2, 1), 255, vec![7, 42]),
            (nat(2, 2), 0, vec![7, 255]),
            (huge(2), 0, vec![7, 255]),
        ] {
            let mut code = byte_input(&[7, 255]);
            code.extend([
                index,
                call(3, "extern:ByteArray.get!", &[1, 2]),
                I::Copy {
                    dst: r(7),
                    src: r(1),
                },
                nat(4, 42),
                call(5, "extern:ByteArray.set!", &[1, 2, 4]),
                array(6, &[7, 3, 5]),
                I::Return { src: r(6) },
            ]);
            let value = returned(&replay(code, owned));
            assert_eq!(bytes(&value.array_child(0)), [7, 255]);
            assert_eq!(value.array_child(1).unbox(), expected);
            assert_eq!(bytes(&value.array_child(2)), updated);
        }
        for row in ["extern:ByteArray.get", "extern:ByteArray.set"] {
            for index in [nat(2, 2), huge(2)] {
                let mut code = byte_input(&[7, 255]);
                code.extend([index, nat(3, 42)]);
                code.push(call(
                    4,
                    row,
                    if row.ends_with("set") {
                        &[1, 2, 3]
                    } else {
                        &[1, 2]
                    },
                ));
                code.push(I::Return { src: r(4) });
                assert!(matches!(
                    execute(&replay(code, owned), ExecutionLimits::default(), None),
                    Outcome::Complete(VmExit::Refused {
                        refusal: VmRefusal::ArrayIndexOutOfBounds { size: 2, .. },
                        ..
                    })
                ));
            }
        }
    }
    clean_shadow();
}

#[test]
fn array_bounds_recovery_preserves_values_and_respects_diagnostic_budget() {
    const CHILD: &str = "FLN_ARRAY_BOUNDS_TEST";
    if std::env::var_os(CHILD).is_none() {
        let output = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "array_bounds_recovery_preserves_values_and_respects_diagnostic_budget",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .env("RUST_BACKTRACE", "0")
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
    for owned in [false, true] {
        for row in [
            "extern:Array.get!Internal",
            "extern:Array.get!InternalBorrowed",
            "extern:Array.set!",
        ] {
            for index in [nat(2, 1), huge(2)] {
                let args = if row.ends_with("set!") {
                    [1, 2, 0]
                } else {
                    [0, 1, 2]
                };
                let program = replay(
                    vec![
                        string(0, "default or replacement"),
                        array(1, &[]),
                        I::Copy {
                            dst: r(5),
                            src: r(0),
                        },
                        I::Copy {
                            dst: r(6),
                            src: r(1),
                        },
                        index,
                        call(3, row, &args),
                        array(4, &[5, 6, 3]),
                        I::Return { src: r(4) },
                    ],
                    owned,
                );
                let limit = BOUNDS_MESSAGE.len() - 1;
                let capture = StdoutCapture::begin_isolated(limit, true).unwrap();
                let stopped = execute(&program, ExecutionLimits::default(), None);
                assert_eq!(stopped.authority(), Authority::NonAuthoritative);
                assert!(matches!(stopped, Outcome::Inconclusive(_)));
                let captured = capture.finish();
                assert!(captured.bytes.is_empty());
                assert_eq!(
                    captured.error,
                    Some(StdoutCaptureError::Limit {
                        limit,
                        requested: BOUNDS_MESSAGE.len()
                    })
                );
                let capture = StdoutCapture::begin_isolated(BOUNDS_MESSAGE.len(), true).unwrap();
                let value = returned(&program);
                assert_eq!(text(&value.array_child(0)), "default or replacement");
                assert_eq!(value.array_child(1).array_view().0, 0);
                if row.ends_with("set!") {
                    assert_eq!(
                        value.array_child(1).identity_token(),
                        value.array_child(2).identity_token()
                    );
                } else {
                    assert_eq!(text(&value.array_child(2)), "default or replacement");
                    assert_eq!(
                        value.array_child(0).identity_token(),
                        value.array_child(2).identity_token()
                    );
                }
                let captured = capture.finish();
                assert_eq!(captured.error, None);
                assert_eq!(captured.bytes, BOUNDS_MESSAGE);
            }
        }
    }
}

#[test]
fn replicate_resource_limits_and_execution_stops_publish_no_partial_array() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    let slots = OUTPUT_LIMIT / std::mem::size_of::<Obj>() as u64;
    for (count, observed) in [
        (
            nat(0, slots + 1),
            (slots + 1) * std::mem::size_of::<Obj>() as u64,
        ),
        (huge(0), u64::MAX),
    ] {
        let program = replay(
            vec![
                count,
                string(1, "retained once"),
                call(2, "extern:Array.replicate", &[0, 1]),
                I::Return { src: r(2) },
            ],
            true,
        );
        let stopped = execute(&program, ExecutionLimits::default(), None);
        assert_eq!(stopped.authority(), Authority::NonAuthoritative);
        assert!(matches!(
            stopped,
            Outcome::Inconclusive(ref stop)
                if matches!(&stop.cause, InconclusiveCause::ResourceExhausted { usage }
                    if usage.reason == ResourceReason::Memory { limit_bytes: OUTPUT_LIMIT }
                        && usage.allowed == OUTPUT_LIMIT && usage.observed == observed)
                    && stop.progress.as_ref().is_some_and(|progress|
                        progress.text().contains("Array.replicate output bytes"))
        ));
    }
    let program = replay(
        vec![
            nat(0, 3),
            string(1, "retry"),
            call(2, "extern:Array.replicate", &[0, 1]),
            I::Return { src: r(2) },
        ],
        false,
    );
    for allowed in 0..4 {
        assert!(matches!(
            execute(&program, ExecutionLimits { max_steps: allowed, ..ExecutionLimits::default() }, None),
            Outcome::Inconclusive(ref stop)
                if matches!(&stop.cause, InconclusiveCause::ResourceExhausted { usage }
                    if usage.reason == ResourceReason::ExecutionSteps
                        && usage.allowed == allowed && usage.observed == allowed + 1)
        ));
    }
    let polls = Cell::new(0);
    let cancel = || {
        polls.set(polls.get() + 1);
        polls.get() == 3
    };
    assert!(matches!(
        execute(&program, ExecutionLimits::default(), Some(&cancel)),
        Outcome::Inconclusive(stop) if matches!(stop.cause, InconclusiveCause::Cancelled { .. })
    ));
    let result = returned(&program);
    assert_eq!(result.array_view().0, 3);
    assert_eq!(text(&result.array_child(2)), "retry");
    drop(result);
    clean_shadow();
}

#[test]
fn native_arrays_refuse_bad_operand_types_and_generated_contracts() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for row in ["extern:Array.replicate", "extern:Array.getInternalBorrowed"] {
        let code = vec![
            string(0, "not a count or array"),
            nat(1, 0),
            call(2, row, &[0, 1]),
            I::Return { src: r(2) },
        ];
        assert!(matches!(
            execute(&replay(code, true), ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch { .. },
                ..
            })
        ));
    }
    for result_mismatch in [false, true] {
        let mut instruction = call(2, "extern:Array.replicate", &[0, 1]);
        if let I::Intrinsic {
            argument_ownership,
            result_ownership,
            ..
        } = &mut instruction
        {
            if result_mismatch {
                *result_ownership = R::Owned;
            } else {
                argument_ownership[1] = A::Borrowed;
            }
        }
        let program = replay(
            vec![
                nat(0, 2),
                string(1, "must not publish"),
                instruction,
                I::Return { src: r(2) },
            ],
            false,
        );
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused { .. })
        ));
    }
    clean_shadow();
}

#[test]
fn byte_array_hash_matches_the_exact_reference_pin_with_all_uint64_bits() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN") else {
        assert_ne!(
            std::env::var("FLN_REQUIRE_REFERENCE").as_deref(),
            Ok("1"),
            "FLN_REFERENCE_LEAN is required for the live Array oracle"
        );
        eprintln!("SKIP live ByteArray.hash oracle: FLN_REFERENCE_LEAN is not configured");
        return;
    };
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .unwrap()
        .split_whitespace()
        .find_map(|word| word.strip_prefix("commit="))
        .unwrap();
    let identity = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);
    let mut command = Command::new(&reference);
    command
        .arg("--stdin")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(library) = std::env::var_os("FLN_REFERENCE_LIB") {
        command.env("LEAN_PATH", library);
    }
    let mut child = command.spawn().unwrap();
    child.stdin.take().unwrap().write_all(
        b"module\nprelude\npublic import Init\npublic meta import Init.System.IO\npublic section\n#eval do\n  for n in List.range 256 do\n    let bytes : ByteArray := { data := #[UInt8.ofNat n] }\n    IO.println bytes.hash.toNat\n"
    ).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let expected: Vec<u64> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| line.parse().expect("Reference UInt64 result"))
        .collect();
    assert_eq!(expected.len(), 256);
    assert!(expected.iter().any(|hash| *hash > (usize::MAX >> 1) as u64));
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for (input, expected) in expected.into_iter().enumerate() {
        for owned in [false, true] {
            let mut code = byte_input(&[u8::try_from(input).unwrap()]);
            code.extend([
                call(2, "extern:ByteArray.hash", &[1]),
                call(3, "extern:UInt64.toNat", &[2]),
                array(4, &[2, 3]),
                I::Return { src: r(4) },
            ]);
            let result = returned(&replay(code, owned));
            assert_eq!(result.array_child(0).try_ctor_scalar_u64(0), Some(expected));
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&result.array_child(1)).as_deref(),
                Some(expected.to_string().as_str())
            );
        }
    }
    clean_shadow();
}
