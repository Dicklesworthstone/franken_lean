//! Every native FloatArray row through generated ownership and canonical FLBC.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::outcome::Outcome;
use fln_rt::obj::{Obj, shadow};
use fln_vm::extern_row::{
    ArgumentOwnership as ContractArgument, Ownership, ResultOwnership as ContractResult,
};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::sync::Mutex;

static TEST_LOCK: Mutex<()> = Mutex::new(());

fn r(index: u16) -> Register {
    Register::new(index)
}

fn nat(dst: u16, value: u64) -> I {
    I::Nat { dst: r(dst), value }
}

fn wide(dst: u16, bits: u64) -> I {
    I::Ctor {
        dst: r(dst),
        tag: 0,
        fields: Vec::new(),
        scalar_bytes: bits.to_ne_bytes().to_vec(),
    }
}

fn call(dst: u16, row: &str, arguments: &[u16]) -> I {
    let row = EXTERN_ROWS.iter().find(|entry| entry.id == row).unwrap();
    let contract = Ownership::parse(row.ownership).unwrap();
    I::Intrinsic {
        dst: r(dst),
        row: row.id.to_owned(),
        args: arguments.iter().copied().map(r).collect(),
        argument_ownership: contract
            .argument_ownership(arguments.len())
            .unwrap()
            .into_iter()
            .map(|value| match value {
                ContractArgument::Borrowed => A::Borrowed,
                ContractArgument::Owned => A::Owned,
                ContractArgument::Scalar => A::Scalar,
                ContractArgument::Unique => A::Unique,
            })
            .collect(),
        result_ownership: match contract.result_ownership().unwrap() {
            ContractResult::Owned => R::Owned,
            ContractResult::Borrowed => R::Borrowed,
            ContractResult::Scalar => R::Scalar,
            ContractResult::RawObject => R::RawObject,
        },
    }
}

fn replay(code: Vec<I>) -> ValidatedProgram {
    let validated = flbc::validate(Program::new(
        FunctionId::new(0),
        vec![Function {
            id: FunctionId::new(0),
            arity: 0,
            parameter_ownership: Vec::new(),
            result_ownership: C::Erased,
            register_count: 32,
            code,
        }],
    ))
    .unwrap();
    let bytes = flbc::encode_canonical(&validated, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap(),
        bytes
    );
    decoded
}

fn returned(program: &ValidatedProgram) -> Obj {
    let outcome = execute(program, ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(result)) = outcome else {
        panic!("native FloatArray did not return: {outcome:?}");
    };
    result.value
}

fn packed(value: &Obj) -> Vec<u64> {
    let (width, size, _, bytes) = value.try_borrow_sarray_view().unwrap();
    assert_eq!(width, 8);
    assert_eq!(bytes.len(), size * 8);
    bytes
        .chunks_exact(8)
        .map(|word| u64::from_ne_bytes(word.try_into().unwrap()))
        .collect()
}

fn bits(value: &Obj) -> u64 {
    assert_eq!(value.header().tag, 0);
    assert_eq!(value.header().other, 0);
    value.try_ctor_scalar_u64(0).unwrap()
}

fn assert_clean_shadow() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "native FloatArray results and refusals retain no objects"
    );
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
    )));
}

fn input(values: &[u64]) -> Vec<I> {
    let mut code = vec![nat(0, 0), call(1, "extern:FloatArray.emptyWithCapacity", &[0])];
    for value in values {
        code.extend([wide(2, *value), call(1, "extern:FloatArray.push", &[1, 2])]);
    }
    code
}

#[test]
fn float_array_native_rows_preserve_values_aliases_and_owned_pushes() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    let original = [(-0.0f64).to_bits(), 1.25f64.to_bits(), 0x7ff8_0000_0000_0123];
    let mut code = input(&original);
    code.extend([
        I::Copy {
            dst: r(3),
            src: r(1),
        },
        wide(2, f64::INFINITY.to_bits()),
        call(1, "extern:FloatArray.push", &[1, 2]),
        call(4, "extern:FloatArray.size", &[1]),
        call(5, "extern:FloatArray.usize", &[3]),
        I::Copy {
            dst: r(6),
            src: r(1),
        },
        call(7, "extern:FloatArray.data", &[6]),
        I::Copy {
            dst: r(8),
            src: r(7),
        },
        call(9, "extern:FloatArray.mk", &[8]),
        I::Array {
            dst: r(10),
            items: vec![r(1), r(3), r(4), r(5), r(7), r(9)],
        },
        I::Return { src: r(10) },
    ]);
    let program = replay(code);
    for _ in 0..2 {
        let result = returned(&program);
        let updated = result.array_child(0);
        let snapshot = result.array_child(1);
        let expected = [original[0], original[1], original[2], f64::INFINITY.to_bits()];
        assert_eq!(packed(&updated), expected);
        assert_eq!(packed(&snapshot), original);
        assert_ne!(updated.identity_token(), snapshot.identity_token());
        assert_eq!(result.array_child(2).unbox(), 4);
        assert_eq!(bits(&result.array_child(3)), 3);
        let data = result.array_child(4);
        assert_eq!(data.array_view().0, expected.len());
        for (index, expected) in expected.into_iter().enumerate() {
            assert_eq!(bits(&data.array_child(index)), expected);
        }
        assert_eq!(packed(&result.array_child(5)), packed(&updated));
    }
    assert_clean_shadow();
}

#[test]
fn float_array_indexed_operations_keep_exact_bits_and_shared_predecessors() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for (set, get, usize_index) in [
        ("extern:FloatArray.set", "extern:FloatArray.get", false),
        ("extern:FloatArray.set!", "extern:FloatArray.get!", false),
        ("extern:FloatArray.uset", "extern:FloatArray.uget", true),
    ] {
        for replacement in [
            0,
            (-0.0f64).to_bits(),
            1,
            f64::INFINITY.to_bits(),
            f64::NEG_INFINITY.to_bits(),
            0x7ff8_0000_0000_0123,
        ] {
            let mut code = input(&[1.25f64.to_bits(), 2.5f64.to_bits()]);
            code.extend([
                I::Copy {
                    dst: r(3),
                    src: r(1),
                },
                if usize_index {
                    wide(4, 1)
                } else {
                    nat(4, 1)
                },
                wide(5, replacement),
                call(6, set, &[1, 4, 5]),
                call(7, get, &[6, 4]),
                call(8, get, &[3, 4]),
                I::Array {
                    dst: r(9),
                    items: vec![r(3), r(6), r(7), r(8)],
                },
                I::Return { src: r(9) },
            ]);
            let result = returned(&replay(code));
            assert_eq!(
                packed(&result.array_child(0)),
                [1.25f64.to_bits(), 2.5f64.to_bits()]
            );
            assert_eq!(packed(&result.array_child(1)), [1.25f64.to_bits(), replacement]);
            assert_eq!(bits(&result.array_child(2)), replacement);
            assert_eq!(bits(&result.array_child(3)), 2.5f64.to_bits());
        }
    }
    assert_clean_shadow();
}

#[test]
fn float_array_total_indexing_preserves_pin_out_of_bounds_defaults() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for index in [
        nat(4, 1),
        I::NatBig {
            dst: r(4),
            limbs_le: vec![0, 1],
        },
    ] {
        let mut code = input(&[(-0.0f64).to_bits()]);
        code.extend([
            I::Copy {
                dst: r(3),
                src: r(1),
            },
            index,
            wide(5, 1.0f64.to_bits()),
            call(6, "extern:FloatArray.get!", &[1, 4]),
            call(7, "extern:FloatArray.set!", &[1, 4, 5]),
            I::Array {
                dst: r(8),
                items: vec![r(3), r(6), r(7)],
            },
            I::Return { src: r(8) },
        ]);
        let result = returned(&replay(code));
        assert_eq!(
            bits(&result.array_child(1)),
            0,
            "off-array reads return positive zero"
        );
        assert_eq!(
            result.array_child(0).identity_token(),
            result.array_child(2).identity_token()
        );
        assert_eq!(packed(&result.array_child(2)), [(-0.0f64).to_bits()]);
    }
    assert_clean_shadow();
}

#[test]
fn float_array_proof_indexing_refuses_out_of_bounds_without_truncation() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for (row, setter, machine_index) in [
        ("extern:FloatArray.get", false, false),
        ("extern:FloatArray.set", true, false),
        ("extern:FloatArray.uget", false, true),
        ("extern:FloatArray.uset", true, true),
    ] {
        let mut code = input(&[1.25f64.to_bits()]);
        code.extend([
            if machine_index {
                wide(4, usize::MAX as u64)
            } else {
                I::NatBig {
                    dst: r(4),
                    limbs_le: vec![0, 1],
                }
            },
            wide(5, 2.5f64.to_bits()),
            call(6, row, if setter { &[1, 4, 5] } else { &[1, 4] }),
            I::Return { src: r(6) },
        ]);
        assert!(matches!(
            execute(&replay(code), ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::ArrayIndexOutOfBounds {
                    index: usize::MAX,
                    size: 1
                },
                ..
            })
        ));
    }
    assert_clean_shadow();
}

#[test]
fn float_array_rows_refuse_wrong_storage_scalar_kinds_and_ownership() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for bad_input in [
        vec![nat(1, 0)],
        vec![I::String {
            dst: r(1),
            value: "bytes".to_owned(),
        }],
        vec![I::Array {
            dst: r(1),
            items: vec![],
        }],
        vec![nat(0, 0), call(1, "extern:ByteArray.emptyWithCapacity", &[0])],
    ] {
        let mut code = bad_input;
        code.extend([
            call(3, "extern:FloatArray.size", &[1]),
            I::Return { src: r(3) },
        ]);
        assert!(matches!(
            execute(&replay(code), ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch {
                    expected: "FloatArray",
                    ..
                },
                ..
            })
        ));
    }
    for bad_float in [
        nat(2, 1),
        I::String {
            dst: r(2),
            value: "1.25".to_owned(),
        },
        I::Ctor {
            dst: r(2),
            tag: 1,
            fields: vec![],
            scalar_bytes: vec![0; 8],
        },
    ] {
        let mut code = input(&[]);
        code.extend([
            bad_float,
            call(3, "extern:FloatArray.push", &[1, 2]),
            I::Return { src: r(3) },
        ]);
        assert!(matches!(
            execute(&replay(code), ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch { .. },
                ..
            })
        ));
    }
    let malformed_array = replay(vec![
        wide(0, 1.25f64.to_bits()),
        nat(1, 3),
        I::Array {
            dst: r(2),
            items: vec![r(0), r(1)],
        },
        call(3, "extern:FloatArray.mk", &[2]),
        I::Return { src: r(3) },
    ]);
    assert!(matches!(
        execute(&malformed_array, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch { .. },
            ..
        })
    ));
    let mut wrong = call(3, "extern:FloatArray.push", &[1, 2]);
    let I::Intrinsic {
        argument_ownership, ..
    } = &mut wrong
    else {
        unreachable!();
    };
    argument_ownership[0] = A::Borrowed;
    let mut code = input(&[]);
    code.extend([wide(2, 1.25f64.to_bits()), wrong, I::Return { src: r(3) }]);
    assert!(matches!(
        execute(&replay(code), ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::IntrinsicOwnershipMismatch { argument: 0, .. },
            ..
        })
    ));
    let mut retry = input(&[(-0.0f64).to_bits(), 0x7ff8_0000_0000_0123]);
    retry.push(I::Return { src: r(1) });
    assert_eq!(
        packed(&returned(&replay(retry))),
        [(-0.0f64).to_bits(), 0x7ff8_0000_0000_0123]
    );
    assert_clean_shadow();
}
