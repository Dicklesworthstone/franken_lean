//! Exact tagged-scalar discrimination through FIR, ownership, wire, and Golem.
#![forbid(unsafe_code)]

use fln_comp::{fir, flbc};
use fln_core::outcome::Outcome;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, nat_decimal};

fn r(index: u16) -> flbc::Register {
    flbc::Register::new(index)
}

fn program(code: Vec<flbc::Instruction>, registers: u16, owned: bool) -> flbc::Program {
    flbc::Program::new(
        flbc::FunctionId::new(0),
        vec![flbc::Function {
            id: flbc::FunctionId::new(0),
            arity: 0,
            parameter_ownership: Vec::new(),
            result_ownership: if owned {
                flbc::CallableResultOwnership::Owned
            } else {
                flbc::CallableResultOwnership::Scalar
            },
            register_count: registers,
            code,
        }],
    )
}

fn replays(source: flbc::Program) -> [flbc::ValidatedProgram; 2] {
    let checked = flbc::validate(source).unwrap();
    let owned = flbc::insert_ownership(&checked, flbc::OwnershipLimits::default()).unwrap();
    let bytes = flbc::encode_canonical(owned.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    [owned.into_program(), replay]
}

fn returned(program: &flbc::ValidatedProgram) -> fln_rt::obj::Obj {
    let outcome = execute(program, ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(result)) = outcome else {
        panic!("{outcome:?}")
    };
    result.value
}

#[test]
fn scalar_tag_tests_never_treat_a_heap_payload_as_a_scalar() {
    use flbc::Instruction as I;
    for (input, tag, expected) in [
        (
            I::Nat {
                dst: r(0),
                value: 7,
            },
            7,
            "1",
        ),
        (
            I::Nat {
                dst: r(0),
                value: 7,
            },
            8,
            "0",
        ),
        (
            I::Nat {
                dst: r(0),
                value: 256,
            },
            256,
            "1",
        ),
        (
            I::Nat {
                dst: r(0),
                value: 0,
            },
            u64::MAX,
            "0",
        ),
        (
            I::NatBig {
                dst: r(0),
                limbs_le: vec![u64::MAX],
            },
            u64::MAX,
            "0",
        ),
        (
            I::Ctor {
                dst: r(0),
                tag: 7,
                fields: Vec::new(),
                scalar_bytes: Vec::new(),
            },
            7,
            "0",
        ),
        (
            I::String {
                dst: r(0),
                value: "λ\0🙂".to_owned(),
            },
            0,
            "0",
        ),
        (
            I::Array {
                dst: r(0),
                items: Vec::new(),
            },
            0,
            "0",
        ),
    ] {
        let source = program(
            vec![
                input,
                I::ScalarTagTest {
                    dst: r(1),
                    src: r(0),
                    expected_tag: tag,
                },
                I::Return { src: r(1) },
            ],
            2,
            false,
        );
        for replay in replays(source) {
            assert_eq!(nat_decimal(&returned(&replay)).as_deref(), Some(expected));
        }
    }
}

#[test]
fn scalar_tag_tests_borrow_before_replacing_an_aliased_register() {
    use flbc::Instruction as I;
    let source = program(
        vec![
            I::String {
                dst: r(0),
                value: "retained λ\0🙂".to_owned(),
            },
            I::Copy {
                dst: r(1),
                src: r(0),
            },
            I::ScalarTagTest {
                dst: r(0),
                src: r(0),
                expected_tag: 0,
            },
            I::Array {
                dst: r(2),
                items: vec![r(0), r(1)],
            },
            I::Return { src: r(2) },
        ],
        3,
        true,
    );
    for replay in replays(source) {
        let result = returned(&replay);
        assert_eq!(nat_decimal(&result.array_child(0)).as_deref(), Some("0"));
        assert_eq!(
            result.array_child(1).string_view().3,
            "retained λ\0🙂\0".as_bytes()
        );
        let stopped = execute(
            &replay,
            ExecutionLimits {
                max_steps: 2,
                ..ExecutionLimits::default()
            },
            None,
        );
        assert!(matches!(stopped, Outcome::Inconclusive(_)));
        assert_eq!(
            returned(&replay).array_child(1).string_view().3,
            "retained λ\0🙂\0".as_bytes()
        );
    }
}

#[test]
fn scalar_tag_tests_validate_registers_and_keep_old_artifacts_distinct() {
    use flbc::Instruction as I;
    let valid = program(
        vec![
            I::Nat {
                dst: r(0),
                value: 0,
            },
            I::ScalarTagTest {
                dst: r(1),
                src: r(0),
                expected_tag: 0,
            },
            I::Return { src: r(1) },
        ],
        2,
        false,
    );
    let mut uninitialized = valid.clone();
    uninitialized.functions[0].code[0] = I::ScalarTagTest {
        dst: r(0),
        src: r(1),
        expected_tag: 0,
    };
    assert!(matches!(
        flbc::validate(uninitialized),
        Err(flbc::ValidationError::ReadBeforeWrite { .. })
    ));
    let mut out_of_bounds = valid.clone();
    out_of_bounds.functions[0].code[1] = I::ScalarTagTest {
        dst: r(2),
        src: r(0),
        expected_tag: 0,
    };
    assert!(matches!(
        flbc::validate(out_of_bounds),
        Err(flbc::ValidationError::RegisterOutOfBounds { .. })
    ));
    let mut obsolete = valid.clone();
    obsolete.schema_version = flbc::FLBC_SCHEMA_VERSION - 1;
    assert!(matches!(
        flbc::validate(obsolete),
        Err(flbc::ValidationError::UnsupportedVersion { .. })
    ));
    for replay in replays(valid) {
        assert_eq!(nat_decimal(&returned(&replay)).as_deref(), Some("1"));
    }
}

fn fir_program() -> fir::Program {
    use fir::{
        Binding, Block, BlockId, Function, FunctionId, Operation, ValueId as V, ValueType as T,
    };
    fir::Program::new(
        FunctionId::new(0),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![Function {
            id: FunctionId::new(0),
            parameters: Vec::new(),
            parameter_ownership: Vec::new(),
            result: T::Bool,
            result_ownership: flbc::CallableResultOwnership::Scalar,
            blocks: vec![Block {
                id: BlockId::new(0),
                bindings: vec![
                    Binding {
                        id: V::new(0),
                        ty: T::String,
                        operation: Operation::String("unused before renumber".to_owned()),
                    },
                    Binding {
                        id: V::new(1),
                        ty: T::Nat,
                        operation: Operation::Nat(256),
                    },
                    Binding {
                        id: V::new(2),
                        ty: T::Abi,
                        operation: Operation::Box(V::new(1)),
                    },
                    Binding {
                        id: V::new(3),
                        ty: T::Bool,
                        operation: Operation::ScalarTagTest {
                            value: V::new(2),
                            tag: 256,
                        },
                    },
                ],
                terminator: fir::Terminator::Return { value: V::new(3) },
            }],
        }],
    )
}

#[test]
fn fir_scalar_tag_tests_survive_optimization_lowering_and_wire_replay() {
    let checked = fir::validate(fir_program(), fir::ValidationLimits::default()).unwrap();
    assert!(
        checked
            .canonical_text()
            .contains("scalar-tag-test v2 tag=256")
    );
    for checked in [
        checked.clone(),
        fir::optimize(&checked, fir::ValidationLimits::default()).unwrap(),
    ] {
        let owned =
            fir::lower_to_flbc_with_ownership(&checked, flbc::OwnershipLimits::default()).unwrap();
        assert!(
            owned.program().functions()[0]
                .code
                .iter()
                .any(|instruction| matches!(
                    instruction,
                    flbc::Instruction::ScalarTagTest {
                        expected_tag: 256,
                        ..
                    }
                ))
        );
        let bytes = flbc::encode_canonical(owned.program(), flbc::CodecLimits::default()).unwrap();
        let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
        assert_eq!(nat_decimal(&returned(&replay)).as_deref(), Some("1"));
    }
}

#[test]
fn fir_scalar_tag_tests_preserve_type_dominance_and_budget_refusals() {
    use fir::{Operation, ValueId as V, ValueType as T};
    let mut wrong_input = fir_program();
    wrong_input.functions[0].blocks[0].bindings[3].operation = Operation::ScalarTagTest {
        value: V::new(1),
        tag: 256,
    };
    assert!(matches!(
        fir::validate(wrong_input, fir::ValidationLimits::default()),
        Err(fir::ValidationError::ScalarTagTestOperandType { actual: T::Nat, .. })
    ));
    let mut wrong_output = fir_program();
    wrong_output.functions[0].blocks[0].bindings[3].ty = T::Nat;
    assert!(matches!(
        fir::validate(wrong_output, fir::ValidationLimits::default()),
        Err(fir::ValidationError::BindingType {
            declared: T::Nat,
            inferred: T::Bool,
            ..
        })
    ));
    let mut uninitialized = fir_program();
    uninitialized.functions[0].blocks[0].bindings[3].operation = Operation::ScalarTagTest {
        value: V::new(4),
        tag: 256,
    };
    uninitialized.functions[0].blocks[0]
        .bindings
        .push(fir::Binding {
            id: V::new(4),
            ty: T::Abi,
            operation: Operation::Alias(V::new(2)),
        });
    assert!(matches!(
        fir::validate(uninitialized, fir::ValidationLimits::default()),
        Err(fir::ValidationError::ReadBeforeDefinition { .. })
    ));
    let limits = fir::ValidationLimits {
        max_operations: 0,
        ..fir::ValidationLimits::default()
    };
    assert!(
        fir::validate(fir_program(), limits)
            .unwrap_err()
            .is_resource_exhaustion()
    );
    fir::validate(fir_program(), fir::ValidationLimits::default()).unwrap();
}
