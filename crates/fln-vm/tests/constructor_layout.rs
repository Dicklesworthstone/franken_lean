//! Complete constructor layout guards survive ownership and canonical replay.
#![forbid(unsafe_code)]

use fln_comp::{fir, flbc};
use fln_core::outcome::Outcome;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, nat_decimal};

fn r(index: u16) -> flbc::Register {
    flbc::Register::new(index)
}

fn program(input: flbc::Instruction) -> flbc::Program {
    flbc::Program::new(
        flbc::FunctionId::new(0),
        vec![flbc::Function {
            id: flbc::FunctionId::new(0),
            arity: 0,
            parameter_ownership: vec![],
            result_ownership: flbc::CallableResultOwnership::Scalar,
            register_count: 3,
            code: vec![
                flbc::Instruction::String {
                    dst: r(0),
                    value: "retained child".into(),
                },
                input,
                flbc::Instruction::CtorLayoutTest {
                    dst: r(2),
                    src: r(1),
                    expected_tag: 7,
                    expected_fields: 1,
                    expected_scalar_bytes: 0,
                },
                flbc::Instruction::Return { src: r(2) },
            ],
        }],
    )
}

fn replays(program: flbc::Program) -> [flbc::ValidatedProgram; 2] {
    let checked = flbc::validate(program).unwrap();
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
    let result = execute(program, ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(value)) = result else {
        panic!("{result:?}")
    };
    value.value
}

#[test]
fn layout_guard_rejects_hidden_scalar_payloads_and_all_wrong_carriers() {
    use flbc::Instruction as I;
    for (input, expected) in [
        (
            I::Ctor {
                dst: r(1),
                tag: 7,
                fields: vec![r(0)],
                scalar_bytes: vec![],
            },
            "1",
        ),
        (
            I::Ctor {
                dst: r(1),
                tag: 6,
                fields: vec![r(0)],
                scalar_bytes: vec![],
            },
            "0",
        ),
        (
            I::Ctor {
                dst: r(1),
                tag: 7,
                fields: vec![],
                scalar_bytes: vec![],
            },
            "0",
        ),
        (
            I::Ctor {
                dst: r(1),
                tag: 7,
                fields: vec![r(0), r(0)],
                scalar_bytes: vec![],
            },
            "0",
        ),
        (
            I::Ctor {
                dst: r(1),
                tag: 7,
                fields: vec![r(0)],
                scalar_bytes: vec![0],
            },
            "0",
        ),
        (
            I::Ctor {
                dst: r(1),
                tag: 7,
                fields: vec![r(0)],
                scalar_bytes: vec![0; 16],
            },
            "0",
        ),
        (
            I::Nat {
                dst: r(1),
                value: 7,
            },
            "0",
        ),
        (
            I::NatBig {
                dst: r(1),
                limbs_le: vec![u64::MAX],
            },
            "0",
        ),
        (
            I::String {
                dst: r(1),
                value: "other heap kind".into(),
            },
            "0",
        ),
        (
            I::Array {
                dst: r(1),
                items: vec![r(0)],
            },
            "0",
        ),
    ] {
        for replay in replays(program(input)) {
            assert_eq!(nat_decimal(&returned(&replay)).as_deref(), Some(expected));
        }
    }
}

#[test]
fn layout_guard_borrows_and_checks_before_overwriting_its_input() {
    use flbc::Instruction as I;
    let mut source = program(I::Ctor {
        dst: r(1),
        tag: 7,
        fields: vec![r(0)],
        scalar_bytes: vec![],
    });
    source.functions[0].register_count = 4;
    source.functions[0].result_ownership = flbc::CallableResultOwnership::Owned;
    source.functions[0].code.insert(
        2,
        I::Copy {
            dst: r(3),
            src: r(1),
        },
    );
    source.functions[0].code[3] = I::CtorLayoutTest {
        dst: r(1),
        src: r(1),
        expected_tag: 7,
        expected_fields: 1,
        expected_scalar_bytes: 0,
    };
    source.functions[0].code[4] = I::Ctor {
        dst: r(2),
        tag: 0,
        fields: vec![r(1), r(3)],
        scalar_bytes: vec![],
    };
    source.functions[0].code.push(I::Return { src: r(2) });
    for replay in replays(source) {
        let result = returned(&replay);
        assert_eq!(
            nat_decimal(&result.try_ctor_child(0).unwrap()).as_deref(),
            Some("1")
        );
        let kept = result.try_ctor_child(1).unwrap();
        assert_eq!(kept.header().tag, 7);
        assert!(
            kept.try_ctor_child(0)
                .unwrap()
                .try_borrow_string_view()
                .is_some()
        );
    }
}

fn fir_program() -> fir::Program {
    use fir::{
        Binding, Block, BlockId, ConstructorDecl, ConstructorId, Function, FunctionId, Operation,
        ValueId as V, ValueType as T,
    };
    fir::Program::new(
        FunctionId::new(0),
        vec![ConstructorDecl {
            id: ConstructorId::new(0),
            tag: 7,
            fields: vec![T::String],
            static_scalar_bytes: vec![],
        }],
        vec![],
        vec![],
        vec![Function {
            id: FunctionId::new(0),
            parameters: vec![],
            parameter_ownership: vec![],
            result: T::Bool,
            result_ownership: flbc::CallableResultOwnership::Scalar,
            blocks: vec![Block {
                id: BlockId::new(0),
                bindings: vec![
                    Binding {
                        id: V::new(0),
                        ty: T::Nat,
                        operation: Operation::Nat(99),
                    },
                    Binding {
                        id: V::new(1),
                        ty: T::String,
                        operation: Operation::String("child".into()),
                    },
                    Binding {
                        id: V::new(2),
                        ty: T::Constructor,
                        operation: Operation::Ctor {
                            constructor: ConstructorId::new(0),
                            fields: vec![V::new(1)],
                        },
                    },
                    Binding {
                        id: V::new(3),
                        ty: T::Abi,
                        operation: Operation::Box(V::new(2)),
                    },
                    Binding {
                        id: V::new(4),
                        ty: T::Bool,
                        operation: Operation::CtorLayoutTest {
                            constructor: ConstructorId::new(0),
                            value: V::new(3),
                        },
                    },
                ],
                terminator: fir::Terminator::Return { value: V::new(4) },
            }],
        }],
    )
}

#[test]
fn layout_guard_survives_fir_optimization_lowering_and_replay() {
    let checked = fir::validate(fir_program(), fir::ValidationLimits::default()).unwrap();
    assert!(checked.canonical_text().contains("ctor-layout-test c0 v3"));
    for checked in [
        checked.clone(),
        fir::optimize(&checked, fir::ValidationLimits::default()).unwrap(),
    ] {
        let lowered =
            fir::lower_to_flbc_with_ownership(&checked, flbc::OwnershipLimits::default()).unwrap();
        assert!(
            lowered.program().functions()[0]
                .code
                .iter()
                .any(|instruction| matches!(
                    instruction,
                    flbc::Instruction::CtorLayoutTest {
                        expected_tag: 7,
                        expected_fields: 1,
                        expected_scalar_bytes: 0,
                        ..
                    }
                ))
        );
        let bytes =
            flbc::encode_canonical(lowered.program(), flbc::CodecLimits::default()).unwrap();
        let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
        assert_eq!(nat_decimal(&returned(&replay)).as_deref(), Some("1"));
    }
}

#[test]
fn invalid_layouts_and_untyped_operands_are_refused_before_execution() {
    use flbc::Instruction as I;
    for (tag, fields, scalars) in [(255, 1, 0), (7, u16::MAX, 0), (7, 1, u16::MAX)] {
        let mut invalid = program(I::Nat {
            dst: r(1),
            value: 0,
        });
        invalid.functions[0].code[2] = I::CtorLayoutTest {
            dst: r(2),
            src: r(1),
            expected_tag: tag,
            expected_fields: fields,
            expected_scalar_bytes: scalars,
        };
        assert!(flbc::validate(invalid).is_err());
    }
    let mut invalid = fir_program();
    invalid.functions[0].blocks[0].bindings[4].operation = fir::Operation::CtorLayoutTest {
        constructor: fir::ConstructorId::new(0),
        value: fir::ValueId::new(2),
    };
    assert!(matches!(
        fir::validate(invalid, fir::ValidationLimits::default()),
        Err(fir::ValidationError::ConstructorLayoutTestOperandType { .. })
    ));
    let mut invalid = fir_program();
    invalid.functions[0].blocks[0].bindings[4].operation = fir::Operation::CtorLayoutTest {
        constructor: fir::ConstructorId::new(1),
        value: fir::ValueId::new(3),
    };
    assert!(matches!(
        fir::validate(invalid, fir::ValidationLimits::default()),
        Err(fir::ValidationError::MissingConstructor { .. })
    ));
}
