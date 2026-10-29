//! Native constructor discrimination, lazy dispatch, ownership, and FLBC replay.
#![forbid(unsafe_code)]
use fln_comp::{fir, flbc, ingress};
use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute, nat_decimal};

fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn nat(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn constant(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}
fn literal_program(input: flbc::Instruction, tag: u8, fields: u16) -> flbc::Program {
    flbc::Program::new(
        flbc::FunctionId::new(0),
        vec![flbc::Function {
            id: flbc::FunctionId::new(0),
            arity: 0,
            parameter_ownership: vec![],
            result_ownership: flbc::CallableResultOwnership::Scalar,
            register_count: 2,
            code: vec![
                input,
                flbc::Instruction::CtorTest {
                    dst: flbc::Register::new(1),
                    src: flbc::Register::new(0),
                    expected_tag: tag,
                    expected_fields: fields,
                },
                flbc::Instruction::Return {
                    src: flbc::Register::new(1),
                },
            ],
        }],
    )
}
fn returned(program: &flbc::ValidatedProgram, expected: &str) {
    let Outcome::Complete(VmExit::Returned(value)) =
        execute(program, ExecutionLimits::default(), None)
    else {
        panic!("native execution must return")
    };
    assert_eq!(nat_decimal(&value.value).as_deref(), Some(expected));
}
#[test]
fn shape_predicate_is_total_borrowed_and_canonically_replayable() {
    for (input, tag, fields, expected) in [
        (
            flbc::Instruction::Ctor {
                dst: flbc::Register::new(0),
                tag: 7,
                fields: vec![],
                scalar_bytes: vec![],
            },
            7,
            0,
            "1",
        ),
        (
            flbc::Instruction::Ctor {
                dst: flbc::Register::new(0),
                tag: 7,
                fields: vec![],
                scalar_bytes: vec![],
            },
            6,
            0,
            "0",
        ),
        (
            flbc::Instruction::Ctor {
                dst: flbc::Register::new(0),
                tag: 7,
                fields: vec![],
                scalar_bytes: vec![],
            },
            7,
            1,
            "0",
        ),
        (
            flbc::Instruction::Nat {
                dst: flbc::Register::new(0),
                value: 7,
            },
            7,
            0,
            "0",
        ),
        (
            flbc::Instruction::String {
                dst: flbc::Register::new(0),
                value: "owned".to_owned(),
            },
            7,
            0,
            "0",
        ),
    ] {
        let program = flbc::validate(literal_program(input, tag, fields)).unwrap();
        let owned = flbc::insert_ownership(&program, flbc::OwnershipLimits::default()).unwrap();
        let bytes = flbc::encode_canonical(owned.program(), flbc::CodecLimits::default()).unwrap();
        let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
        assert_eq!(
            flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
            bytes
        );
        returned(&replay, expected);
    }
}
#[test]
fn malformed_tests_and_uninitialized_operands_are_rejected_before_execution() {
    let input = flbc::Instruction::Nat {
        dst: flbc::Register::new(0),
        value: 0,
    };
    assert!(flbc::validate(literal_program(input.clone(), 255, 0)).is_err());
    assert!(flbc::validate(literal_program(input.clone(), 0, u16::MAX)).is_err());
    let mut p = literal_program(input, 0, 0);
    p.functions[0].code[0] = flbc::Instruction::CtorTest {
        dst: flbc::Register::new(0),
        src: flbc::Register::new(1),
        expected_tag: 0,
        expected_fields: 0,
    };
    assert!(flbc::validate(p).is_err());
}
fn dispatch(
    selected: &str,
    cases: Vec<Name>,
    limits: ingress::IngressLimits,
) -> Result<ingress::IngressedProgram, ingress::IngressError> {
    let lambdas: Vec<_> = [17, 25]
        .into_iter()
        .map(|n| ingress::LambdaBinding {
            lambda: Expr::lam(
                name(&format!("branch{n}")),
                constant("Packet"),
                nat(n),
                BinderInfo::Default,
            ),
            parameters: vec![fir::ValueType::Constructor],
            parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed],
            result: fir::ValueType::Nat,
            result_ownership: flbc::CallableResultOwnership::OwnedOrScalar,
            recursion: ingress::LambdaRecursion::NonRecursive,
        })
        .collect();
    let source = [
        constant(selected),
        lambdas[0].lambda.clone(),
        lambdas[1].lambda.clone(),
    ]
    .into_iter()
    .fold(constant("cases"), Expr::app);
    let constructors: Vec<_> = [("Z", 7), ("A", 3), ("Other", 9)]
        .into_iter()
        .map(|(n, tag)| ingress::ConstructorBinding {
            name: name(n),
            universe_arity: 0,
            tag,
            fields: vec![],
            projection_structure: None,
            static_scalar_bytes: vec![],
        })
        .collect();
    ingress::lower_closed_expr_with_control_flow(
        &source,
        &[],
        &[],
        &constructors,
        ingress::CallableBindings {
            functions: &[],
            lambdas: &lambdas,
            bool_cases: &[],
            nat_cases: &[],
            empty_cases: &[],
            constructor_cases: &[ingress::ConstructorCaseBinding {
                name: name("cases"),
                constructors: cases,
                result: fir::ValueType::Nat,
            }],
        },
        limits,
    )
}
#[test]
fn constructor_branch_order_is_semantic_not_catalog_sort_order() {
    for (selected, expected) in [("Z", "17"), ("A", "25")] {
        let program = dispatch(
            selected,
            vec![name("Z"), name("A")],
            ingress::IngressLimits::default(),
        )
        .unwrap();
        let code = fir::lower_to_flbc(program.fir()).unwrap();
        returned(&code, expected);
        let bytes = flbc::encode_canonical(&code, flbc::CodecLimits::default()).unwrap();
        returned(
            &flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap(),
            expected,
        );
    }
}
#[test]
fn unmatched_runtime_objects_do_not_select_the_last_branch() {
    let program = dispatch(
        "Other",
        vec![name("Z"), name("A")],
        ingress::IngressLimits::default(),
    )
    .unwrap();
    let code = fir::lower_to_flbc(program.fir()).unwrap();
    assert!(matches!(
        execute(&code, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Panicked { .. })
    ));
}
#[test]
fn malformed_case_catalogs_and_explicit_resource_bounds_are_refused() {
    for cases in [
        vec![],
        vec![name("Z"), name("Z")],
        vec![name("Z"), name("Absent")],
    ] {
        assert!(dispatch("Z", cases, ingress::IngressLimits::default()).is_err());
    }
    let mut limits = ingress::IngressLimits::default();
    limits.fir.max_blocks = 4;
    assert!(
        dispatch("Z", vec![name("Z"), name("A")], limits)
            .unwrap_err()
            .is_resource_exhaustion()
    );
}

fn packed_register(index: u16) -> flbc::Register {
    flbc::Register::new(index)
}

fn packed_replays(
    code: Vec<flbc::Instruction>,
    result_ownership: flbc::CallableResultOwnership,
) -> (flbc::OwnershipProgram, flbc::ValidatedProgram) {
    let program = flbc::validate(flbc::Program::new(
        flbc::FunctionId::new(0),
        vec![flbc::Function {
            id: flbc::FunctionId::new(0),
            arity: 0,
            parameter_ownership: vec![],
            result_ownership,
            register_count: 32,
            code,
        }],
    ))
    .expect("valid packed constructor program");
    let owned = flbc::insert_ownership(&program, flbc::OwnershipLimits::default())
        .expect("checked packed ownership");
    let bytes = flbc::encode_canonical(owned.program(), flbc::CodecLimits::default())
        .expect("packed artifact encodes");
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default())
        .expect("independent packed replay validates");
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    (owned, replay)
}

fn packed_returned(program: &flbc::ValidatedProgram) -> fln_rt::obj::Obj {
    match execute(program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(value)) => value.value,
        other => panic!("packed constructor execution must return: {other:?}"),
    }
}

fn packed_integer_conversion(family: &str, method: &str, dst: u16, src: u16) -> flbc::Instruction {
    let (argument, result) = match method {
        "ofNat" => (
            flbc::ArgumentOwnership::Borrowed,
            flbc::ResultOwnership::Scalar,
        ),
        "toNat" => (
            flbc::ArgumentOwnership::Scalar,
            flbc::ResultOwnership::Owned,
        ),
        _ => unreachable!("test conversion is fixed"),
    };
    flbc::Instruction::Intrinsic {
        dst: packed_register(dst),
        row: format!("extern:{family}.{method}"),
        args: vec![packed_register(src)],
        argument_ownership: vec![argument],
        result_ownership: result,
    }
}

#[test]
fn packed_integer_fields_preserve_native_values_object_aliases_and_replay() {
    use flbc::{Instruction as I, PackedScalar, ScalarKind as K};
    let r = packed_register;
    let mut code = vec![
        I::String {
            dst: r(0),
            value: "shared payload".to_owned(),
        },
        I::Nat {
            dst: r(1),
            value: 0xa5,
        },
        I::Nat {
            dst: r(2),
            value: 0xbeef,
        },
        I::Nat {
            dst: r(3),
            value: 0x89ab_cdef,
        },
        I::NatBig {
            dst: r(4),
            limbs_le: vec![0xfedc_ba98_7654_3210],
        },
        packed_integer_conversion("UInt64", "ofNat", 5, 4),
        I::NatBig {
            dst: r(6),
            limbs_le: vec![0x8000_0000_0000_0001],
        },
        packed_integer_conversion("USize", "ofNat", 7, 6),
        I::CtorPacked {
            dst: r(8),
            tag: 7,
            fields: vec![r(0)],
            scalar_bytes: vec![0x5a; 24],
            scalars: vec![
                PackedScalar {
                    offset: 8,
                    kind: K::UInt64,
                    value: r(5),
                },
                PackedScalar {
                    offset: 16,
                    kind: K::USize,
                    value: r(7),
                },
                PackedScalar {
                    offset: 24,
                    kind: K::UInt32,
                    value: r(3),
                },
                PackedScalar {
                    offset: 28,
                    kind: K::UInt16,
                    value: r(2),
                },
                PackedScalar {
                    offset: 30,
                    kind: K::UInt8,
                    value: r(1),
                },
            ],
        },
        I::Copy {
            dst: r(9),
            src: r(8),
        },
    ];
    for (dst, offset, kind) in [
        (10, 8, K::UInt64),
        (11, 16, K::USize),
        (12, 24, K::UInt32),
        (13, 28, K::UInt16),
        (14, 30, K::UInt8),
        (15, 31, K::UInt8),
    ] {
        code.push(I::CtorScalar {
            dst: r(dst),
            src: r(8),
            offset,
            kind,
        });
    }
    code.extend([
        I::CtorFieldDynamic {
            dst: r(16),
            src: r(8),
            field: 0,
        },
        packed_integer_conversion("UInt64", "toNat", 17, 10),
        packed_integer_conversion("USize", "toNat", 18, 11),
        I::Array {
            dst: r(19),
            items: vec![
                r(17),
                r(18),
                r(12),
                r(13),
                r(14),
                r(15),
                r(16),
                r(0),
                r(9),
                r(5),
                r(7),
            ],
        },
        I::Return { src: r(19) },
    ]);
    let (owned, replay) = packed_replays(code, flbc::CallableResultOwnership::Owned);
    for program in [owned.program(), &replay] {
        let value = packed_returned(program);
        for (index, expected) in [
            0xfedc_ba98_7654_3210u64,
            0x8000_0000_0000_0001,
            0x89ab_cdef,
            0xbeef,
            0xa5,
            0x5a,
        ]
        .into_iter()
        .enumerate()
        {
            assert_eq!(
                nat_decimal(&value.array_child(index)),
                Some(expected.to_string())
            );
        }
        for index in [6, 7] {
            assert_eq!(
                value.array_child(index).string_view().3,
                b"shared payload\0"
            );
        }
        let original = value.array_child(8);
        assert_eq!(original.header().tag, 7);
        assert_eq!(original.ctor_child(0).string_view().3, b"shared payload\0");
        assert_eq!(original.try_ctor_scalar_u64(8), Some(0xfedc_ba98_7654_3210));
        assert_eq!(
            value.array_child(9).try_ctor_scalar_u64(0),
            Some(0xfedc_ba98_7654_3210)
        );
        assert_eq!(
            value.array_child(10).try_ctor_scalar_u64(0),
            Some(0x8000_0000_0000_0001)
        );
    }
}

#[test]
fn packed_subword_and_unaligned_projections_copy_before_releasing_the_parent() {
    use flbc::{Instruction as I, ScalarKind as K};
    let r = packed_register;
    for (kind, offset, expected) in [
        (K::UInt8, 23, 0x8f),
        (K::UInt16, 15, 0x8887),
        (K::UInt32, 13, 0x8887_8685),
        (K::UInt64, 11, 0x8a89_8887_8685_8483),
        (K::USize, 11, 0x8a89_8887_8685_8483),
    ] {
        let (owned, replay) = packed_replays(
            vec![
                I::String {
                    dst: r(0),
                    value: "released parent child".to_owned(),
                },
                I::Ctor {
                    dst: r(1),
                    tag: 3,
                    fields: vec![r(0)],
                    scalar_bytes: (0x80..0x90).collect(),
                },
                I::CtorScalar {
                    dst: r(1),
                    src: r(1),
                    offset,
                    kind,
                },
                I::Return { src: r(1) },
            ],
            flbc::CallableResultOwnership::Erased,
        );
        for program in [owned.program(), &replay] {
            let value = packed_returned(program);
            if kind.width() == 8 {
                assert_eq!(value.try_ctor_scalar_u64(0), Some(expected));
            } else {
                assert_eq!(nat_decimal(&value), Some(expected.to_string()));
            }
        }
    }
}

#[test]
fn packed_scalar_projection_reads_native_wide_boxes_without_layout_relabeling() {
    use flbc::{Instruction as I, ScalarKind as K};
    let r = packed_register;
    for (family, kind) in [("UInt64", K::UInt64), ("USize", K::USize)] {
        let (owned, replay) = packed_replays(
            vec![
                I::NatBig {
                    dst: r(0),
                    limbs_le: vec![u64::MAX],
                },
                packed_integer_conversion(family, "ofNat", 1, 0),
                I::CtorScalar {
                    dst: r(2),
                    src: r(1),
                    offset: 0,
                    kind,
                },
                packed_integer_conversion(family, "toNat", 3, 2),
                I::Return { src: r(3) },
            ],
            flbc::CallableResultOwnership::OwnedOrScalar,
        );
        for program in [owned.program(), &replay] {
            assert_eq!(
                nat_decimal(&packed_returned(program)),
                Some(u64::MAX.to_string())
            );
        }
    }
}

#[test]
fn packed_scalar_projection_refuses_wrong_objects_and_storage_boundaries() {
    use flbc::{Instruction as I, ScalarKind as K};
    let r = packed_register;
    for (mut code, offset, kind, storage_refusal) in [
        (
            vec![I::Nat {
                dst: r(1),
                value: 0,
            }],
            0,
            K::UInt8,
            false,
        ),
        (
            vec![I::String {
                dst: r(1),
                value: "not a constructor".to_owned(),
            }],
            0,
            K::UInt32,
            false,
        ),
        (
            vec![I::Array {
                dst: r(1),
                items: vec![],
            }],
            0,
            K::USize,
            false,
        ),
        (
            vec![I::Ctor {
                dst: r(1),
                tag: 0,
                fields: vec![],
                scalar_bytes: vec![],
            }],
            0,
            K::UInt8,
            true,
        ),
        (
            vec![
                I::Nat {
                    dst: r(0),
                    value: 3,
                },
                I::Ctor {
                    dst: r(1),
                    tag: 0,
                    fields: vec![r(0)],
                    scalar_bytes: vec![0; 8],
                },
            ],
            0,
            K::UInt8,
            true,
        ),
        (
            vec![
                I::Nat {
                    dst: r(0),
                    value: 3,
                },
                I::Ctor {
                    dst: r(1),
                    tag: 0,
                    fields: vec![r(0)],
                    scalar_bytes: vec![0; 8],
                },
            ],
            15,
            K::UInt16,
            true,
        ),
    ] {
        code.extend([
            I::CtorScalar {
                dst: r(2),
                src: r(1),
                offset,
                kind,
            },
            I::Return { src: r(2) },
        ]);
        let (owned, replay) = packed_replays(code, flbc::CallableResultOwnership::Erased);
        for program in [owned.program(), &replay] {
            let Outcome::Complete(VmExit::Refused { refusal, .. }) =
                execute(program, ExecutionLimits::default(), None)
            else {
                panic!("invalid scalar storage must refuse before reading")
            };
            if storage_refusal {
                assert!(matches!(refusal, VmRefusal::ConstructorScalarBounds { .. }));
            } else {
                assert!(matches!(refusal, VmRefusal::TypeMismatch { .. }));
            }
        }
    }
}

#[test]
fn packed_initialization_refuses_out_of_range_and_wrong_kind_scalars() {
    use flbc::{Instruction as I, PackedScalar, ScalarKind as K};
    let r = packed_register;
    for (mut code, kind, overflow) in [
        (
            vec![I::Nat {
                dst: r(1),
                value: 256,
            }],
            K::UInt8,
            true,
        ),
        (
            vec![I::Nat {
                dst: r(1),
                value: 65_536,
            }],
            K::UInt16,
            true,
        ),
        (
            vec![I::Nat {
                dst: r(1),
                value: 1 << 32,
            }],
            K::UInt32,
            true,
        ),
        (
            vec![I::String {
                dst: r(1),
                value: "not scalar bits".to_owned(),
            }],
            K::UInt64,
            false,
        ),
        (
            vec![
                I::Nat {
                    dst: r(0),
                    value: 7,
                },
                I::Ctor {
                    dst: r(1),
                    tag: 0,
                    fields: vec![r(0)],
                    scalar_bytes: vec![0; 8],
                },
            ],
            K::USize,
            false,
        ),
    ] {
        code.extend([
            I::CtorPacked {
                dst: r(2),
                tag: 0,
                fields: vec![],
                scalar_bytes: vec![0; kind.width()],
                scalars: vec![PackedScalar {
                    offset: 0,
                    kind,
                    value: r(1),
                }],
            },
            I::Return { src: r(2) },
        ]);
        let (owned, replay) = packed_replays(code, flbc::CallableResultOwnership::Owned);
        for program in [owned.program(), &replay] {
            let Outcome::Complete(VmExit::Refused { refusal, .. }) =
                execute(program, ExecutionLimits::default(), None)
            else {
                panic!("malformed scalar must not publish a packed constructor")
            };
            if overflow {
                assert!(matches!(refusal, VmRefusal::NatOverflow { .. }));
            } else {
                assert!(matches!(refusal, VmRefusal::TypeMismatch { .. }));
            }
        }
    }
}
