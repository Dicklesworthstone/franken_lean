//! Native constructor discrimination, lazy dispatch, ownership, and FLBC replay.
#![forbid(unsafe_code)]
use fln_comp::{fir, flbc, ingress};
use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, nat_decimal};

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
