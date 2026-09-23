//! The compiler's empty branch has no returning path, including after replay.
#![forbid(unsafe_code)]
use fln_comp::{fir, flbc, ingress};
use fln_core::{
    expr::{Expr, Literal, NatLit},
    name::Name,
    outcome::Outcome,
};
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute};
fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn constant(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}
fn compile(
    cases: &[ingress::EmptyCaseBinding],
    source: &Expr,
    limits: ingress::IngressLimits,
) -> Result<ingress::IngressedProgram, ingress::IngressError> {
    ingress::lower_closed_expr_with_closure_interfaces(
        source,
        &[ingress::ScalarConstructorBinding {
            name: name("false"),
            universe_arity: 0,
            value: false,
        }],
        &[],
        &[ingress::ConstructorBinding {
            name: name("object"),
            universe_arity: 0,
            tag: 0,
            fields: vec![],
            projection_structure: None,
            static_scalar_bytes: vec![],
        }],
        ingress::CallableBindings {
            empty_cases: cases,
            ..Default::default()
        },
        &[ingress::ClosureSignature {
            parameters: vec![fir::ValueType::Nat],
            parameter_ownership: vec![flbc::ArgumentOwnership::Borrowed],
            result: fir::ValueType::Nat,
            result_ownership: flbc::CallableResultOwnership::OwnedOrScalar,
        }],
        limits,
    )
}
fn case() -> ingress::EmptyCaseBinding {
    ingress::EmptyCaseBinding {
        name: name("empty"),
        major: fir::ValueType::Bool,
        result: fir::ValueType::Nat,
    }
}
#[test]
fn every_result_representation_panics_instead_of_returning_a_dummy_value() {
    for (major, value) in [
        (fir::ValueType::Bool, "false"),
        (fir::ValueType::Constructor, "object"),
    ] {
        for result in [
            fir::ValueType::Nat,
            fir::ValueType::Bool,
            fir::ValueType::String,
            fir::ValueType::Constructor,
            fir::ValueType::Closure(fir::ClosureTypeId::new(0)),
        ] {
            let source = Expr::app(constant("empty"), constant(value));
            let binding = ingress::EmptyCaseBinding {
                major,
                result,
                ..case()
            };
            let compiled = compile(&[binding], &source, ingress::IngressLimits::default()).unwrap();
            let bytecode = fir::lower_to_flbc(compiled.fir()).unwrap();
            let owned =
                flbc::insert_ownership(&bytecode, flbc::OwnershipLimits::default()).unwrap();
            let bytes =
                flbc::encode_canonical(owned.program(), flbc::CodecLimits::default()).unwrap();
            let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
            assert_eq!(
                flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
                bytes
            );
            let Outcome::Complete(VmExit::Panicked { message, .. }) =
                execute(&replay, ExecutionLimits::default(), None)
            else {
                panic!("empty elimination must not return a value");
            };
            assert_eq!(message, "empty elimination: unreachable branch reached");
        }
    }
}
#[test]
fn empty_binding_collisions_and_unrepresentable_majors_fail_closed() {
    let source = Expr::app(constant("empty"), constant("false"));
    for cases in [
        vec![case(), case()],
        vec![ingress::EmptyCaseBinding {
            name: name("false"),
            ..case()
        }],
        vec![ingress::EmptyCaseBinding {
            name: name("object"),
            ..case()
        }],
        vec![ingress::EmptyCaseBinding {
            name: Name::anonymous(),
            ..case()
        }],
        vec![ingress::EmptyCaseBinding {
            major: fir::ValueType::Nat,
            ..case()
        }],
        vec![ingress::EmptyCaseBinding {
            result: fir::ValueType::Closure(fir::ClosureTypeId::new(999)),
            ..case()
        }],
    ] {
        assert!(compile(&cases, &source, ingress::IngressLimits::default()).is_err());
    }
}
#[test]
fn empty_binding_does_not_relax_argument_or_universe_validation() {
    for source in [
        constant("empty"),
        Expr::app(
            constant("empty"),
            Expr::lit(Literal::Nat(NatLit::from_u64(0))),
        ),
        Expr::app(
            Expr::const_(name("empty"), vec![fln_core::level::Level::zero()]),
            constant("false"),
        ),
        Expr::app(
            Expr::app(constant("empty"), constant("false")),
            constant("false"),
        ),
    ] {
        assert!(compile(&[case()], &source, ingress::IngressLimits::default()).is_err());
    }
}
#[test]
fn empty_code_generation_remains_bounded_and_recovers() {
    let source = Expr::app(constant("empty"), constant("false"));
    let mut limits = [ingress::IngressLimits::default(); 5];
    limits[0].max_context_depth = 0;
    limits[1].max_literal_bytes = 0;
    limits[2].fir.max_functions = 1;
    limits[3].fir.max_blocks = 0;
    limits[4].max_nodes = 0;
    for bounded in limits {
        assert!(compile(&[case()], &source, bounded).is_err());
    }
    assert!(compile(&[case()], &source, ingress::IngressLimits::default()).is_ok());
}
