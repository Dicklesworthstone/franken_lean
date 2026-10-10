use super::*;
use fln_core::expr::{BinderInfo, NatLit};

fn nat(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn lambda(parameter: &str, body: Expr) -> Expr {
    Expr::lam(
        Name::from_components(["major"]),
        Expr::const_(Name::from_components([parameter]), vec![]),
        body,
        BinderInfo::Default,
    )
}

fn lambda_binding(lambda: Expr, parameter: fir::ValueType) -> LambdaBinding {
    LambdaBinding {
        lambda,
        parameters: vec![parameter],
        parameter_ownership: vec![ArgumentOwnership::Borrowed],
        result: fir::ValueType::Nat,
        result_ownership: default_callable_result_ownership(fir::ValueType::Nat),
        recursion: LambdaRecursion::NonRecursive,
    }
}

#[derive(Clone)]
struct Fixture {
    name: Name,
    major: Expr,
    zero: Expr,
    successor: Expr,
    bool_branch: Expr,
    lambdas: Vec<LambdaBinding>,
    functions: Vec<FunctionBinding>,
    bool_cases: Vec<BoolCaseBinding>,
    nat_cases: Vec<NatCaseBinding>,
}

impl Fixture {
    fn new(major: Expr) -> Self {
        let name = Name::from_components(["choose"]);
        let zero = lambda("Nat", nat(17));
        // The successor branch returns the original major, not a synthetic
        // Boolean, zero, or predecessor supplied by the control operation.
        let successor = lambda("Nat", Expr::bvar(0).unwrap());
        let bool_branch = lambda("Bool", nat(23));
        Self {
            name: name.clone(),
            major,
            zero: zero.clone(),
            successor: successor.clone(),
            bool_branch: bool_branch.clone(),
            lambdas: vec![
                lambda_binding(zero, fir::ValueType::Nat),
                lambda_binding(successor, fir::ValueType::Nat),
            ],
            functions: vec![],
            bool_cases: vec![],
            nat_cases: vec![NatCaseBinding {
                name,
                result: fir::ValueType::Nat,
            }],
        }
    }

    fn compile(&self, limits: IngressLimits) -> Result<IngressedProgram, IngressError> {
        let source = [
            self.major.clone(),
            self.zero.clone(),
            self.successor.clone(),
        ]
        .into_iter()
        .fold(Expr::const_(self.name.clone(), vec![]), Expr::app);
        lower_closed_expr_with_control_flow(
            &source,
            &[ScalarConstructorBinding {
                name: Name::from_components(["false"]),
                universe_arity: 0,
                value: false,
            }],
            &[],
            &[],
            CallableBindings {
                functions: &self.functions,
                lambdas: &self.lambdas,
                bool_cases: &self.bool_cases,
                nat_cases: &self.nat_cases,
                ..CallableBindings::default()
            },
            limits,
        )
    }
}

#[test]
fn nat_cases_preserve_zero_nonzero_and_wide_majors_in_canonical_control_flow() {
    for major in [
        NatLit::from_u64(0),
        NatLit::from_u64(7),
        NatLit::from_u64(u64::MAX),
        NatLit::from_limbs_le(vec![0, 1]),
    ] {
        let fixture = Fixture::new(Expr::lit(Literal::Nat(major.clone())));
        let compiled = fixture.compile(IngressLimits::default()).unwrap();
        assert!(compiled.fir().intrinsics().is_empty());
        assert_eq!(compiled.work().intrinsic_calls, 0);
        assert_eq!(compiled.work().generated_functions, 4);

        let case = compiled
            .fir()
            .functions()
            .iter()
            .find(|function| function.parameters.len() == 3)
            .unwrap();
        assert_eq!(case.parameters[0], fir::ValueType::Nat);
        assert_eq!(case.parameter_ownership, [ArgumentOwnership::Borrowed; 3]);
        assert_eq!(case.result, fir::ValueType::Nat);
        assert_eq!(case.blocks.len(), 3);
        // No callback is applied before the selected basic block is entered.
        assert!(case.blocks[0].bindings.is_empty());
        assert_eq!(
            case.blocks[0].terminator,
            fir::Terminator::BranchZero {
                condition: fir::ValueId::new(0),
                zero: fir::BlockId::new(1),
                nonzero: fir::BlockId::new(2),
            }
        );
        for (block, closure) in case.blocks[1..].iter().zip([1, 2]) {
            assert_eq!(block.bindings.len(), 1);
            assert_eq!(
                block.bindings[0].operation,
                fir::Operation::Apply {
                    closure: fir::ValueId::new(closure),
                    args: vec![fir::ValueId::new(0)],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: default_callable_result_ownership(fir::ValueType::Nat),
                }
            );
        }

        let bytecode = fir::lower_to_flbc(compiled.fir()).unwrap();
        let bytes =
            crate::flbc::encode_canonical(&bytecode, crate::flbc::CodecLimits::default()).unwrap();
        let decoded =
            crate::flbc::decode_canonical(&bytes, crate::flbc::CodecLimits::default()).unwrap();
        assert_eq!(decoded, bytecode);
        assert_eq!(
            crate::flbc::encode_canonical(&decoded, crate::flbc::CodecLimits::default()).unwrap(),
            bytes
        );
        assert!(decoded.functions().iter().any(|function| {
            function.code.iter().any(|instruction| {
                matches!(instruction, crate::flbc::Instruction::JumpIfZero { .. })
            })
        }));
        assert!(decoded.functions().iter().any(|function| {
            function.code.iter().any(|instruction| match instruction {
                crate::flbc::Instruction::Nat { value, .. } => NatLit::from_u64(*value) == major,
                crate::flbc::Instruction::NatBig { limbs_le, .. } => {
                    NatLit::from_limbs_le(limbs_le.clone()) == major
                }
                _ => false,
            })
        }));
    }
}

#[test]
fn nat_cases_require_explicit_authority_and_share_callable_collision_checks() {
    let fixture = Fixture::new(nat(7));
    let mut missing = fixture.clone();
    missing.nat_cases.clear();
    assert!(matches!(
        missing.compile(IngressLimits::default()),
        Err(IngressError::UnknownConstant { name, .. }) if name == fixture.name
    ));

    let mut duplicate = fixture.clone();
    duplicate.nat_cases.push(duplicate.nat_cases[0].clone());
    assert!(matches!(
        duplicate.compile(IngressLimits::default()),
        Err(IngressError::DuplicateFunctionName {
            first: 0,
            second: 1,
            ..
        })
    ));

    let mut boolean = fixture.clone();
    boolean.lambdas.push(lambda_binding(
        boolean.bool_branch.clone(),
        fir::ValueType::Bool,
    ));
    boolean.bool_cases.push(BoolCaseBinding {
        name: fixture.name.clone(),
        result: fir::ValueType::Nat,
    });
    assert!(matches!(
        boolean.compile(IngressLimits::default()),
        Err(IngressError::DuplicateFunctionName {
            first: 0,
            second: 1,
            ..
        })
    ));

    let mut source_function = fixture.clone();
    source_function.functions.push(FunctionBinding {
        name: fixture.name.clone(),
        universe_arity: 0,
        parameters: vec![],
        parameter_ownership: vec![],
        result: fir::ValueType::Nat,
        result_ownership: default_callable_result_ownership(fir::ValueType::Nat),
        body: nat(0),
    });
    assert!(matches!(
        source_function.compile(IngressLimits::default()),
        Err(IngressError::DuplicateFunctionName {
            first: 0,
            second: 1,
            ..
        })
    ));
}

#[test]
fn nat_cases_refuse_mistyped_selectors_callbacks_and_incomplete_function_budgets() {
    let fixture = Fixture::new(nat(7));
    for major in [
        Expr::const_(Name::from_components(["false"]), vec![]),
        Expr::lit(Literal::Str("0".to_owned())),
    ] {
        let mut invalid = fixture.clone();
        invalid.major = major;
        assert!(matches!(
            invalid.compile(IngressLimits::default()),
            Err(IngressError::FunctionArgumentType {
                argument: 0,
                expected: fir::ValueType::Nat,
                ..
            })
        ));
    }
    for argument in [1, 2] {
        let mut invalid = fixture.clone();
        invalid.lambdas.push(lambda_binding(
            invalid.bool_branch.clone(),
            fir::ValueType::Bool,
        ));
        if argument == 1 {
            invalid.zero = invalid.bool_branch.clone();
        } else {
            invalid.successor = invalid.bool_branch.clone();
        }
        assert!(matches!(
            invalid.compile(IngressLimits::default()),
            Err(IngressError::FunctionArgumentType { argument: actual, .. }) if actual == argument
        ));
    }
    let mut invalid = fixture.clone();
    invalid.nat_cases[0].result = fir::ValueType::String;
    assert!(matches!(
        invalid.compile(IngressLimits::default()),
        Err(IngressError::UnsupportedNode {
            kind: "Nat case branch signature"
        })
    ));
    // Entry, the case function, and the two used branch lambdas require four
    // rows even though no source-defined ordinary function was supplied.
    let mut limits = IngressLimits::default();
    limits.fir.max_functions = 3;
    let error = fixture.compile(limits).unwrap_err();
    assert!(error.is_resource_exhaustion(), "{error:?}");
    fixture.compile(IngressLimits::default()).unwrap();
}
