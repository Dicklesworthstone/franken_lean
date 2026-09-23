//! Explicit compiler-owned control flow, not an extern or a kernel reduction.
use super::*;
use crate::flbc::ArgumentOwnership;

/// An untrusted binding for `name condition when_false when_true`.
///
/// Both branch arguments have the canonical closure signature `(Bool) -> result`.
/// The selector is passed as the closure's (normally ignored) argument. This
/// makes laziness explicit without a zero-arity application convention, phi
/// nodes, hidden effects, or a new runtime intrinsic. Names share the ordinary
/// callable collision checks. Source admission remains entirely the caller's job.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoolCaseBinding {
    pub name: Name,
    pub result: fir::ValueType,
}

/// All callable inputs to the expression compiler. Empty catalogs preserve the
/// previous compiler behavior; merely naming a case primitive grants no authority.
#[derive(Clone, Copy, Default)]
pub struct CallableBindings<'a> {
    pub functions: &'a [FunctionBinding],
    pub lambdas: &'a [LambdaBinding],
    pub bool_cases: &'a [BoolCaseBinding],
    pub constructor_cases: &'a [ConstructorCaseBinding],
    pub empty_cases: &'a [EmptyCaseBinding],
}

pub(super) fn prepare(
    catalog: &mut PreparedCatalog<'_>,
    cases: &[BoolCaseBinding],
    source_offset: usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    for (index, case) in cases.iter().enumerate() {
        let source_index = source_offset.saturating_add(index);
        if case.name.is_anonymous() {
            return Err(IngressError::AnonymousFunctionName {
                binding: source_index,
            });
        }
        if is_check_system_name(&case.name) {
            return Err(IngressError::CheckSystemFunctionNameCollision {
                binding: source_index,
            });
        }
        charge(IngressResource::ContextDepth, 3, limits.max_context_depth)?;
        let ownership = default_callable_result_ownership(case.result);
        let closure = catalog
            .closure_types
            .iter()
            .find(|signature| {
                signature.parameters == [fir::ValueType::Bool]
                    && signature.parameter_ownership == [ArgumentOwnership::Borrowed]
                    && signature.result == case.result
                    && signature.result_ownership == ownership
            })
            .ok_or(IngressError::UnsupportedNode {
                kind: "Boolean case branch signature",
            })?;
        let parameters = vec![
            fir::ValueType::Bool,
            fir::ValueType::Closure(closure.id),
            fir::ValueType::Closure(closure.id),
        ];
        try_push(
            &mut catalog.functions,
            PreparedFunction {
                source_index,
                name: case.name.clone(),
                universe_arity: 0,
                id: fir::FunctionId::new(0),
                parameters,
                parameter_ownership: borrowed_argument_ownership(3)?,
                result: case.result,
                result_ownership: ownership,
                body: PreparedFunctionBody::BoolCase,
            },
            IngressResource::ProgramTables,
            limits.fir.max_functions.saturating_sub(1),
        )?;
    }
    Ok(())
}

pub(super) fn assemble(function: &PreparedFunction<'_>) -> Result<fir::Function, IngressError> {
    let selector = fir::ValueId::new(0);
    let mut blocks = Vec::new();
    blocks
        .try_reserve_exact(3)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: 3,
        })?;
    blocks.push(fir::Block {
        id: fir::BlockId::new(0),
        bindings: vec![],
        terminator: fir::Terminator::BranchZero {
            condition: selector,
            zero: fir::BlockId::new(1),
            nonzero: fir::BlockId::new(2),
        },
    });
    for branch in 1..=2 {
        let value = fir::ValueId::new(branch + 2);
        blocks.push(fir::Block {
            id: fir::BlockId::new(branch),
            bindings: vec![fir::Binding {
                id: value,
                ty: function.result,
                operation: fir::Operation::Apply {
                    closure: fir::ValueId::new(branch),
                    args: vec![selector],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: function.result_ownership,
                },
            }],
            terminator: fir::Terminator::Return { value },
        });
    }
    Ok(fir::Function {
        id: function.id,
        parameters: clone_types(&function.parameters)?,
        parameter_ownership: clone_argument_ownership(&function.parameter_ownership)?,
        result: function.result,
        result_ownership: function.result_ownership,
        blocks,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::{BinderInfo, NatLit};

    fn compile(
        cases: &[BoolCaseBinding],
        bad_condition: bool,
        limits: IngressLimits,
    ) -> Result<IngressedProgram, IngressError> {
        let nat = |n| Expr::lit(Literal::Nat(NatLit::from_u64(n)));
        let lambda = |n| {
            Expr::lam(
                Name::from_components(["ignored"]),
                Expr::const_(Name::from_components(["Bool"]), vec![]),
                nat(n),
                BinderInfo::Default,
            )
        };
        let no = lambda(17);
        let yes = lambda(23);
        let lambdas = [no.clone(), yes.clone()].map(|lambda| LambdaBinding {
            lambda,
            parameters: vec![fir::ValueType::Bool],
            parameter_ownership: vec![ArgumentOwnership::Borrowed],
            result: fir::ValueType::Nat,
            result_ownership: default_callable_result_ownership(fir::ValueType::Nat),
            recursion: LambdaRecursion::NonRecursive,
        });
        let condition = if bad_condition {
            nat(0)
        } else {
            Expr::const_(Name::from_components(["false"]), vec![])
        };
        let source = [condition, no, yes].into_iter().fold(
            Expr::const_(Name::from_components(["choose"]), vec![]),
            Expr::app,
        );
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
                functions: &[],
                lambdas: &lambdas,
                bool_cases: cases,
                constructor_cases: &[],
                empty_cases: &[],
            },
            limits,
        )
    }
    fn case() -> BoolCaseBinding {
        BoolCaseBinding {
            name: Name::from_components(["choose"]),
            result: fir::ValueType::Nat,
        }
    }
    #[test]
    fn lazy_cases_publish_cfg_and_roundtrip_validated_bytecode() {
        let result = compile(&[case()], false, IngressLimits::default()).unwrap();
        let bytes = crate::flbc::encode_canonical(
            &fir::lower_to_flbc(result.fir()).unwrap(),
            crate::flbc::CodecLimits::default(),
        )
        .unwrap();
        crate::flbc::decode_canonical(&bytes, crate::flbc::CodecLimits::default()).unwrap();
        assert_eq!(result.work().generated_functions, 4);
    }
    #[test]
    fn case_name_collisions_and_mistyped_conditions_are_refused() {
        assert!(matches!(
            compile(&[case(), case()], false, IngressLimits::default()),
            Err(IngressError::DuplicateFunctionName { .. })
        ));
        assert!(matches!(
            compile(&[case()], true, IngressLimits::default()),
            Err(IngressError::FunctionArgumentType { argument: 0, .. })
        ));
        let mut invalid = case();
        invalid.name = Name::anonymous();
        assert!(matches!(
            compile(&[invalid], false, IngressLimits::default()),
            Err(IngressError::AnonymousFunctionName { .. })
        ));
    }
    #[test]
    fn cases_require_matching_branch_signatures_and_respect_budgets() {
        let mut invalid = case();
        invalid.result = fir::ValueType::String;
        assert!(compile(&[invalid], false, IngressLimits::default()).is_err());
        let mut limits = IngressLimits::default();
        limits.fir.max_functions = 1;
        assert!(
            compile(&[case()], false, limits)
                .unwrap_err()
                .is_resource_exhaustion()
        );
        limits = IngressLimits::default();
        limits.fir.max_blocks = 2;
        assert!(
            compile(&[case()], false, limits)
                .unwrap_err()
                .is_resource_exhaustion()
        );
        // A constant without an explicit case binding remains unknown.
        assert!(matches!(
            compile(&[], false, IngressLimits::default()),
            Err(IngressError::UnknownConstant { .. })
        ));
    }
}
