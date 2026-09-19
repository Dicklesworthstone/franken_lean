//! Standalone callback interfaces are untrusted and receive full FIR validation.
#![forbid(unsafe_code)]
use fln_comp::{
    fir::{self, ClosureTypeId, ValueType},
    flbc::{ArgumentOwnership, CallableResultOwnership},
    ingress::{
        CallableBindings, ClosureSignature, IngressLimits, LambdaBinding, LambdaRecursion,
        lower_closed_expr_with_closure_interfaces,
    },
};
use fln_core::{
    expr::{BinderInfo, Expr, Literal, NatLit},
    level::Level,
    name::Name,
};
fn interface() -> ClosureSignature {
    ClosureSignature {
        parameters: vec![ValueType::Nat],
        parameter_ownership: vec![ArgumentOwnership::Borrowed],
        result: ValueType::Nat,
        result_ownership: CallableResultOwnership::OwnedOrScalar,
    }
}
fn nat() -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(42)))
}

#[test]
fn callback_interface_needs_no_dummy_executable_lambda() {
    let source = Expr::lam(
        Name::from_components(["f"]),
        Expr::sort(Level::zero()),
        Expr::app(Expr::bvar(0).unwrap(), nat()),
        BinderInfo::Default,
    );
    let lambda = LambdaBinding {
        lambda: source.clone(),
        parameters: vec![ValueType::Closure(ClosureTypeId::new(0))],
        parameter_ownership: vec![ArgumentOwnership::Borrowed],
        result: ValueType::Nat,
        result_ownership: CallableResultOwnership::OwnedOrScalar,
        recursion: LambdaRecursion::NonRecursive,
    };
    let result = lower_closed_expr_with_closure_interfaces(
        &source,
        &[],
        &[],
        &[],
        CallableBindings {
            lambdas: &[lambda],
            ..CallableBindings::default()
        },
        &[interface()],
        IngressLimits::default(),
    )
    .unwrap();
    assert_eq!(result.fir().closure_types().len(), 2);
    assert!(fir::lower_to_flbc(result.fir()).is_ok());
}

#[test]
fn interface_order_and_duplicates_do_not_change_the_program() {
    let a = interface();
    let mut b = interface();
    b.parameters = vec![ValueType::String];
    let lower = |interfaces: &[ClosureSignature]| {
        lower_closed_expr_with_closure_interfaces(
            &nat(),
            &[],
            &[],
            &[],
            CallableBindings::default(),
            interfaces,
            IngressLimits::default(),
        )
        .unwrap()
    };
    assert_eq!(
        lower(&[a.clone(), b.clone()]).fir(),
        lower(&[b.clone(), a.clone(), a]).fir()
    );
}

#[test]
fn interfaces_retain_partial_application_suffixes() {
    let mut signature = interface();
    signature.parameters.push(ValueType::Nat);
    signature
        .parameter_ownership
        .push(ArgumentOwnership::Borrowed);
    let result = lower_closed_expr_with_closure_interfaces(
        &nat(),
        &[],
        &[],
        &[],
        CallableBindings::default(),
        &[signature],
        IngressLimits::default(),
    )
    .unwrap();
    assert_eq!(result.fir().closure_types().len(), 2);
}

#[test]
fn malformed_arity_ownership_and_type_references_are_refused() {
    let mut no_args = interface();
    no_args.parameters.clear();
    no_args.parameter_ownership.clear();
    let mut arity = interface();
    arity.parameter_ownership.clear();
    let mut ownership = interface();
    ownership.result = ValueType::String;
    ownership.result_ownership = CallableResultOwnership::Scalar;
    let mut dangling = interface();
    dangling.result = ValueType::Closure(ClosureTypeId::new(9));
    dangling.result_ownership = CallableResultOwnership::Owned;
    for malformed in [no_args, arity, ownership, dangling] {
        assert!(
            lower_closed_expr_with_closure_interfaces(
                &nat(),
                &[],
                &[],
                &[],
                CallableBindings::default(),
                &[malformed],
                IngressLimits::default()
            )
            .is_err()
        );
    }
}

#[test]
fn interface_tables_and_telescope_depth_remain_bounded() {
    for limits in [
        IngressLimits {
            fir: fir::ValidationLimits {
                max_closure_types: 0,
                ..fir::ValidationLimits::default()
            },
            ..IngressLimits::default()
        },
        IngressLimits {
            max_context_depth: 0,
            ..IngressLimits::default()
        },
    ] {
        let error = lower_closed_expr_with_closure_interfaces(
            &nat(),
            &[],
            &[],
            &[],
            CallableBindings::default(),
            &[interface()],
            limits,
        )
        .unwrap_err();
        assert!(error.is_resource_exhaustion());
    }
}
