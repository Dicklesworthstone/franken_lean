//! Structural producer controls; source tests separately exercise admission.
use super::*;
use fln_env::constants::{ConstantVal, ReducibilityHints};

fn nat() -> Expr {
    Expr::const_(name("Nat"), vec![])
}
fn b(index: usize) -> Expr {
    variable(index).unwrap()
}
fn pi(domain: Expr, result: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, result, BinderInfo::Default)
}
fn lam(label: &str, domain: Expr, body: Expr) -> Expr {
    Expr::lam(name(label), domain, body, BinderInfo::Default)
}
fn call(label: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter()
        .fold(Expr::const_(name(label), vec![]), Expr::app)
}
fn local(label: &str, value: Expr, body: Expr) -> Expr {
    Expr::let_e(name(label), nat(), value, body, false)
}
fn callback_type() -> Expr {
    pi(nat(), pi(nat(), nat()))
}
fn staged() -> Expr {
    lam(
        "x",
        nat(),
        local("paid", call("observe", [b(0)]), lam("y", nat(), b(1))),
    )
}
fn definition(safety: DefinitionSafety) -> DefinitionVal {
    DefinitionVal {
        base: ConstantVal {
            name: name("consume"),
            level_params: Vec::new(),
            type_: pi(nat(), pi(callback_type(), pi(nat(), nat()))),
        },
        value: lam(
            "first",
            nat(),
            lam(
                "callback",
                callback_type(),
                lam("last", nat(), Expr::app(Expr::app(b(1), b(2)), b(0))),
            ),
        ),
        hints: ReducibilityHints::Abbrev,
        safety,
        all: Vec::new(),
    }
}
fn environment(safety: DefinitionSafety) -> Environment {
    Environment::new()
        .add_decl(ConstantInfo::Defn(definition(safety)))
        .unwrap()
}
fn occurrences(input: &Expr, label: &str) -> usize {
    let mut work = vec![input.clone()];
    let mut found = 0;
    while let Some(expr) = work.pop() {
        match expr.node() {
            ExprNode::Const { name: n, .. } => found += usize::from(n == &name(label)),
            ExprNode::App { f, a } => {
                work.push(f.clone());
                work.push(a.clone());
            }
            ExprNode::Lam { body, .. } | ExprNode::MData { expr: body, .. } => {
                work.push(body.clone());
            }
            ExprNode::LetE { value, body, .. } => {
                work.push(value.clone());
                work.push(body.clone());
            }
            _ => {}
        }
    }
    found
}

#[test]
fn flat_literal_callbacks_keep_the_existing_catalog_path() {
    let environment = environment(DefinitionSafety::Safe);
    let flat = lam("x", nat(), lam("y", nat(), b(0)));
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .specialize_staged_callback(
                &call("consume", []),
                &[nat::literal(0), flat, nat::literal(1)]
            )
            .unwrap()
            .is_none()
    );
}

#[test]
fn specialization_keeps_ordered_runtime_arguments_and_the_literal_stage_boundary() {
    let environment = environment(DefinitionSafety::Safe);
    let callback = staged();
    let actual = Preparation::new(&environment, IngressLimits::default())
        .specialize_staged_callback(
            &call("consume", []),
            &[
                call("firstArgument", []),
                callback.clone(),
                call("lastArgument", []),
            ],
        )
        .unwrap()
        .unwrap();
    let expected = local(
        "first",
        call("firstArgument", []),
        local(
            "last",
            call("lastArgument", []),
            Expr::app(Expr::app(callback, b(1)), b(0)),
        ),
    );
    assert_eq!(actual, expected);
    assert_eq!(occurrences(&actual, "observe"), 1);
    assert_eq!(occurrences(&actual, "consume"), 0);
}

#[test]
fn open_callback_captures_are_lifted_across_retained_arguments_without_capture() {
    let environment = environment(DefinitionSafety::Safe);
    let callback = lam("x", nat(), local("paid", b(1), lam("y", nat(), b(1))));
    let actual = Preparation::new(&environment, IngressLimits::default())
        .specialize_staged_callback(&call("consume", []), &[b(0), callback.clone(), b(1)])
        .unwrap()
        .unwrap();
    let expected = local(
        "first",
        b(0),
        local(
            "last",
            b(2),
            Expr::app(
                Expr::app(callback.lift_loose(0, 2).unwrap(), b(1)),
                b(0),
            ),
        ),
    );
    assert_eq!(actual, expected);
}

#[test]
fn partial_consumers_return_a_typed_real_lambda_not_a_flat_interface_cast() {
    let environment = environment(DefinitionSafety::Safe);
    let actual = Preparation::new(&environment, IngressLimits::default())
        .specialize_staged_callback(&call("consume", []), &[nat::literal(9), staged()])
        .unwrap()
        .unwrap();
    let ExprNode::LetE { value, body, .. } = actual.node() else {
        panic!("strict prefix");
    };
    assert_eq!(value, &nat::literal(9));
    let ExprNode::LetE {
        type_, value, body, ..
    } = body.node()
    else {
        panic!("callback annotation");
    };
    assert_eq!(type_, &pi(nat(), nat()));
    assert!(matches!(value.node(), ExprNode::Lam { .. }));
    assert_eq!(body, &b(0));
    assert!(!actual.has_loose_bvars());
}

#[test]
fn computed_callback_operands_are_never_treated_as_literal_values() {
    let environment = environment(DefinitionSafety::Safe);
    let operand = Expr::let_e(
        name("paid"),
        nat(),
        call("observableInitializer", []),
        staged(),
        false,
    );
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .specialize_staged_callback(
                &call("consume", []),
                &[nat::literal(0), operand, nat::literal(1)]
            )
            .unwrap()
            .is_none()
    );
}

#[test]
fn specialization_never_crosses_a_strict_callee_stage_to_find_a_callback() {
    let mut declaration = definition(DefinitionSafety::Safe);
    let ExprNode::Lam { body, .. } = declaration.value.node() else {
        panic!("first binder");
    };
    declaration.value = lam(
        "first",
        nat(),
        local(
            "required",
            call("observe", [b(0)]),
            body.lift_loose(0, 1).unwrap(),
        ),
    );
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(declaration))
        .unwrap();
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .specialize_staged_callback(
                &call("consume", []),
                &[nat::literal(0), staged(), nat::literal(1)]
            )
            .unwrap()
            .is_none()
    );
}

#[test]
fn unsafe_definitions_and_universe_arity_errors_cannot_supply_callback_code() {
    for safety in [DefinitionSafety::Unsafe, DefinitionSafety::Partial] {
        let environment = environment(safety);
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .specialize_staged_callback(&call("consume", []), &[nat::literal(0), staged()])
                .unwrap()
                .is_none()
        );
    }
    let environment = environment(DefinitionSafety::Safe);
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .specialize_staged_callback(
                &Expr::const_(name("consume"), vec![Level::one()]),
                &[nat::literal(0), staged()]
            )
            .unwrap()
            .is_none()
    );
    assert!(
        Preparation::new(&Environment::new(), IngressLimits::default())
            .specialize_staged_callback(&call("consume", []), &[staged()])
            .unwrap()
            .is_none()
    );
}

#[test]
fn specialization_obeys_work_argument_and_retained_context_limits() {
    let environment = environment(DefinitionSafety::Safe);
    for limits in [
        IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        },
        IngressLimits {
            max_application_args: 1,
            ..IngressLimits::default()
        },
        IngressLimits {
            max_context_depth: 1,
            ..IngressLimits::default()
        },
    ] {
        assert!(matches!(
            Preparation::new(&environment, limits).specialize_staged_callback(
                &call("consume", []),
                &[nat::literal(0), staged(), nat::literal(1)],
            ),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
}
