//! Classification and substitution controls. Integration tests admit real source.
use super::*;

fn ty(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}
fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}
fn generic() -> (Expr, Expr) {
    (
        pi(Expr::sort(Level::one()), pi(b(0), b(1))),
        lam(Expr::sort(Level::one()), lam(b(0), b(0))),
    )
}
fn staged() -> (Expr, Expr) {
    (
        pi(ty("Nat"), pi(ty("Nat"), ty("Nat"))),
        lam(
            ty("Nat"),
            Expr::let_e(
                name("saved"),
                ty("Nat"),
                b(0),
                lam(ty("Nat"), b(1)),
                false,
            ),
        ),
    )
}
fn classify(value: &Expr, type_: &Expr) -> Option<Expr> {
    Preparation::new(&Environment::new(), IngressLimits::default())
        .local_callable_template(value, type_)
        .unwrap()
}

#[test]
fn local_type_parameters_are_templates_not_runtime_slots() {
    let (type_, value) = generic();
    assert_eq!(classify(&value, &type_), Some(value));
}

#[test]
fn static_parameters_after_runtime_binders_are_found() {
    let (type_, value) = generic();
    let type_ = pi(ty("Nat"), type_);
    let value = lam(ty("Nat"), value);
    assert_eq!(classify(&value, &type_), Some(value));
}

#[test]
fn type_constructor_arguments_are_static_without_evaluating_a_function_body() {
    let kind = pi(Expr::sort(Level::one()), Expr::sort(Level::one()));
    let value = lam(kind.clone(), lam(ty("Nat"), b(0)));
    let type_ = pi(kind, pi(ty("Nat"), ty("Nat")));
    assert_eq!(classify(&value, &type_), Some(value));
}

#[test]
fn literal_staged_helpers_are_exposed_but_flat_helpers_remain_shared() {
    let (type_, value) = staged();
    assert_eq!(classify(&value, &type_), Some(value));
    let flat = lam(ty("Nat"), lam(ty("Nat"), b(0)));
    assert!(classify(&flat, &type_).is_none());
    let ordinary = lam(ty("Nat"), b(0));
    assert!(classify(&ordinary, &pi(ty("Nat"), ty("Nat"))).is_none());
}

#[test]
fn computed_initializers_and_unknown_callees_are_never_substituted() {
    let (type_, value) = staged();
    let computed = Expr::let_e(
        name("required"),
        ty("Nat"),
        Expr::app(ty("observableInitializer"), b(0)),
        value,
        false,
    );
    assert!(classify(&computed, &type_).is_none());
    assert!(classify(&Expr::app(ty("makeCallback"), b(0)), &type_).is_none());
    assert!(classify(&b(0), &type_).is_none());
}

#[test]
fn capture_avoiding_substitution_reopens_an_outer_value_below_a_new_binder() {
    let type_ = pi(ty("Nat"), pi(ty("Nat"), ty("Nat")));
    let value = lam(
        ty("Nat"),
        Expr::let_e(
            name("saved"),
            ty("Nat"),
            b(1),
            lam(ty("Nat"), b(1)),
            false,
        ),
    );
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let literal = preparation
        .local_callable_template(&value, &type_)
        .unwrap()
        .unwrap();
    // The local helper occupied #0; the new caller lambda occupies #0 now.
    let body = lam(ty("Nat"), Expr::app(Expr::app(b(1), b(0)), b(2)));
    let actual = preparation.substitution(&body, &literal).unwrap();
    let expected = lam(
        ty("Nat"),
        Expr::app(
            Expr::app(value.lift_loose(0, 1).unwrap(), b(0)),
            b(1),
        ),
    );
    assert_eq!(actual, expected);
}

#[test]
fn unused_literal_bodies_are_not_run_during_selection_or_substitution() {
    let type_ = pi(ty("Nat"), pi(ty("Nat"), ty("Nat")));
    let value = lam(ty("Nat"), Expr::app(ty("observableProducer"), b(0)));
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let literal = preparation
        .local_callable_template(&value, &type_)
        .unwrap()
        .unwrap();
    assert_eq!(
        preparation
            .substitution(&nat::literal(42), &literal)
            .unwrap(),
        nat::literal(42)
    );
}

#[test]
fn a_long_telescope_uses_heap_iteration_and_refuses_small_budgets() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let (mut type_, mut value) = generic();
            for _ in 0..600 {
                type_ = pi(ty("Nat"), type_);
                value = lam(ty("Nat"), value);
            }
            let environment = Environment::new();
            for limits in [
                IngressLimits {
                    max_nodes: 0,
                    ..IngressLimits::default()
                },
                IngressLimits {
                    max_context_depth: 20,
                    ..IngressLimits::default()
                },
            ] {
                assert!(matches!(
                    Preparation::new(&environment, limits).local_callable_template(&value, &type_),
                    Err(IngressError::ResourceLimit { .. })
                ));
            }
            assert_eq!(classify(&value, &type_), Some(value));
        })
        .unwrap()
        .join()
        .unwrap();
}
