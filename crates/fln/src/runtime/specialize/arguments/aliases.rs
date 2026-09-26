//! Returning an initializer through an identity let is not a new call stage.
use super::*;

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn ty(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}
fn binder(domain: Expr, body: Expr, lambda: bool) -> Expr {
    if lambda {
        Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
    } else {
        Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
    }
}
fn generic(lambda: bool) -> Expr {
    binder(
        Expr::sort(Level::one()),
        binder(b(0), b(u32::from(!lambda)), lambda),
        lambda,
    )
}
fn returned(type_: Expr, initializer: Expr) -> Expr {
    Expr::let_e(name("callback"), type_, initializer, b(0), false)
}

#[test]
fn returned_polymorphic_initializers_keep_strict_work_and_its_outer_capture() {
    let poly_type = generic(false);
    let type_ = binder(ty("Nat"), poly_type.clone(), false);
    let work = Expr::app(ty("observe"), b(0));
    let value = binder(
        ty("Nat"),
        returned(
            poly_type,
            Expr::let_e(name("paid"), ty("Nat"), work.clone(), generic(true), false),
        ),
        true,
    );
    let environment = Environment::new();
    let result = Preparation::new(&environment, IngressLimits::default())
        .specialize_arguments(type_, value, &[nat::literal(7), ty("Nat"), nat::literal(42)])
        .unwrap();
    assert_eq!(
        result.type_,
        binder(ty("Nat"), binder(ty("Nat"), ty("Nat"), false), false)
    );
    assert_eq!(
        result.value,
        binder(
            ty("Nat"),
            Expr::let_e(
                name("paid"),
                ty("Nat"),
                work,
                binder(ty("Nat"), b(0), true),
                false,
            ),
            true,
        )
    );
    assert_eq!(result.static_arguments, vec![(1, ty("Nat"))]);
    assert_eq!(
        result.runtime_arguments,
        vec![nat::literal(7), nat::literal(42)]
    );
    assert!(!result.value.has_loose_bvars());
}

#[test]
fn returning_a_computed_callback_does_not_execute_it_during_specialization() {
    let type_ = generic(false);
    let value = returned(
        type_.clone(),
        Expr::app(ty("computeCallback"), nat::literal(9)),
    );
    let environment = Environment::new();
    let result = Preparation::new(&environment, IngressLimits::default())
        .specialize_arguments(type_.clone(), value.clone(), &[ty("Nat")])
        .unwrap();
    assert!(result.static_arguments.is_empty());
    assert_eq!(result.value, value);
    assert_eq!(result.type_, type_);
}

#[test]
fn a_return_of_an_earlier_binding_does_not_drop_intervening_strict_work() {
    let type_ = generic(false);
    let value = Expr::let_e(
        name("callback"),
        type_.clone(),
        generic(true),
        Expr::let_e(
            name("paid"),
            ty("Nat"),
            Expr::app(ty("observe"), nat::literal(9)),
            b(1),
            false,
        ),
        false,
    );
    let environment = Environment::new();
    let result = Preparation::new(&environment, IngressLimits::default())
        .specialize_arguments(type_.clone(), value.clone(), &[ty("Nat")])
        .unwrap();
    assert!(result.static_arguments.is_empty());
    assert_eq!(result.value, value);
    assert_eq!(result.type_, type_);
}

#[test]
fn deep_return_aliases_are_iterative_and_charge_the_shared_work_budget() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let type_ = generic(false);
            let mut value = generic(true);
            for _ in 0..2000 {
                value = returned(type_.clone(), value);
            }
            let environment = Environment::new();
            let result = Preparation::new(&environment, IngressLimits::default())
                .specialize_arguments(type_.clone(), value.clone(), &[ty("Nat")])
                .unwrap();
            assert_eq!(result.type_, binder(ty("Nat"), ty("Nat"), false));
            assert_eq!(result.value, binder(ty("Nat"), b(0), true));
            let limits = IngressLimits {
                max_nodes: 16,
                ..IngressLimits::default()
            };
            let mut bounded = Preparation::new(&environment, limits);
            assert!(matches!(
                bounded.specialize_arguments(type_, value, &[ty("Nat")]),
                Err(IngressError::ResourceLimit { .. })
            ));
            assert!(bounded.specializations.definitions.is_empty());
            assert!(bounded.specializations.instances.is_empty());
        })
        .unwrap()
        .join()
        .unwrap();
}
