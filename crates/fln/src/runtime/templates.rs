//! Template classification is syntactic and never substitutes for admission.
use super::*;

fn scalar(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}
fn pi(domain: Expr, body: Expr, info: BinderInfo) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, info)
}
fn template(type_: Expr) -> bool {
    is_template(&DefinitionVal {
        base: ConstantVal {
            name: name("subject"),
            level_params: Vec::new(),
            type_,
        },
        value: nat::literal(0),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: Vec::new(),
    })
}

#[test]
fn later_type_and_dictionary_binders_are_templates() {
    let type_parameter = pi(
        Expr::sort(Level::one()),
        pi(
            Expr::bvar(0).unwrap(),
            Expr::bvar(1).unwrap(),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let dictionary = pi(
        scalar("Dictionary"),
        scalar("Nat"),
        BinderInfo::InstImplicit,
    );
    for suffix in [type_parameter, dictionary] {
        assert!(template(pi(scalar("Nat"), suffix, BinderInfo::Default)));
    }
}

#[test]
fn type_producing_functions_are_not_run_as_scalar_programs() {
    assert!(template(pi(
        scalar("Nat"),
        Expr::sort(Level::one()),
        BinderInfo::Default,
    )));
}

#[test]
fn higher_rank_callback_parameters_are_templates_at_every_prefix_position() {
    let identity = pi(
        Expr::sort(Level::one()),
        pi(
            Expr::bvar(0).unwrap(),
            Expr::bvar(1).unwrap(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    for callback in [
        identity.clone(),
        pi(scalar("Nat"), identity, BinderInfo::Default),
    ] {
        let consumer = pi(callback, scalar("Nat"), BinderInfo::Default);
        assert!(template(consumer.clone()));
        assert!(template(pi(
            scalar("String"),
            consumer,
            BinderInfo::Default,
        )));
    }
}

#[test]
fn ordinary_callback_and_scalar_parameters_still_require_execution() {
    let callback = pi(scalar("Nat"), scalar("Nat"), BinderInfo::Default);
    assert!(!template(pi(
        callback.clone(),
        scalar("Nat"),
        BinderInfo::Default,
    )));
    let consumer = pi(callback, scalar("Nat"), BinderInfo::Default);
    assert!(!template(pi(consumer, scalar("Nat"), BinderInfo::Default)));
    assert!(!template(pi(
        scalar("Nat"),
        pi(scalar("String"), scalar("Bool"), BinderInfo::Default),
        BinderInfo::Default,
    )));
    assert!(!template(scalar("Nat")));
}

#[test]
fn explicit_polymorphic_callbacks_require_concrete_call_site_templates() {
    let identity = pi(
        Expr::sort(Level::one()),
        pi(
            Expr::bvar(0).unwrap(),
            Expr::bvar(1).unwrap(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    for callback in [
        identity.clone(),
        pi(scalar("Nat"), identity, BinderInfo::Default),
        pi(Expr::sort(Level::one()), scalar("Nat"), BinderInfo::Default),
    ] {
        assert!(template(pi(
            scalar("Nat"),
            pi(callback, scalar("Nat"), BinderInfo::Default),
            BinderInfo::Default,
        )));
    }
}

#[test]
fn long_parameter_telescopes_do_not_recurse_on_the_host_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut type_ = pi(
                Expr::sort(Level::one()),
                scalar("Nat"),
                BinderInfo::Implicit,
            );
            for _ in 0..4000 {
                type_ = pi(scalar("Nat"), type_, BinderInfo::Default);
            }
            // Both the definition's outer telescope and a callback's own
            // generic prefix remain iterative on this deliberately small stack.
            assert!(template(type_.clone()));
            assert!(template(pi(type_, scalar("Nat"), BinderInfo::Default)));
        })
        .unwrap()
        .join()
        .unwrap();
}
