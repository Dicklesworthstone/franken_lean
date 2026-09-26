//! Producer transforms are structural; integration tests perform real admission.
use super::*;
use fln_env::constants::{ConstantVal, ReducibilityHints};

fn ty() -> Expr {
    Expr::const_(name("Nat"), vec![])
}
fn b(index: usize) -> Expr {
    variable(index).unwrap()
}
fn pi(body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), ty(), body, BinderInfo::Default)
}
fn lam(body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), ty(), body, BinderInfo::Default)
}
fn app(label: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter()
        .fold(Expr::const_(name(label), vec![]), Expr::app)
}
fn local(label: &str, type_: Expr, value: Expr, body: Expr) -> Expr {
    Expr::let_e(name(label), type_, value, body, false)
}
fn annotation(type_: Expr, value: Expr) -> Expr {
    Expr::let_e(Name::anonymous(), type_, value, b(0), false)
}
fn env(type_: Expr, value: Expr, safety: DefinitionSafety) -> Environment {
    Environment::new()
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: name("factory"),
                level_params: vec![],
                type_,
            },
            value,
            hints: ReducibilityHints::Abbrev,
            safety,
            all: vec![],
        }))
        .unwrap()
}
fn body() -> Expr {
    local(
        "paid",
        ty(),
        app("observe", [b(0)]),
        lam(app("Nat.add", [b(1), b(0)])),
    )
}

#[test]
fn exact_stage_application_keeps_the_producer_strict_and_shared() {
    let environment = env(pi(pi(ty())), lam(body()), DefinitionSafety::Safe);
    let result = Preparation::new(&environment, IngressLimits::default())
        .global_producer(&app("factory", []), &[b(0)])
        .unwrap()
        .unwrap();
    let expected = Expr::let_e(
        Name::anonymous(),
        ty(),
        b(0),
        local(
            "paid",
            ty(),
            app("observe", [b(0)]),
            annotation(pi(ty()), lam(app("Nat.add", [b(1), b(0)]))),
        ),
        false,
    );
    assert_eq!(result, expected);
}

#[test]
fn trailing_arguments_follow_the_producer_and_cross_all_new_binders() {
    let environment = env(pi(pi(ty())), lam(body()), DefinitionSafety::Safe);
    let result = Preparation::new(&environment, IngressLimits::default())
        .global_producer(&app("factory", []), &[b(0), app("after", [b(1)])])
        .unwrap()
        .unwrap();
    let produced = local(
        "paid",
        ty(),
        app("observe", [b(0)]),
        annotation(pi(ty()), lam(app("Nat.add", [b(1), b(0)]))),
    );
    let expected = Expr::let_e(
        Name::anonymous(),
        ty(),
        b(0),
        Expr::let_e(
            Name::anonymous(),
            pi(ty()),
            produced,
            Expr::let_e(
                Name::anonymous(),
                ty(),
                app("after", [b(3)]),
                annotation(ty(), Expr::app(b(1), b(0))),
                false,
            ),
            false,
        ),
        false,
    );
    assert_eq!(result, expected);
}

#[test]
fn partial_and_bare_globals_keep_their_real_remaining_lambda_spines() {
    let value = lam(lam(body()));
    let environment = env(pi(pi(pi(ty()))), value.clone(), DefinitionSafety::Safe);
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    assert_eq!(
        preparation
            .global_producer(&app("factory", []), &[])
            .unwrap()
            .unwrap(),
        annotation(pi(pi(pi(ty()))), value)
    );
    let partial = preparation
        .global_producer(&app("factory", []), &[b(0)])
        .unwrap()
        .unwrap();
    assert_eq!(
        partial,
        Expr::let_e(
            Name::anonymous(),
            ty(),
            b(0),
            annotation(pi(pi(ty())), lam(body())),
            false,
        )
    );
}

#[test]
fn zero_argument_global_initializers_are_not_moved_under_a_lambda() {
    let value = local("paid", ty(), app("observe", [nat::literal(9)]), lam(b(1)));
    let environment = env(pi(ty()), value, DefinitionSafety::Safe);
    let result = Preparation::new(&environment, IngressLimits::default())
        .global_producer(&app("factory", []), &[])
        .unwrap()
        .unwrap();
    assert_eq!(
        result,
        local(
            "paid",
            ty(),
            app("observe", [nat::literal(9)]),
            annotation(pi(ty()), lam(b(1)))
        )
    );
}

#[test]
fn root_annotations_preserve_the_outer_spine_and_type_the_returned_callback() {
    let environment = Environment::new();
    let value = lam(body());
    let result = Preparation::new(&environment, IngressLimits::default())
        .annotate_execution_value(value, pi(pi(ty())))
        .unwrap();
    assert_eq!(
        result,
        lam(local(
            "paid",
            ty(),
            app("observe", [b(0)]),
            annotation(pi(ty()), lam(app("Nat.add", [b(1), b(0)])))
        ))
    );
}

#[test]
fn flat_unsafe_unknown_and_dependent_globals_do_not_gain_new_code() {
    let flat = env(pi(ty()), lam(b(0)), DefinitionSafety::Safe);
    assert!(
        Preparation::new(&flat, IngressLimits::default())
            .global_producer(&app("factory", []), &[])
            .unwrap()
            .is_none()
    );
    let unsafe_env = env(pi(pi(ty())), lam(body()), DefinitionSafety::Unsafe);
    assert!(
        Preparation::new(&unsafe_env, IngressLimits::default())
            .global_producer(&app("factory", []), &[])
            .unwrap()
            .is_none()
    );
    assert!(
        Preparation::new(&Environment::new(), IngressLimits::default())
            .global_producer(&app("missing", []), &[])
            .unwrap()
            .is_none()
    );
    let dependent = env(pi(pi(b(1))), lam(body()), DefinitionSafety::Safe);
    assert!(
        Preparation::new(&dependent, IngressLimits::default())
            .global_producer(&app("factory", []), &[nat::literal(0)])
            .unwrap()
            .is_none()
    );
}

#[test]
fn work_arguments_and_combined_generated_context_have_real_limits() {
    let environment = env(pi(pi(ty())), lam(body()), DefinitionSafety::Safe);
    for limits in [
        IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        },
        IngressLimits {
            max_context_depth: 1,
            ..IngressLimits::default()
        },
        IngressLimits {
            max_application_args: 1,
            ..IngressLimits::default()
        },
    ] {
        assert!(matches!(
            Preparation::new(&environment, limits)
                .global_producer(&app("factory", []), &[b(0), b(1)]),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
}

#[test]
fn long_producer_telescopes_use_heap_walks_instead_of_host_recursion() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut type_ = pi(ty());
            let mut value = local("paid", ty(), nat::literal(0), lam(b(0)));
            for _ in 0..500 {
                type_ = pi(type_);
                value = lam(value);
            }
            let environment = env(type_, value, DefinitionSafety::Safe);
            let args = vec![nat::literal(0); 500];
            let result = Preparation::new(&environment, IngressLimits::default())
                .global_producer(&app("factory", []), &args)
                .unwrap()
                .unwrap();
            assert!(!result.has_loose_bvars());
        })
        .unwrap()
        .join()
        .unwrap();
}
