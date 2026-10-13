//! Exact administrative reduction; source controls exercise native ingress.
use super::*;
use fln_core::level::Level;

fn constant(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn lam(body: Expr) -> Expr {
    Expr::lam(
        Name::anonymous(),
        constant("Nat"),
        body,
        BinderInfo::Default,
    )
}

fn local(label: &str, type_: Expr, value: Expr, body: Expr) -> Expr {
    Expr::let_e(name(label), type_, value, body, false)
}

fn action() -> Expr {
    Expr::forall_e(
        Name::anonymous(),
        constant("Nat"),
        constant("Nat"),
        BinderInfo::Default,
    )
}

fn alias(value: Expr) -> Expr {
    local("result", action(), value, b(0))
}

#[test]
fn a_checked_local_spine_exposes_only_its_own_inert_return_gap() {
    let environment = Environment::new();
    let input = lam(lam(local(
        "unused",
        constant("Nat"),
        b(0),
        alias(lam(b(3))),
    )));
    let expected = lam(lam(lam(b(2))));
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    assert_eq!(
        preparation.administrative_callable_value(&input).unwrap(),
        expected
    );
    let strict = lam(lam(local(
        "paid",
        constant("Nat"),
        Expr::app(constant("spend"), b(0)),
        alias(lam(b(3))),
    )));
    assert_eq!(
        preparation.administrative_callable_value(&strict).unwrap(),
        strict
    );
    assert!(preparation.lambdas.is_empty());
}

#[test]
fn dead_value_aliases_preserve_open_capture_indices_and_binder_types() {
    let environment = Environment::new();
    // One outer Nat is captured across three administrative slots. The
    // returned lambda must still reference that value after all slots vanish.
    let add = |a, z| Expr::app(Expr::app(constant("Nat.add"), a), z);
    let input = local(
        "unused",
        constant("Nat"),
        b(0),
        local(
            "message",
            constant("String"),
            Expr::lit(fln_core::expr::Literal::Str("unreachable".to_owned())),
            local(
                "forwarded",
                constant("String"),
                b(0),
                local("result", action(), lam(add(b(0), b(4))), alias(b(0))),
            ),
        ),
    );
    let expected = lam(add(b(0), b(1)));
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    assert_eq!(
        preparation.administrative_callable_gap(&input).unwrap(),
        Some(expected)
    );

    // A type annotation that refers to the alias makes it live, even if the
    // runtime body ignores its value. The pass must not guess a substitution.
    let dependent = local(
        "carrier",
        Expr::sort(Level::one()),
        b(0),
        Expr::lam(Name::anonymous(), b(0), b(1), BinderInfo::Default),
    );
    assert!(
        preparation
            .administrative_callable_gap(&dependent)
            .unwrap()
            .is_none()
    );
}

#[test]
fn strict_computation_used_aliases_and_unknown_projections_keep_the_stage_boundary() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    for input in [
        local(
            "paid",
            constant("Nat"),
            Expr::app(constant("spend"), b(0)),
            lam(b(0)),
        ),
        local("used", constant("Nat"), b(0), lam(b(1))),
        local("used", constant("Nat"), nat::literal(7), lam(b(1))),
        local("unknown", constant("Nat"), constant("missing"), lam(b(0))),
        local(
            "selected",
            constant("Nat"),
            Expr::proj(name("Missing"), 0, b(0)),
            lam(b(0)),
        ),
        // A computed initializer does not become inert merely because two
        // identity wrappers hide it and the resulting value is discarded.
        local(
            "paid",
            constant("Nat"),
            alias(alias(Expr::app(constant("spend"), b(0)))),
            alias(lam(b(0))),
        ),
    ] {
        assert!(
            preparation
                .administrative_callable_gap(&input)
                .unwrap()
                .is_none(),
            "the original strict stage must survive: {input:?}"
        );
    }
}

#[test]
fn administrative_scopes_and_work_fail_before_publication_and_retry_cleanly() {
    let environment = Environment::new();
    let input = local("unused", constant("Nat"), b(0), alias(alias(lam(b(3)))));
    let mut measured = Preparation::new(&environment, IngressLimits::default());
    let expected = measured
        .administrative_callable_gap(&input)
        .unwrap()
        .unwrap();
    let required = measured.visited;
    assert!(required > 1);
    for max_nodes in [0, required - 1] {
        let mut preparation = Preparation::new(
            &environment,
            IngressLimits {
                max_nodes,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            preparation.administrative_callable_gap(&input),
            Err(IngressError::ResourceLimit { resource: IngressResource::Nodes, limit, .. })
                if limit == max_nodes
        ));
        assert!(preparation.lambdas.is_empty());
        preparation.limits.max_nodes = IngressLimits::default().max_nodes;
        assert_eq!(
            preparation.administrative_callable_gap(&input).unwrap(),
            Some(expected.clone())
        );
    }
    let mut preparation = Preparation::new(
        &environment,
        IngressLimits {
            max_context_depth: 1,
            ..IngressLimits::default()
        },
    );
    let nested = local(
        "a",
        constant("Nat"),
        b(0),
        local("b", constant("Nat"), b(0), lam(b(3))),
    );
    assert!(matches!(
        preparation.administrative_callable_gap(&nested),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 1,
            observed: 2
        })
    ));
    preparation.limits.max_context_depth = IngressLimits::default().max_context_depth;
    assert_eq!(
        preparation.administrative_callable_gap(&nested).unwrap(),
        Some(lam(b(1)))
    );
}

#[test]
fn identity_lets_expose_only_an_existing_literal_lambda() {
    let environment = Environment::new();
    let literal = lam(b(0));
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    assert_eq!(
        preparation
            .administrative_callable_gap(&alias(alias(literal.clone())))
            .unwrap(),
        Some(literal)
    );
    let call = Expr::app(constant("computeCallback"), nat::literal(0));
    assert!(
        preparation
            .administrative_callable_gap(&alias(call))
            .unwrap()
            .is_none()
    );
}

#[test]
fn a_callback_exposed_after_application_gets_its_exact_captured_flat_interface() {
    let engine = crate::Engine::with_source_seed(crate::EngineAdmissionLimits::new(
        crate::Budget::for_stack_bytes(2 * 1024 * 1024),
    ))
    .unwrap()
    .into_complete()
    .unwrap();
    let bool_type = constant("Bool");
    let callback_type = Expr::forall_e(
        name("flag"),
        bool_type.clone(),
        action(),
        BinderInfo::Default,
    );
    let add = |a, z| Expr::app(Expr::app(constant("Nat.add"), a), z);
    // The typed initializer is an application, so its callback is exposed
    // only after that annotation has been scheduled. The resulting strict
    // binding captures the caller's Nat while the value-only inner gap can
    // disappear before any callback metadata is registered.
    let callback = Expr::lam(
        name("flag"),
        bool_type,
        local("unused", constant("Nat"), b(1), alias(lam(add(b(0), b(3))))),
        BinderInfo::Default,
    );
    let initializer = Expr::app(lam(callback), b(0));
    let input = local("callback", callback_type, initializer, b(0));
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let prepared = preparation.expression(&input).unwrap();
    let binding = preparation
        .lambdas
        .iter()
        .find(|binding| binding.parameters == [ValueType::Bool, ValueType::Nat])
        .expect("the exposed callback retains its two-argument interface");
    assert_eq!(binding.result, ValueType::Nat);
    assert_eq!(binding.recursion, LambdaRecursion::NonRecursive);
    let ExprNode::Lam { body, .. } = binding.lambda.node() else {
        panic!("the callback owns its literal lambda");
    };
    assert_eq!(body, &lam(add(b(0), b(2))));
    let ExprNode::LetE { value, .. } = prepared.node() else {
        panic!("the original checked callback annotation survives");
    };
    assert!(matches!(value.node(), ExprNode::LetE { value, .. } if value == &b(0)));
}
