use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn lambda(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn arrow(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn action() -> Expr {
    arrow(c("Nat"), c("Nat"))
}

fn alias(value: Expr) -> Expr {
    Expr::let_e(Name::anonymous(), action(), value, b(0), false)
}

fn outer(target: Expr) -> Expr {
    lambda(
        c("Bool"),
        Expr::let_e(
            name("message"),
            c("String"),
            Expr::lit(Literal::Str("unreachable".to_owned())),
            alias(alias(target)),
            false,
        ),
    )
}

fn add(a: Expr, z: Expr) -> Expr {
    Expr::app(Expr::app(c("Nat.add"), a), z)
}

fn engine() -> crate::Engine {
    crate::Engine::with_source_seed(crate::EngineAdmissionLimits::new(
        crate::Budget::for_stack_bytes(2 * 1024 * 1024),
    ))
    .unwrap()
    .into_complete()
    .unwrap()
}

#[test]
fn completed_closed_tail_stays_an_exact_executable_target_of_the_flat_wrapper() {
    let engine = engine();
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let target = preparation
        .local_lambda(&lambda(c("Nat"), add(b(0), nat::literal(32))), &action())
        .unwrap();
    let original = preparation.lambdas.clone();
    let input = outer(target.clone());
    let forwarded = preparation
        .forward_closed_administrative_tail(&input)
        .unwrap()
        .unwrap();
    assert_eq!(preparation.lambdas, original);
    let ExprNode::Lam { body, .. } = forwarded.node() else {
        panic!("the ordinary outer prefix remains");
    };
    let ExprNode::Lam {
        binder_type, body, ..
    } = body.node()
    else {
        panic!("the closed target contributes its actual parameter");
    };
    assert_eq!(binder_type, &c("Nat"));
    assert_eq!(body, &Expr::app(target.clone(), b(0)));

    let registered = preparation
        .local_lambda(&input, &arrow(c("Bool"), action()))
        .unwrap();
    assert_eq!(preparation.lambdas.len(), original.len() + 1);
    assert_eq!(preparation.lambdas[..original.len()], original);
    let binding = preparation.lambdas.last().unwrap();
    assert_eq!(binding.lambda, registered);
    assert_eq!(binding.parameters, [ValueType::Bool, ValueType::Nat]);
    assert_eq!(binding.result, ValueType::Nat);
    let ExprNode::Lam { body, .. } = registered.node() else {
        unreachable!()
    };
    let ExprNode::Lam { body, .. } = body.node() else {
        unreachable!()
    };
    assert_eq!(body, &Expr::app(target, b(0)));
}

#[test]
fn forwarding_preserves_relative_dependencies_between_its_parameter_domains() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let dependent = Expr::app(c("IndexedPayload"), b(0));
    let target = lambda(c("Nat"), lambda(dependent.clone(), b(1)));
    // This descriptive fixture isolates binder transport. Runtime ingress
    // still independently owns the actual payload representation and calls.
    preparation.lambdas.push(LambdaBinding {
        lambda: target.clone(),
        parameters: vec![ValueType::Nat, ValueType::Constructor],
        parameter_ownership: borrowed_runtime_parameters(2).unwrap(),
        result: ValueType::Nat,
        result_ownership: result_ownership(ValueType::Nat),
        recursion: LambdaRecursion::NonRecursive,
    });
    let before = preparation.lambdas.clone();
    let result = preparation
        .forward_closed_administrative_tail(&outer(target.clone()))
        .unwrap()
        .unwrap();
    let ExprNode::Lam { body, .. } = result.node() else {
        unreachable!()
    };
    let ExprNode::Lam {
        binder_type, body, ..
    } = body.node()
    else {
        unreachable!()
    };
    assert_eq!(binder_type, &c("Nat"));
    let ExprNode::Lam {
        binder_type, body, ..
    } = body.node()
    else {
        unreachable!()
    };
    assert_eq!(binder_type, &dependent);
    assert_eq!(body, &Expr::app(Expr::app(target, b(1)), b(0)));
    assert_eq!(preparation.lambdas, before);
}

#[test]
fn late_forwarding_refuses_captured_recursive_computed_and_nonborrowed_tails() {
    let engine = engine();
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let closed = preparation
        .local_lambda(&lambda(c("Nat"), b(0)), &action())
        .unwrap();
    let captured = preparation
        .local_lambda(&lambda(c("Nat"), add(b(0), b(1))), &action())
        .unwrap();
    let strict = lambda(
        c("Bool"),
        Expr::let_e(
            name("paid"),
            c("Nat"),
            Expr::app(c("spend"), b(0)),
            alias(closed.clone()),
            false,
        ),
    );
    let before = preparation.lambdas.clone();
    for input in [
        outer(captured),
        strict,
        outer(lambda(c("Nat"), nat::literal(7))),
    ] {
        assert!(
            preparation
                .forward_closed_administrative_tail(&input)
                .unwrap()
                .is_none()
        );
        assert_eq!(preparation.lambdas, before);
    }

    let input = outer(closed);
    preparation.lambdas[0].recursion = LambdaRecursion::SelfBinder;
    assert!(
        preparation
            .forward_closed_administrative_tail(&input)
            .unwrap()
            .is_none()
    );
    preparation.lambdas[0].recursion = LambdaRecursion::MutualMember {
        group: 4,
        member: 0,
        members: 2,
    };
    assert!(
        preparation
            .forward_closed_administrative_tail(&input)
            .unwrap()
            .is_none()
    );
    preparation.lambdas[0].recursion = LambdaRecursion::NonRecursive;
    preparation.lambdas[0].parameter_ownership[0] = fln_comp::flbc::ArgumentOwnership::Owned;
    assert!(
        preparation
            .forward_closed_administrative_tail(&input)
            .unwrap()
            .is_none()
    );
}

#[test]
fn completed_forwarding_respects_work_and_combined_prefix_depth_without_mutating_rows() {
    let engine = engine();
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let target = preparation
        .local_lambda(&lambda(c("Nat"), b(0)), &action())
        .unwrap();
    let input = outer(target);
    let before = preparation.lambdas.clone();
    preparation.visited = 0;
    let expected = preparation
        .forward_closed_administrative_tail(&input)
        .unwrap()
        .unwrap();
    let work = preparation.visited;
    preparation.visited = 0;
    preparation.limits.max_nodes = work - 1;
    assert!(
        matches!(preparation.forward_closed_administrative_tail(&input),
        Err(IngressError::ResourceLimit { resource: IngressResource::Nodes, limit, observed })
            if limit == work - 1 && observed == work)
    );
    assert_eq!(preparation.lambdas, before);
    preparation.visited = 0;
    preparation.limits.max_nodes = IngressLimits::default().max_nodes;
    preparation.limits.max_context_depth = 1;
    assert!(matches!(
        preparation.forward_closed_administrative_tail(&input),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 1,
            observed: 2
        })
    ));
    assert_eq!(preparation.lambdas, before);
    preparation.visited = 0;
    preparation.limits = IngressLimits::default();
    assert_eq!(
        preparation
            .forward_closed_administrative_tail(&input)
            .unwrap(),
        Some(expected)
    );
    assert_eq!(preparation.lambdas, before);
}
