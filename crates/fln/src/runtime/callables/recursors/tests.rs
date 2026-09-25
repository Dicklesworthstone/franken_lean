use super::*;
use fln_core::level::Level;

fn engine() -> crate::Engine {
    crate::Engine::with_source_seed(crate::EngineAdmissionLimits::new(
        crate::Budget::for_stack_bytes(2 * 1024 * 1024),
    ))
    .unwrap()
    .into_complete()
    .unwrap()
}
fn constant(spelling: &str) -> Expr {
    Expr::const_(name(spelling), vec![])
}
fn recursor(spelling: &str) -> Expr {
    Expr::const_(name(spelling), vec![Level::one()])
}
fn motive(domain: &str) -> Expr {
    Expr::lam(
        Name::anonymous(),
        constant(domain),
        constant("Nat"),
        BinderInfo::Default,
    )
}

#[test]
fn strict_capture_order_and_outer_indices_survive_the_wrapper() {
    let engine = engine();
    let mut prep = Preparation::new(engine.environment(), IngressLimits::default());
    let head = recursor("Bool.rec");
    let args = [motive("Bool"), variable(1).unwrap(), variable(0).unwrap()];
    let value = prep
        .partially_applied_recursor(&head, &args)
        .unwrap()
        .unwrap();
    assert!(value.has_loose_bvar(0));
    assert!(value.has_loose_bvar(1));
    assert!(!value.has_loose_bvar(2));
    let ExprNode::LetE {
        value: first, body, ..
    } = value.node()
    else {
        panic!("first capture must be strict");
    };
    assert_eq!(first, &variable(1).unwrap());
    let ExprNode::LetE {
        value: second,
        body,
        ..
    } = body.node()
    else {
        panic!("second capture must be strict");
    };
    assert_eq!(second, &variable(1).unwrap()); // outer #0 lifted past capture 1
    let ExprNode::LetE {
        value: wrapper,
        body,
        ..
    } = body.node()
    else {
        panic!("typed callback binding");
    };
    assert_eq!(body, &variable(0).unwrap());
    let ExprNode::Lam { body, .. } = wrapper.node() else {
        panic!("missing major premise");
    };
    let (actual_head, actual_args) = prep.spine(body).unwrap();
    assert_eq!(actual_head, head);
    assert_eq!(actual_args.len(), 4);
    assert_eq!(actual_args[1], variable(2).unwrap());
    assert_eq!(actual_args[2], variable(1).unwrap());
    assert_eq!(actual_args[3], variable(0).unwrap());
    // Its saturated body cannot be rewritten into another partial wrapper.
    let repeated = prep
        .partially_applied_recursor(&actual_head, &actual_args)
        .unwrap();
    assert!(repeated.is_none());
}

#[test]
fn literal_minors_keep_their_syntax_and_lift_outer_captures() {
    let engine = engine();
    let mut prep = Preparation::new(engine.environment(), IngressLimits::default());
    let step = Expr::lam(
        Name::anonymous(),
        constant("Nat"),
        Expr::lam(
            Name::anonymous(),
            constant("Nat"),
            variable(2).unwrap(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let value = prep
        .partially_applied_recursor(
            &recursor("Nat.rec"),
            &[motive("Nat"), variable(0).unwrap(), step.clone()],
        )
        .unwrap()
        .unwrap();
    let ExprNode::LetE { body, .. } = value.node() else {
        panic!("base capture");
    };
    let ExprNode::LetE { value: wrapper, .. } = body.node() else {
        panic!("typed callback, not an eager minor binding");
    };
    let ExprNode::Lam { body, .. } = wrapper.node() else {
        panic!("missing major");
    };
    let (_, args) = prep.spine(body).unwrap();
    assert_eq!(args[2], step.lift_loose(0, 2).unwrap());
    assert!(matches!(args[2].node(), ExprNode::Lam { .. }));
    assert_eq!(args[1], variable(1).unwrap());
    assert_eq!(args[3], variable(0).unwrap());
    assert!(value.has_loose_bvar(0));
    assert!(!value.has_loose_bvar(1));
}

#[test]
fn combined_context_limits_and_missing_static_authority_are_not_bypassed() {
    let engine = engine();
    let head = recursor("Bool.rec");
    let args = [motive("Bool"), variable(1).unwrap(), variable(0).unwrap()];
    let mut prep = Preparation::new(
        engine.environment(),
        IngressLimits {
            max_context_depth: 2,
            ..IngressLimits::default()
        },
    );
    assert!(matches!(
        prep.partially_applied_recursor(&head, &args),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 2,
            observed: 3,
        })
    ));
    let empty = Environment::new();
    let mut prep = Preparation::new(&empty, IngressLimits::default());
    let unavailable = prep.partially_applied_recursor(&head, &args).unwrap();
    assert!(unavailable.is_none());
    let mut prep = Preparation::new(engine.environment(), IngressLimits::default());
    let missing_motive = prep.partially_applied_recursor(&head, &[]).unwrap();
    assert!(missing_motive.is_none());
    let wrong_levels = constant("Bool.rec");
    let wrong_epoch = prep
        .partially_applied_recursor(&wrong_levels, &args)
        .unwrap();
    assert!(wrong_epoch.is_none());
}
