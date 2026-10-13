//! Post-erasure motive bindings; source import tests exercise admitted programs.
use super::*;

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap()
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn constant(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn local(label: &str, type_: Expr, value: Expr, body: Expr) -> Expr {
    Expr::let_e(name(label), type_, value, body, false)
}

fn motive(body: Expr) -> Expr {
    // This is the erased telescope of the actual pin's Nat.div.go motive,
    // which may become visible only after its containing callback is inlined.
    local(
        "motive",
        pi(
            constant("Nat"),
            pi(constant("Bool"), Expr::sort(Level::one())),
        ),
        lam(constant("Nat"), lam(constant("Bool"), constant("Nat"))),
        body,
    )
}

#[test]
fn late_type_family_lets_preserve_dependent_annotations_and_outer_captures() {
    let engine = engine();
    let nat = constant("Nat");
    // The input is an open catalog body, not a closed source root. This makes
    // expression preparation handle the binding exposed after proof erasure.
    let selected = Expr::app(Expr::app(b(0), b(1)), constant("Bool.false"));
    for (input, expected) in [
        (motive(b(1)), b(0)),
        (
            motive(local("value", selected.clone(), b(1), b(0))),
            local("value", nat.clone(), b(0), b(0)),
        ),
        (motive(lam(selected, b(2))), lam(nat.clone(), b(1))),
    ] {
        assert!(input.has_loose_bvars());
        let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
        assert_eq!(preparation.expression(&input).unwrap(), expected);
        assert!(
            preparation.lambdas.is_empty(),
            "a type family is not a runtime closure"
        );
    }

    // A static family can capture an outer type. Removing its binder must not
    // capture that type or the outer value under a new runtime lambda.
    let captured = local(
        "family",
        pi(nat.clone(), Expr::sort(Level::one())),
        lam(nat.clone(), b(2)),
        lam(Expr::app(b(0), nat::literal(0)), b(2)),
    );
    let expected = lam(b(1), b(1));
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(preparation.expression(&captured).unwrap(), expected);
    assert!(preparation.lambdas.is_empty());
}

#[test]
fn late_type_let_elimination_preserves_strict_runtime_lets_and_callbacks() {
    let engine = engine();
    let nat = constant("Nat");
    let add = Expr::app(Expr::app(constant("Nat.add"), b(0)), nat::literal(1));
    let input = local("paid", nat.clone(), add.clone(), motive(b(2)));
    let expected = local("paid", nat.clone(), add, b(1));
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(preparation.expression(&input).unwrap(), expected);

    // Literal lambda syntax alone is not an erasure criterion. This unused
    // runtime function retains its checked binding and ordinary registration.
    let callback_type = pi(nat.clone(), nat.clone());
    let callback = lam(nat.clone(), b(0));
    let input = local("callback", callback_type.clone(), callback, motive(b(2)));
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let result = preparation.expression(&input).unwrap();
    let ExprNode::LetE {
        type_, value, body, ..
    } = result.node()
    else {
        panic!("the runtime callback binding must remain");
    };
    assert_eq!(type_, &callback_type);
    assert_eq!(body, &b(1));
    assert_eq!(preparation.lambdas.len(), 1);
    assert_eq!(preparation.lambdas[0].lambda, *value);
    assert_eq!(preparation.lambdas[0].parameters, vec![ValueType::Nat]);
    assert_eq!(preparation.lambdas[0].result, ValueType::Nat);
}

#[test]
fn late_type_let_elimination_respects_the_preparation_budget() {
    let engine = engine();
    let input = motive(lam(
        Expr::app(Expr::app(b(0), b(1)), constant("Bool.false")),
        b(2),
    ));
    let expected = lam(constant("Nat"), b(1));
    let mut successful = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(successful.expression(&input).unwrap(), expected);
    let boundary = successful.visited - 1;
    let mut limited = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: boundary,
            ..IngressLimits::default()
        },
    );
    assert!(matches!(
        limited.expression(&input),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        }) if limit == boundary && observed == boundary + 1
    ));
    let mut retry = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(retry.expression(&input).unwrap(), expected);
    assert_eq!(retry.visited, successful.visited);
}
