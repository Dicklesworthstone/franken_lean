//! Projection layout selection must not expand unaffected shared expression DAGs.
use super::*;

fn environment() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[b"structure PruningBox where\n  value : Nat"],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}
fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}
fn plus(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(c("Nat.add"), a), b)
}
fn shared(mut leaf: Expr, depth: usize) -> Expr {
    for _ in 0..depth {
        leaf = plus(leaf.clone(), leaf);
    }
    leaf
}
#[test]
fn an_unaffected_shared_sibling_does_not_exhaust_projection_lowering() {
    let engine = environment();
    let root = engine.logical_root(&KVMap::new());
    let sibling = shared(nat::literal(1), 20);
    let receiver = Expr::app(c("PruningBox.mk"), nat::literal(42));
    let projected = Expr::proj(name("PruningBox"), 0, receiver);
    let input = plus(sibling.clone(), projected);
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let output = preparation.lower_projections(&input).unwrap();
    let ExprNode::App { f, .. } = output.node() else {
        panic!("outer application");
    };
    let ExprNode::App { a, .. } = f.node() else {
        panic!("first operand");
    };
    assert_eq!(a, &sibling);
    assert_eq!(a.allocation_identity(), sibling.allocation_identity());
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn open_unaffected_subtrees_keep_their_exact_scope_and_strict_bindings() {
    let engine = environment();
    let variable = Expr::bvar(0).unwrap();
    let retained = Expr::let_e(
        name("strict"),
        c("Nat"),
        Expr::app(c("workStillExecutes"), variable.clone()),
        variable,
        false,
    );
    let body = plus(
        retained.clone(),
        Expr::proj(
            name("PruningBox"),
            0,
            Expr::app(c("PruningBox.mk"), nat::literal(42)),
        ),
    );
    let input = Expr::lam(name("x"), c("Nat"), body, BinderInfo::Default);
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let output = preparation.lower_projections(&input).unwrap();
    let ExprNode::Lam { body, .. } = output.node() else {
        panic!("lambda");
    };
    let ExprNode::App { f, .. } = body.node() else {
        panic!("application");
    };
    let ExprNode::App { a, .. } = f.node() else {
        panic!("retained operand");
    };
    assert_eq!(a, &retained);
    assert_eq!(a.allocation_identity(), retained.allocation_identity());
    // The unknown executable initializer is deliberately not evaluated by a
    // representation-only pass. This test does not authorize its compilation.
}

#[test]
fn nested_projections_and_invalid_receivers_are_not_hidden_by_the_summary() {
    let engine = environment();
    let nested = Expr::proj(
        name("PruningBox"),
        0,
        Expr::app(c("PruningBox.mk"), nat::literal(7)),
    );
    let input = Expr::proj(name("PruningBox"), 0, Expr::app(c("PruningBox.mk"), nested));
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let output = preparation.lower_projections(&input).unwrap();
    let ExprNode::Proj {
        struct_name: outer,
        expr,
        ..
    } = output.node()
    else {
        panic!("outer field");
    };
    let ExprNode::App { a, .. } = expr.node() else {
        panic!("constructor");
    };
    let ExprNode::Proj {
        struct_name: inner, ..
    } = a.node()
    else {
        panic!("inner field");
    };
    assert_eq!(outer, inner);
    assert_eq!(outer, &name("PruningBox"));
    for (family, index) in [("Other", 0), ("PruningBox", 1)] {
        let invalid = plus(
            shared(nat::literal(1), 20),
            Expr::proj(
                name(family),
                index,
                Expr::app(c("PruningBox.mk"), nat::literal(42)),
            ),
        );
        assert!(
            Preparation::new(engine.environment(), IngressLimits::default())
                .lower_projections(&invalid)
                .is_err()
        );
    }
}

#[test]
fn summary_and_lowering_budget_stops_do_not_change_fresh_retries() {
    let engine = environment();
    let root = engine.logical_root(&KVMap::new());
    let input = plus(
        shared(nat::literal(1), 12),
        Expr::proj(
            name("PruningBox"),
            0,
            Expr::app(c("PruningBox.mk"), nat::literal(42)),
        ),
    );
    let mut full = Preparation::new(engine.environment(), IngressLimits::default());
    let expected = full.lower_projections(&input).unwrap();
    let required = full.visited;
    assert!(
        required > 1 && required < 10_000,
        "bounded DAG work: {required}"
    );
    for allowed in [0, required / 2, required - 1] {
        let mut limited = Preparation::new(
            engine.environment(),
            IngressLimits {
                max_nodes: allowed,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            limited.lower_projections(&input),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
    let mut retry = Preparation::new(engine.environment(), IngressLimits::default());
    assert_eq!(retry.lower_projections(&input).unwrap(), expected);
    assert_eq!(retry.visited, required);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn closed_projection_dags_share_analysis_without_erasing_any_occurrence() {
    let engine = environment();
    let receiver = Expr::app(c("PruningBox.mk"), nat::literal(42));
    let leaf = Expr::proj(name("PruningBox"), 0, receiver);
    let input = shared(leaf, 20);
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let output = preparation.lower_projections(&input).unwrap();
    let mut current = &output;
    for _ in 0..20 {
        let ExprNode::App { f, a: right } = current.node() else {
            panic!("right operand");
        };
        let ExprNode::App { a: left, .. } = f.node() else {
            panic!("left operand");
        };
        assert_eq!(left, right);
        assert_eq!(left.allocation_identity(), right.allocation_identity());
        current = left;
    }
    assert!(matches!(current.node(), ExprNode::Proj { .. }));
    assert!(
        preparation.visited < 10_000,
        "linear analysis work: {}",
        preparation.visited
    );
}
