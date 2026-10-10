//! Bounded occurrence analysis must preserve value uses and lexical depth.
use super::*;

fn nat() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}

fn b(index: usize) -> Expr {
    variable(index).unwrap()
}

fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn local(type_: Expr, value: Expr, body: Expr) -> Expr {
    Expr::let_e(Name::anonymous(), type_, value, body, false)
}

fn lambda_chain(count: usize) -> Expr {
    (0..count).fold(nat::literal(0), |body, _| lam(nat(), body))
}

fn let_chain(count: usize) -> Expr {
    (0..count).fold(nat::literal(0), |body, _| {
        local(nat(), nat::literal(0), body)
    })
}

#[test]
fn absence_pruning_preserves_callee_and_value_occurrences() {
    let environment = Environment::new();
    let direct = Expr::app(b(0), nat::literal(1));
    let cases = [
        ("callee", direct.clone(), true),
        ("bare value", b(0), false),
        ("argument", Expr::app(b(1), b(0)), false),
        ("mixed", Expr::app(direct, b(0)), false),
        (
            "outer under lambda",
            lam(nat(), Expr::app(b(1), b(0))),
            true,
        ),
        (
            "unrelated local",
            lam(nat(), Expr::app(b(0), nat::literal(1))),
            false,
        ),
        (
            "lambda returns value",
            Expr::app(lam(nat(), b(1)), nat::literal(1)),
            false,
        ),
        (
            "let callee tail",
            Expr::app(local(nat(), nat::literal(0), b(1)), nat::literal(1)),
            true,
        ),
        ("let value tail", local(nat(), nat::literal(0), b(1)), false),
        (
            "let initializer is a value",
            Expr::app(local(nat(), b(0), b(0)), nat::literal(1)),
            false,
        ),
        (
            "metadata callee",
            Expr::app(Expr::mdata(KVMap::new(), b(0)), nat::literal(1)),
            true,
        ),
        (
            "projection receiver is a value",
            Expr::app(Expr::proj(name("Box"), 0, b(0)), nat::literal(1)),
            false,
        ),
        ("lambda type only", lam(b(0), b(0)), false),
        ("let type only", local(b(0), nat::literal(0), b(0)), false),
    ];
    for (label, expression, expected) in cases {
        let original = expression.clone();
        assert_eq!(
            Preparation::new(&environment, IngressLimits::default())
                .only_callee_uses(&expression)
                .unwrap(),
            expected,
            "{label}"
        );
        assert_eq!(expression, original, "{label}: source syntax is retained");
    }
}

#[test]
fn a_large_absent_subtree_does_not_consume_an_expanded_tree_budget() {
    let environment = Environment::new();
    let add = Expr::const_(name("Nat.add"), Vec::new());
    let mut closed = nat::literal(1);
    for _ in 0..20 {
        closed = Expr::app(Expr::app(add.clone(), closed.clone()), closed);
    }
    assert_eq!(closed.loose_bvar_range(), 0);
    assert!(closed.approx_depth() < u8::MAX);
    let limits = IngressLimits {
        max_nodes: 3,
        ..IngressLimits::default()
    };
    let expression = Expr::app(b(0), closed.clone());
    let original = expression.clone();
    let mut preparation = Preparation::new(&environment, limits);
    assert!(preparation.only_callee_uses(&expression).unwrap());
    assert_eq!(preparation.visited, 3);
    assert_eq!(expression, original);

    let mut preparation = Preparation::new(&environment, limits);
    assert!(!preparation.only_callee_uses(&closed).unwrap());
    assert_eq!(preparation.visited, 1);
}

#[test]
fn absent_binders_still_enforce_the_original_context_depth_boundary() {
    let environment = Environment::new();
    for expression in [lambda_chain(26), let_chain(26)] {
        assert_eq!(expression.loose_bvar_range(), 0);
        assert!(expression.approx_depth() < u8::MAX);
        let limits = IngressLimits {
            max_context_depth: 25,
            ..IngressLimits::default()
        };
        assert_eq!(
            Preparation::new(&environment, limits).only_callee_uses(&expression),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: 25,
                observed: 26,
            })
        );
        let limits = IngressLimits {
            max_context_depth: 26,
            ..limits
        };
        assert!(
            !Preparation::new(&environment, limits)
                .only_callee_uses(&expression)
                .unwrap()
        );
    }
}

#[test]
fn saturated_height_never_proves_that_deep_binders_fit() {
    let environment = Environment::new();
    for expression in [lambda_chain(400), let_chain(400)] {
        assert_eq!(expression.approx_depth(), u8::MAX);
        assert_eq!(expression.loose_bvar_range(), 0);
        let limits = IngressLimits {
            max_context_depth: 260,
            ..IngressLimits::default()
        };
        assert_eq!(
            Preparation::new(&environment, limits).only_callee_uses(&expression),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: 260,
                observed: 261,
            })
        );
        let limits = IngressLimits {
            max_context_depth: 400,
            ..limits
        };
        assert!(
            !Preparation::new(&environment, limits)
                .only_callee_uses(&expression)
                .unwrap()
        );
    }

    // Structural height is only a conservative pruning condition: a deep
    // application without binders must not invent a lexical-depth refusal.
    let expression = (0..400).fold(nat::literal(0), |body, _| {
        Expr::app(Expr::const_(name("Nat.succ"), Vec::new()), body)
    });
    assert_eq!(expression.approx_depth(), u8::MAX);
    assert!(
        !Preparation::new(
            &environment,
            IngressLimits {
                max_context_depth: 0,
                ..IngressLimits::default()
            },
        )
        .only_callee_uses(&expression)
        .unwrap()
    );
}

#[test]
fn even_pruned_queries_charge_fuel_and_fail_without_mutating_the_input() {
    let environment = Environment::new();
    let expression = lambda_chain(26);
    let original = expression.clone();
    let limits = IngressLimits {
        max_nodes: 0,
        ..IngressLimits::default()
    };
    assert_eq!(
        Preparation::new(&environment, limits).only_callee_uses(&expression),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 0,
            observed: 1,
        })
    );
    let limits = IngressLimits {
        max_nodes: 1,
        ..limits
    };
    assert!(
        !Preparation::new(&environment, limits)
            .only_callee_uses(&expression)
            .unwrap()
    );
    assert_eq!(expression, original);

    let expression = Expr::app(b(0), nat::literal(1));
    let limits = IngressLimits {
        max_nodes: 2,
        ..limits
    };
    assert_eq!(
        Preparation::new(&environment, limits).only_callee_uses(&expression),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 2,
            observed: 3,
        })
    );
    assert!(
        Preparation::new(
            &environment,
            IngressLimits {
                max_nodes: 3,
                ..limits
            },
        )
        .only_callee_uses(&expression)
        .unwrap()
    );
}
