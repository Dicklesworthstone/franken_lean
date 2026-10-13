//! Compare telescope opening with the preexisting single-binder operation.

use super::*;
use crate::wire::{BinderStyle, NamePart};
use std::collections::BTreeSet;

fn id(index: usize) -> ExprId {
    ExprId::from_index(index).expect("bounded test arena")
}

fn name(text: &str) -> WireName {
    WireName::from_parts(vec![NamePart::Text(text.to_owned())])
}

fn local(index: u64) -> WireName {
    WireName::from_parts(vec![
        NamePart::Text("_local.with.dot".to_owned()),
        NamePart::Numeric {
            value: index,
            overflowed: false,
        },
    ])
}

fn complete(outcome: TermOutcome<WireExpr>) -> WireExpr {
    match outcome {
        TermOutcome::Complete(term) => term,
        other => panic!("unexpected opening outcome: {other:?}"),
    }
}

fn push(nodes: &mut Vec<ExprNode>, node: ExprNode) -> ExprId {
    let result = id(nodes.len());
    nodes.push(node);
    result
}

fn apply(nodes: &mut Vec<ExprNode>, function: ExprId, argument: ExprId) -> ExprId {
    push(nodes, ExprNode::Apply { function, argument })
}

/// This oracle executes the unchanged operation formerly used by inference.
/// Counts cover each actual materialized output, including unused positions.
fn sequential_open(term: &WireExpr, names: &[&WireName]) -> (WireExpr, u64, usize) {
    let mut result = term.clone();
    let mut polls = 0;
    let mut copied_nodes = 0;
    for name in names.iter().rev() {
        let replacement = WireExpr::from_parts(
            vec![ExprNode::Free {
                name: (*name).clone(),
            }],
            vec![],
            id(0),
        );
        result = complete(substitute_bound_with(
            &result,
            0,
            &replacement,
            TermBudget::unlimited(),
            || {
                polls += 1;
                false
            },
        ));
        copied_nodes += result.nodes().len() + result.levels().len();
    }
    (result, polls, copied_nodes)
}

/// Compare denoted syntax without requiring identical output DAG sharing.
/// Iterative pair visitation also handles the exponentially shared work case.
fn assert_same_syntax(left: &WireExpr, right: &WireExpr) {
    assert_eq!(left.levels(), right.levels());
    let mut pending = vec![(left.root(), right.root())];
    let mut seen = BTreeSet::new();
    while let Some((left_id, right_id)) = pending.pop() {
        if !seen.insert((left_id.index(), right_id.index())) {
            continue;
        }
        let left = left.node(left_id).expect("left node");
        let right = right.node(right_id).expect("right node");
        match (left, right) {
            (
                ExprNode::Apply {
                    function: lf,
                    argument: la,
                },
                ExprNode::Apply {
                    function: rf,
                    argument: ra,
                },
            ) => pending.extend([(*lf, *rf), (*la, *ra)]),
            (
                ExprNode::Lambda {
                    binder_name: ln,
                    binder_type: lt,
                    body: lb,
                    style: ls,
                },
                ExprNode::Lambda {
                    binder_name: rn,
                    binder_type: rt,
                    body: rb,
                    style: rs,
                },
            )
            | (
                ExprNode::Forall {
                    binder_name: ln,
                    binder_type: lt,
                    body: lb,
                    style: ls,
                },
                ExprNode::Forall {
                    binder_name: rn,
                    binder_type: rt,
                    body: rb,
                    style: rs,
                },
            ) => {
                assert_eq!((ln, ls), (rn, rs));
                pending.extend([(*lt, *rt), (*lb, *rb)]);
            }
            (
                ExprNode::Let {
                    declaration_name: ln,
                    type_: lt,
                    value: lv,
                    body: lb,
                    non_dependent: ld,
                },
                ExprNode::Let {
                    declaration_name: rn,
                    type_: rt,
                    value: rv,
                    body: rb,
                    non_dependent: rd,
                },
            ) => {
                assert_eq!((ln, ld), (rn, rd));
                pending.extend([(*lt, *rt), (*lv, *rv), (*lb, *rb)]);
            }
            (
                ExprNode::Metadata {
                    entries: le,
                    expression: lx,
                },
                ExprNode::Metadata {
                    entries: re,
                    expression: rx,
                },
            ) => {
                assert_eq!(le, re);
                pending.push((*lx, *rx));
            }
            (
                ExprNode::Projection {
                    structure_name: ln,
                    index: li,
                    expression: lx,
                },
                ExprNode::Projection {
                    structure_name: rn,
                    index: ri,
                    expression: rx,
                },
            ) => {
                assert_eq!((ln, li), (rn, ri));
                pending.push((*lx, *rx));
            }
            _ => assert_eq!(left, right),
        }
    }
}

/// One open spine appears at depths zero through three, including in binder
/// domains and a let value (which remain outside their own binder).
fn mixed_scopes() -> WireExpr {
    let mut nodes = vec![
        ExprNode::Bound { index: 0 },
        ExprNode::Bound { index: 1 },
        ExprNode::Bound { index: 4 },
        ExprNode::Bound {
            index: MAX_BVAR_INDEX,
        },
        ExprNode::Free { name: local(99) },
        ExprNode::Sort {
            level: LevelId::ZERO,
        },
    ];
    let mut spine = id(0);
    for argument in [id(1), id(2), id(3), id(4), id(5)] {
        spine = apply(&mut nodes, spine, argument);
    }
    let lambda = push(
        &mut nodes,
        ExprNode::Lambda {
            binder_name: name("same"),
            binder_type: id(1),
            body: spine,
            style: BinderStyle::Implicit,
        },
    );
    let forall = push(
        &mut nodes,
        ExprNode::Forall {
            binder_name: name("same"),
            binder_type: spine,
            body: lambda,
            style: BinderStyle::StrictImplicit,
        },
    );
    let let_ = push(
        &mut nodes,
        ExprNode::Let {
            declaration_name: name("same"),
            type_: spine,
            value: lambda,
            body: forall,
            non_dependent: false,
        },
    );
    let metadata = push(
        &mut nodes,
        ExprNode::Metadata {
            entries: vec![(
                name("source"),
                MetadataValue::Text("λ telescope".to_owned()),
            )],
            expression: let_,
        },
    );
    let projection = push(
        &mut nodes,
        ExprNode::Projection {
            structure_name: name("S"),
            index: 3,
            expression: metadata,
        },
    );
    let root = apply(&mut nodes, spine, projection);
    WireExpr::from_parts(nodes, vec![LevelNode::Zero], root)
}

#[test]
fn open_many_matches_sequential_substitution_across_mixed_scopes() {
    let term = mixed_scopes();
    let names: Vec<_> = (0..7).map(local).collect();
    // Includes empty opening, sparse unused positions, and surviving loose
    // indices. MAX_BVAR_INDEX must decrease without arithmetic wraparound.
    for count in 0..=names.len() {
        let active: Vec<_> = names[..count].iter().collect();
        let expected = sequential_open(&term, &active).0;
        let actual = complete(open_bound_telescope_with(
            &term,
            &active,
            TermBudget::unlimited(),
            &mut || false,
        ));
        assert_same_syntax(&actual, &expected);
        assert!(
            actual
                .nodes()
                .iter()
                .any(|node| { matches!(node, ExprNode::Free { name } if name == &local(99)) }),
            "an existing free identity changed"
        );
    }
}

#[test]
fn open_many_keeps_depth_sensitive_bounds_and_closed_free_dag_sharing() {
    for first_is_bound in [false, true] {
        let mut nodes = vec![
            ExprNode::Bound { index: 0 },
            ExprNode::Free {
                name: name("ambient"),
            },
        ];
        let mut closed = id(1);
        for _ in 0..12 {
            closed = apply(&mut nodes, closed, closed);
        }
        let inner = push(
            &mut nodes,
            ExprNode::Lambda {
                binder_name: name("inner"),
                binder_type: closed,
                body: id(0),
                style: BinderStyle::Default,
            },
        );
        let outer = push(
            &mut nodes,
            ExprNode::Lambda {
                binder_name: name("outer"),
                binder_type: closed,
                body: inner,
                style: BinderStyle::Default,
            },
        );
        let forall = push(
            &mut nodes,
            ExprNode::Forall {
                binder_name: name("forall"),
                binder_type: closed,
                body: id(0),
                style: BinderStyle::InstanceImplicit,
            },
        );
        let let_ = push(
            &mut nodes,
            ExprNode::Let {
                declaration_name: name("let"),
                type_: closed,
                value: id(0),
                body: id(0),
                non_dependent: true,
            },
        );
        let order = if first_is_bound {
            [id(0), outer, forall, let_]
        } else {
            [outer, forall, let_, id(0)]
        };
        let mut root = order[0];
        for next in &order[1..] {
            root = apply(&mut nodes, root, *next);
        }
        let term = WireExpr::from_parts(nodes, vec![], root);
        let names = [local(0), local(1)];
        let active = [&names[0], &names[1]];
        let actual = complete(open_bound_telescope_with(
            &term,
            &active,
            TermBudget::unlimited(),
            &mut || false,
        ));
        assert_same_syntax(&actual, &sequential_open(&term, &active).0);
        let domains: Vec<_> = actual
            .nodes()
            .iter()
            .filter_map(|node| match node {
                ExprNode::Lambda { binder_type, .. } | ExprNode::Forall { binder_type, .. } => {
                    Some(*binder_type)
                }
                ExprNode::Let { type_, .. } => Some(*type_),
                _ => None,
            })
            .collect();
        assert_eq!(domains.len(), 4);
        assert!(
            domains.iter().all(|domain| *domain == domains[0]),
            "closed DAG containing a free name was copied for each depth"
        );
        assert_eq!(
            actual
                .nodes()
                .iter()
                .filter(|node| {
                    matches!(node, ExprNode::Free { name: found } if found == &name("ambient"))
                })
                .count(),
            1
        );
    }
}

#[test]
fn open_many_shares_inserted_locals_across_distinct_nodes_and_depths() {
    let mut nodes = vec![
        ExprNode::Bound { index: 0 },
        ExprNode::Bound { index: 0 },
        ExprNode::Bound { index: 1 },
        ExprNode::Bound { index: 1 },
        ExprNode::Sort {
            level: LevelId::ZERO,
        },
    ];
    let inside = apply(&mut nodes, id(2), id(3));
    let lambda = push(
        &mut nodes,
        ExprNode::Lambda {
            binder_name: name("b"),
            binder_type: id(4),
            body: inside,
            style: BinderStyle::Default,
        },
    );
    let outside = apply(&mut nodes, id(0), id(1));
    let root = apply(&mut nodes, outside, lambda);
    let term = WireExpr::from_parts(nodes, vec![LevelNode::Zero], root);
    let names = [local(0), name(&"largeλ".repeat(128))];
    let active = [&names[0], &names[1]];
    let expected = sequential_open(&term, &active).0;
    let units = expected
        .nodes()
        .iter()
        .map(expression_owned_units)
        .sum::<u64>()
        + expected.levels().iter().map(level_owned_units).sum::<u64>();
    // The old operation copied this one Free replacement once, even though
    // four distinct subject occurrences at two depths select it. The fused
    // operation must still fit that exact output and arena-node budget.
    let actual = complete(open_bound_telescope_with(
        &term,
        &active,
        TermBudget::new(u64::MAX, units).with_max_arena_nodes(expected.nodes().len() as u64),
        &mut || false,
    ));
    assert_same_syntax(&actual, &expected);
    assert_eq!(
        actual
            .nodes()
            .iter()
            .filter(|node| { matches!(node, ExprNode::Free { name } if name == &names[1]) })
            .count(),
        1
    );
}

#[test]
fn open_many_avoids_recopying_a_large_term_for_unused_telescope_positions() {
    const BINDERS: usize = 64;
    const CLOSED_NODES: usize = 8192;
    let mut nodes = vec![ExprNode::Free {
        name: name("ambient"),
    }];
    let mut closed = id(0);
    for _ in 0..CLOSED_NODES {
        closed = apply(&mut nodes, closed, closed);
    }
    let outer = push(
        &mut nodes,
        ExprNode::Bound {
            index: BINDERS as u32 - 1,
        },
    );
    let root = apply(&mut nodes, closed, outer);
    let term = WireExpr::from_parts(nodes, vec![], root);
    let names: Vec<_> = (0..BINDERS as u64).map(local).collect();
    let active: Vec<_> = names.iter().collect();
    let (expected, old_polls, old_nodes) = sequential_open(&term, &active);
    let mut new_polls = 0;
    let actual = complete(open_bound_telescope_with(
        &term,
        &active,
        TermBudget::unlimited(),
        &mut || {
            new_polls += 1;
            false
        },
    ));
    assert_same_syntax(&actual, &expected);
    let new_nodes = actual.nodes().len() + actual.levels().len();
    assert_eq!(new_nodes, term.nodes().len());
    assert_eq!(old_nodes, new_nodes * BINDERS);
    assert!(old_polls >= new_polls * 32, "{old_polls} vs {new_polls}");
    eprintln!(
        "64-local opening: sequential {old_nodes} output nodes / {old_polls} polls; one pass {new_nodes} output nodes / {new_polls} polls"
    );
}

#[test]
fn open_many_preserves_typed_stops_exact_output_bounds_and_input() {
    let term = mixed_scopes();
    let pristine = term.clone();
    let names = [name(&"largeλ".repeat(64)), local(1)];
    let active = [&names[0], &names[1]];
    let mut polls = 0;
    let expected = complete(open_bound_telescope_with(
        &term,
        &active,
        TermBudget::unlimited(),
        &mut || {
            polls += 1;
            false
        },
    ));
    for stop in 1..=polls {
        let mut observed = 0;
        let actual =
            open_bound_telescope_with(&term, &active, TermBudget::unlimited(), &mut || {
                observed += 1;
                observed == stop
            });
        assert!(
            matches!(
                actual,
                TermOutcome::Inconclusive(TermStop::Cancelled { .. })
            ),
            "cancellation {stop}: {actual:?}"
        );
        assert_eq!(term, pristine);
    }
    let units = expected
        .nodes()
        .iter()
        .map(expression_owned_units)
        .sum::<u64>()
        + expected.levels().iter().map(level_owned_units).sum::<u64>();
    let node_count = expected.nodes().len() as u64;
    for (budget, limit) in [
        (TermBudget::new(0, u64::MAX), TermLimit::Steps),
        (TermBudget::new(u64::MAX, units - 1), TermLimit::OutputUnits),
        (
            TermBudget::unlimited().with_max_arena_nodes(node_count - 1),
            TermLimit::ArenaNodes,
        ),
    ] {
        let outcome = open_bound_telescope_with(&term, &active, budget, &mut || false);
        assert!(
            matches!(outcome, TermOutcome::Inconclusive(TermStop::Resource { limit: found, .. }) if found == limit),
            "{outcome:?}"
        );
    }
    assert_eq!(
        complete(open_bound_telescope_with(
            &term,
            &active,
            TermBudget::new(u64::MAX, units).with_max_arena_nodes(node_count),
            &mut || false,
        )),
        expected
    );
    assert_eq!(term, pristine);

    let malformed = WireExpr::from_parts(
        vec![ExprNode::Apply {
            function: id(0),
            argument: id(0),
        }],
        vec![],
        id(0),
    );
    assert!(matches!(
        open_bound_telescope_with(&malformed, &active, TermBudget::unlimited(), &mut || false,),
        TermOutcome::InternalFault(TermFault::NonBackwardExpressionReference { .. })
    ));
}
