use super::*;
use crate::whnf::*;
use crate::wire::{BinderStyle, MetadataValue};

fn name(text: &str) -> WireName {
    WireName::from_parts(vec![NamePart::Text(text.to_owned())])
}

fn id(index: usize) -> ExprId {
    ExprId::from_index(index).expect("bounded test index")
}

fn lid(index: usize) -> LevelId {
    LevelId::from_index(index).expect("bounded test level")
}

fn cursor(term: WireExpr) -> Cursor {
    let root = term.root();
    Cursor::closed(Arc::new(term), root)
}

fn complete(result: WhnfOutcome) -> WhnfResult {
    let WhnfOutcome::Complete(result) = result else {
        panic!("{result:?}")
    };
    result
}

/// `(let x := D; f x) D`, with D a shared binary circuit. Zeta materializes
/// `f D` into a new arena; its argument still points into the original arena.
/// Rebuilding the application must recover D's sharing across those arenas.
fn split_application(depth: usize) -> WireExpr {
    let mut nodes = vec![
        ExprNode::Free { name: name("T") },
        ExprNode::Free { name: name("z") },
        ExprNode::Free { name: name("g") },
        ExprNode::Free { name: name("f") },
        ExprNode::Bound { index: 0 },
    ];
    let mut value = id(1);
    for _ in 0..depth {
        let partial = id(nodes.len());
        nodes.push(ExprNode::Apply {
            function: id(2),
            argument: value,
        });
        nodes.push(ExprNode::Apply {
            function: partial,
            argument: value,
        });
        value = id(nodes.len() - 1);
    }
    let body = id(nodes.len());
    nodes.push(ExprNode::Apply {
        function: id(3),
        argument: id(4),
    });
    let function = id(nodes.len());
    nodes.push(ExprNode::Let {
        declaration_name: name("x"),
        type_: id(0),
        value,
        body,
        non_dependent: false,
    });
    nodes.push(ExprNode::Apply {
        function,
        argument: value,
    });
    let root = id(nodes.len() - 1);
    WireExpr::from_parts(nodes, vec![], root)
}

fn assert_shared_arguments(term: &WireExpr) {
    let ExprNode::Apply {
        function,
        argument: right,
    } = term.node(term.root()).unwrap()
    else {
        panic!("lost application")
    };
    let ExprNode::Apply { argument: left, .. } = term.node(*function).unwrap() else {
        panic!("lost partial application")
    };
    assert_eq!(
        left, right,
        "separate materializations must share one output DAG"
    );
}

#[test]
fn native_rebuilding_rejoins_a_dag_split_by_zeta_materialization() {
    let depth = 24;
    let input = split_application(depth);
    let budget = WhnfBudget::new(
        10_000,
        2,
        TermBudget::new(1000, 4000).with_max_arena_nodes(2 * depth as u64 + 20),
    );
    let result = complete(whnf(&input, &WhnfContext::default(), budget));
    assert_eq!(result.reductions, 1);
    assert_eq!(result.term.nodes().len(), 2 * depth + 5);
    assert_shared_arguments(&result.term);
    // Repeated normalization does not alter the canonical sharing or meaning.
    let again = complete(whnf(&result.term, &WhnfContext::default(), budget));
    assert_eq!(again.term, result.term);
}

#[test]
fn forced_collisions_and_full_tables_never_impersonate_equality() {
    let arena: Vec<_> = (0..MAX_BUCKET + 3)
        .map(|n| ExprNode::Bound { index: n as u32 })
        .collect();
    let mut table = Interned::default();
    for (index, node) in arena.iter().enumerate() {
        assert_eq!(table.find(0, node, &arena, 1), None);
        table.record(0, index, 0);
    }
    assert_eq!(table.buckets[&0].len(), MAX_BUCKET);
    assert_eq!(table.entries, MAX_BUCKET);
    for (index, node) in arena.iter().enumerate() {
        assert_eq!(
            table.find(0, node, &arena, 1),
            (index < MAX_BUCKET).then_some(index)
        );
    }
    table.entries = MAX_ENTRIES;
    table.record(1, 0, 0);
    assert!(!table.buckets.contains_key(&1));
    assert_eq!(table.find(0, &arena[0], &arena, 1), Some(0));
    assert_eq!(table.find(0, &arena[0], &arena, 0), None);
}

/// A flat fixture containing every expression constructor, with rich payloads
/// that must remain part of exact equality. Every row is copied as a cursor.
fn all_nodes() -> WireExpr {
    let nodes = vec![
        ExprNode::Sort { level: lid(2) },
        ExprNode::Bound { index: 0 },
        ExprNode::Free { name: name("x") },
        ExprNode::Meta { name: name("m") },
        ExprNode::Constant {
            name: name("c"),
            levels: vec![lid(0), lid(1)],
        },
        ExprNode::Apply {
            function: id(4),
            argument: id(2),
        },
        ExprNode::Lambda {
            binder_name: name("b"),
            binder_type: id(0),
            body: id(1),
            style: BinderStyle::Implicit,
        },
        ExprNode::Forall {
            binder_name: name("b"),
            binder_type: id(0),
            body: id(1),
            style: BinderStyle::Default,
        },
        ExprNode::Let {
            declaration_name: name("d"),
            type_: id(0),
            value: id(5),
            body: id(1),
            non_dependent: false,
        },
        ExprNode::NatLiteral {
            limbs_le: vec![1, 2],
        },
        ExprNode::StringLiteral("λ\0🙂".to_owned()),
        ExprNode::Metadata {
            entries: vec![(name("key"), MetadataValue::Syntax(7))],
            expression: id(5),
        },
        ExprNode::Projection {
            structure_name: name("S"),
            index: 7,
            expression: id(5),
        },
    ];
    WireExpr::from_parts(
        nodes,
        vec![
            LevelNode::Zero,
            LevelNode::Parameter(name("u")),
            LevelNode::Max(lid(0), lid(1)),
        ],
        id(12),
    )
}

#[test]
fn composition_shares_exact_nodes_and_levels_but_preserves_distinct_payloads() {
    let term = all_nodes();
    let mut no_cancel = || false;
    let mut composer = Composer::new(
        TermBudget::unlimited(),
        WhnfPhase::RebuildApplication,
        0,
        0,
        &mut no_cancel,
    );
    let mut expected = Vec::new();
    for pass in 0..2 {
        // Different allocations, even on each cursor, are intentional.
        for index in 0..term.nodes().len() {
            let node = Cursor::closed(Arc::new(term.clone()), id(index));
            let copied = composer
                .copy_cursor(&node, index)
                .unwrap_or_else(|_| panic!("copy"));
            if pass == 0 {
                expected.push(copied);
            } else {
                assert_eq!(copied, expected[index]);
            }
        }
    }
    assert_eq!(composer.expressions.len(), term.nodes().len());
    assert_eq!(composer.levels.len(), term.levels().len());

    // Mutations hit fields not visible through child indices alone.
    let changes = [
        (0, ExprNode::Sort { level: lid(1) }),
        (1, ExprNode::Bound { index: 1 }),
        (2, ExprNode::Free { name: name("y") }),
        (3, ExprNode::Meta { name: name("n") }),
        (
            4,
            ExprNode::Constant {
                name: name("c"),
                levels: vec![lid(1), lid(0)],
            },
        ),
        (
            5,
            ExprNode::Apply {
                function: id(2),
                argument: id(4),
            },
        ),
        (
            6,
            ExprNode::Lambda {
                binder_name: name("b"),
                binder_type: id(0),
                body: id(1),
                style: BinderStyle::Default,
            },
        ),
        (
            7,
            ExprNode::Forall {
                binder_name: name("other"),
                binder_type: id(0),
                body: id(1),
                style: BinderStyle::Default,
            },
        ),
        (
            8,
            ExprNode::Let {
                declaration_name: name("d"),
                type_: id(0),
                value: id(5),
                body: id(1),
                non_dependent: true,
            },
        ),
        (
            9,
            ExprNode::NatLiteral {
                limbs_le: vec![1, 3],
            },
        ),
        (10, ExprNode::StringLiteral("λ\0🙃".to_owned())),
        (
            11,
            ExprNode::Metadata {
                entries: vec![(name("key"), MetadataValue::Syntax(8))],
                expression: id(5),
            },
        ),
        (
            12,
            ExprNode::Projection {
                structure_name: name("S"),
                index: 8,
                expression: id(5),
            },
        ),
    ];
    for (index, changed) in changes {
        let mut nodes = term.nodes().to_vec();
        nodes[index] = changed;
        let node = cursor(WireExpr::from_parts(
            nodes,
            term.levels().to_vec(),
            id(index),
        ));
        let copied = composer
            .copy_cursor(&node, index)
            .unwrap_or_else(|_| panic!("changed copy"));
        assert_ne!(copied, expected[index], "payload at {index}");
    }
    for level in [LevelNode::Meta(name("u")), LevelNode::Parameter(name("v"))] {
        let input = cursor(WireExpr::from_parts(
            vec![ExprNode::Sort { level: lid(0) }],
            vec![level.clone()],
            id(0),
        ));
        let copied = composer
            .copy_cursor(&input, 0)
            .unwrap_or_else(|_| panic!("level copy"));
        let ExprNode::Sort { level: result } = composer.expressions[copied.index()] else {
            panic!("sort")
        };
        assert_eq!(composer.levels[result.index()], level);
    }
}

#[test]
fn sharing_hits_still_charge_payloads_and_check_cancellation() {
    let term = cursor(all_nodes());
    let fresh = Cursor::closed(Arc::new((*term.arena).clone()), term.root);
    let mut no_cancel = || false;
    let mut composer = Composer::new(
        TermBudget::unlimited(),
        WhnfPhase::RebuildApplication,
        0,
        0,
        &mut no_cancel,
    );
    assert!(composer.copy_cursor(&term, 0).is_ok());
    composer.control.budget.max_output_units = composer.control.output_units;
    assert!(
        matches!(composer.copy_cursor(&fresh, 1), Err(Halt::Stop(stop)) if matches!(*stop, WhnfStop::Materialization { stop: TermStop::Resource { limit: TermLimit::OutputUnits, .. }, .. }))
    );

    let input = split_application(5);
    let pristine = input.clone();
    let mut polls = 0;
    let success = whnf_with(
        &input,
        &WhnfContext::default(),
        WhnfBudget::unlimited(),
        || {
            polls += 1;
            false
        },
    );
    assert!(matches!(&success, WhnfOutcome::Complete(_)));
    for at in 1..=polls {
        let mut calls = 0;
        let stopped = whnf_with(
            &input,
            &WhnfContext::default(),
            WhnfBudget::unlimited(),
            || {
                calls += 1;
                calls == at
            },
        );
        assert!(
            matches!(stopped, WhnfOutcome::Inconclusive(_)),
            "poll {at}: {stopped:?}"
        );
        assert_eq!(input, pristine);
    }
    assert_eq!(
        whnf(&input, &WhnfContext::default(), WhnfBudget::unlimited()),
        success
    );
}

#[test]
fn deep_cross_arena_composition_uses_no_recursive_host_walk() {
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(|| {
            let mut nodes = vec![ExprNode::Free { name: name("x") }];
            for index in 0..4000 {
                nodes.push(ExprNode::Apply {
                    function: id(index),
                    argument: id(index),
                });
            }
            let term = WireExpr::from_parts(nodes, vec![], id(4000));
            let mut no_cancel = || false;
            let mut composer = Composer::new(
                TermBudget::unlimited().with_max_arena_nodes(4001),
                WhnfPhase::RebuildApplication,
                0,
                0,
                &mut no_cancel,
            );
            let left = composer
                .copy_cursor(&cursor(term.clone()), 0)
                .unwrap_or_else(|_| panic!("left copy"));
            let right = composer
                .copy_cursor(&cursor(term), 1)
                .unwrap_or_else(|_| panic!("right copy"));
            assert_eq!(left, right);
            assert_eq!(composer.expressions.len(), 4001);
        })
        .unwrap()
        .join()
        .unwrap();
}
