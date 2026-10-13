use super::*;
use crate::wire::NamePart;

fn lid(index: usize) -> LevelId {
    LevelId::from_index(index).expect("test level index")
}

fn eid(index: usize) -> ExprId {
    ExprId::from_index(index).expect("test expression index")
}

fn name(text: &str) -> WireName {
    WireName::from_parts(vec![NamePart::Text(text.to_owned())])
}

fn complete<T: std::fmt::Debug>(outcome: InstantiationOutcome<T>) -> T {
    match outcome {
        InstantiationOutcome::Complete(value) => value,
        other => panic!("expected complete instantiation: {other:?}"),
    }
}

fn two_sorts() -> WireExpr {
    WireExpr::from_parts(
        vec![
            ExprNode::Sort { level: lid(0) },
            ExprNode::Sort { level: lid(1) },
            ExprNode::Apply {
                function: eid(0),
                argument: eid(1),
            },
        ],
        vec![
            LevelNode::Parameter(name("u")),
            LevelNode::Parameter(name("v")),
        ],
        eid(2),
    )
}

#[test]
fn overlapping_replacements_share_nodes_across_distinct_expressions() {
    let source = vec![
        LevelNode::Zero,
        LevelNode::Succ(lid(0)),
        LevelNode::Succ(lid(1)),
        // This is intentionally not reduced by mk_max: replacements are values.
        LevelNode::Max(lid(1), lid(2)),
    ];
    for roots in [[lid(1), lid(3)], [lid(3), lid(1)]] {
        let result = complete(instantiate_term_parameters_from_level_roots_with(
            &two_sorts(),
            &[name("u"), name("v")],
            &source,
            &roots,
            // 2 parameters + 3 expressions + 2 subject levels + 4 shared nodes.
            TermBudget::new(11, 7).with_max_arena_nodes(4),
            &mut || false,
        ));
        assert_eq!(result.levels(), source.as_slice());
        assert_eq!(result.nodes()[0], ExprNode::Sort { level: roots[0] });
        assert_eq!(result.nodes()[1], ExprNode::Sort { level: roots[1] });
    }
}

#[test]
fn repeated_replacement_roots_do_not_duplicate_large_successor_chains() {
    let mut source = vec![LevelNode::Zero];
    for index in 1..=4_000 {
        source.push(LevelNode::Succ(lid(index - 1)));
    }
    let result = complete(instantiate_term_parameters_from_level_roots_with(
        &two_sorts(),
        &[name("u"), name("v")],
        &source,
        &[lid(4_000), lid(4_000)],
        TermBudget::new(4_008, 4_004).with_max_arena_nodes(4_001),
        &mut || false,
    ));
    assert_eq!(result.levels(), source.as_slice());
    assert_eq!(result.nodes()[0], result.nodes()[1]);
}

#[test]
fn equal_indexes_in_separate_arenas_do_not_alias() {
    let result = complete(instantiate_term_parameters(
        &two_sorts(),
        &[name("u"), name("v")],
        &[
            WireLevel::from_parts(vec![LevelNode::Zero], lid(0)),
            WireLevel::from_parts(vec![LevelNode::Parameter(name("u"))], lid(0)),
        ],
        TermBudget::unlimited(),
    ));
    assert_eq!(
        result.levels(),
        &[LevelNode::Zero, LevelNode::Parameter(name("u"))],
    );
    assert_eq!(result.nodes()[0], ExprNode::Sort { level: lid(0) });
    assert_eq!(result.nodes()[1], ExprNode::Sort { level: lid(1) });
}

#[test]
fn shared_replacements_remain_simultaneous_literal_values() {
    let source = vec![
        LevelNode::Parameter(name("u")),
        LevelNode::Zero,
        LevelNode::IMax(lid(0), lid(1)),
    ];
    let result = complete(instantiate_term_parameters_from_level_roots_with(
        &two_sorts(),
        &[name("u"), name("v")],
        &source,
        &[lid(2), lid(2)],
        TermBudget::unlimited(),
        &mut || false,
    ));
    // The literal IMax must neither collapse to zero nor recursively substitute u.
    assert_eq!(result.levels().len(), 3);
    let ExprNode::Sort { level } = result.nodes()[0] else {
        panic!("sort expected");
    };
    let Some(LevelNode::IMax(left, right)) = result.level(level) else {
        panic!("literal replacement IMax expected");
    };
    assert_eq!(result.level(*left), Some(&LevelNode::Parameter(name("u"))));
    assert_eq!(result.level(*right), Some(&LevelNode::Zero));
    assert_eq!(result.nodes()[0], result.nodes()[1]);
}

#[test]
fn unused_replacement_roots_are_not_visited() {
    let term = WireExpr::from_parts(
        vec![ExprNode::Sort { level: lid(0) }],
        vec![LevelNode::Parameter(name("u"))],
        eid(0),
    );
    let result = complete(instantiate_term_parameters_from_level_roots_with(
        &term,
        &[name("u"), name("v")],
        &[LevelNode::Zero],
        &[lid(0), lid(99)],
        TermBudget::new(5, 2).with_max_arena_nodes(1),
        &mut || false,
    ));
    assert_eq!(result.levels(), &[LevelNode::Zero]);
}

#[test]
fn shared_cache_does_not_hide_a_corrupt_later_replacement() {
    let outcome = instantiate_term_parameters_from_level_roots_with(
        &two_sorts(),
        &[name("u"), name("v")],
        &[LevelNode::Zero, LevelNode::Succ(lid(1))],
        &[lid(0), lid(1)],
        TermBudget::unlimited(),
        &mut || false,
    );
    assert_eq!(
        outcome,
        InstantiationOutcome::InternalFault(InstantiationFault::NonBackwardLevelReference {
            input: InstantiationInput::Replacement { index: 1 },
            parent: 1,
            child: 1,
        },)
    );
    assert!(matches!(
        instantiate_term_parameters_from_level_roots_with(
            &two_sorts(),
            &[name("u"), name("v")],
            &[LevelNode::Zero],
            &[lid(0), lid(99)],
            TermBudget::unlimited(),
            &mut || false,
        ),
        InstantiationOutcome::InternalFault(InstantiationFault::MissingLevel {
            input: InstantiationInput::Replacement { index: 1 },
            index: 99,
        })
    ));
}

#[test]
fn cancellation_remains_observable_while_smart_constructors_reuse_ancestors() {
    let depth = 100;
    let mut source = vec![LevelNode::Parameter(name("u"))];
    for index in 1..=depth {
        source.push(LevelNode::Max(lid(index - 1), lid(0)));
    }
    let subject = WireLevel::from_parts(source, lid(depth));
    let mut polls = 0;
    let outcome = instantiate_level_parameters_with(
        &subject,
        &[name("u")],
        &[WireLevel::from_parts(vec![LevelNode::Zero], lid(0))],
        TermBudget::unlimited(),
        || {
            polls += 1;
            polls == depth + 20
        },
    );
    assert!(matches!(
        outcome,
        InstantiationOutcome::Inconclusive(TermStop::Cancelled { .. })
    ));
}

#[test]
fn shared_copy_cancellation_never_publishes_partial_terms() {
    let subject = two_sorts();
    let parameters = [name("u"), name("v")];
    let source = [LevelNode::Zero, LevelNode::Succ(lid(0))];
    let roots = [lid(1), lid(1)];
    let mut total = 0;
    complete(instantiate_term_parameters_from_level_roots_with(
        &subject,
        &parameters,
        &source,
        &roots,
        TermBudget::unlimited(),
        &mut || {
            total += 1;
            false
        },
    ));
    for stop_at in 1..=total {
        let mut polls = 0;
        let outcome = instantiate_term_parameters_from_level_roots_with(
            &subject,
            &parameters,
            &source,
            &roots,
            TermBudget::unlimited(),
            &mut || {
                polls += 1;
                polls == stop_at
            },
        );
        assert!(matches!(
            outcome,
            InstantiationOutcome::Inconclusive(TermStop::Cancelled { .. })
        ));
    }
}
