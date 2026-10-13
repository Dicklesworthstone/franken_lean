use super::*;
use crate::wire::{BinderStyle, MetadataValue, NamePart};

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

fn legacy_level(level: &WireLevel, parameters: &[WireName], values: &[WireLevel]) -> WireLevel {
    let mut cancelled = || false;
    let mut instantiator = match Instantiator::prepare(
        parameters,
        ReplacementValues::Separate(values),
        TermBudget::unlimited(),
        &mut cancelled,
    ) {
        Ok(Ok(instantiator)) => instantiator,
        _ => panic!("legacy instantiator preparation"),
    };
    let mapping = instantiator
        .map_subject_levels(level.nodes())
        .unwrap_or_else(|_| panic!("legacy level mapping"));
    WireLevel::from_parts(instantiator.levels, mapping[level.root().index()])
}

fn legacy_term(term: &WireExpr, parameters: &[WireName], values: &[WireLevel]) -> WireExpr {
    let mut cancelled = || false;
    let mut instantiator = match Instantiator::prepare(
        parameters,
        ReplacementValues::Separate(values),
        TermBudget::unlimited(),
        &mut cancelled,
    ) {
        Ok(Ok(instantiator)) => instantiator,
        _ => panic!("legacy instantiator preparation"),
    };
    let levels = instantiator
        .map_subject_levels(term.levels())
        .unwrap_or_else(|_| panic!("legacy level mapping"));
    let nodes = instantiator
        .copy_expressions(term, &levels)
        .unwrap_or_else(|_| panic!("legacy expression copying"));
    WireExpr::from_parts(nodes, instantiator.levels, term.root())
}

fn assert_same_level(left: &WireLevel, right: &WireLevel) {
    let mut work = vec![(left.root(), right.root())];
    let mut seen = BTreeSet::new();
    while let Some((a, b)) = work.pop() {
        if !seen.insert((a, b)) {
            continue;
        }
        match (left.node(a), right.node(b)) {
            (Some(LevelNode::Zero), Some(LevelNode::Zero)) => {}
            (Some(LevelNode::Parameter(a)), Some(LevelNode::Parameter(b)))
            | (Some(LevelNode::Meta(a)), Some(LevelNode::Meta(b))) => assert_eq!(a, b),
            (Some(LevelNode::Succ(a)), Some(LevelNode::Succ(b))) => work.push((*a, *b)),
            (Some(LevelNode::Max(a, b)), Some(LevelNode::Max(c, d)))
            | (Some(LevelNode::IMax(a, b)), Some(LevelNode::IMax(c, d))) => {
                work.push((*a, *c));
                work.push((*b, *d));
            }
            pair => panic!("different literal level structures: {pair:?}"),
        }
    }
}

#[test]
fn sparse_level_subject_does_not_spend_the_unrelated_arena() {
    let mut nodes = vec![LevelNode::Zero; 20_000];
    nodes[10_000] = LevelNode::Parameter(name("u"));
    let subject = WireLevel::from_parts(nodes, lid(10_000));
    let replacement = WireLevel::from_parts(vec![LevelNode::Zero, LevelNode::Succ(lid(0))], lid(1));
    // One parameter, one subject node, and two replacement nodes.
    let result = complete(instantiate_level_parameters(
        &subject,
        &[name("u")],
        std::slice::from_ref(&replacement),
        TermBudget::new(4, 2).with_max_arena_nodes(2),
    ));
    assert_eq!(result, replacement);
}

#[test]
fn sparse_term_subject_omits_unused_expressions_and_universes() {
    let literal = ExprNode::NatLiteral { limbs_le: vec![7] };
    let mut nodes = vec![ExprNode::StringLiteral("unrelated".to_owned()); 20_000];
    nodes[10_000] = literal.clone();
    let term = WireExpr::from_parts(nodes, vec![LevelNode::Zero; 20_000], eid(10_000));
    let result = complete(instantiate_term_parameters(
        &term,
        &[],
        &[],
        TermBudget::new(1, 2).with_max_arena_nodes(1),
    ));
    assert_eq!(result.nodes(), &[literal]);
    assert!(result.levels().is_empty());
    assert_eq!(result.root(), eid(0));
}

#[test]
fn every_expression_edge_is_remapped_without_erasing_payload() {
    let metadata = vec![
        (name("source"), MetadataValue::Text("a λ".to_owned())),
        (name("flag"), MetadataValue::Bool(true)),
        (name("name"), MetadataValue::Name(name("original"))),
        (name("nat"), MetadataValue::Nat(17)),
        (name("int"), MetadataValue::Int(-9)),
        (name("syntax"), MetadataValue::Syntax(23)),
    ];
    let make_nodes = |offset: usize, level: LevelId| {
        vec![
            ExprNode::Sort { level },
            ExprNode::Bound { index: 0 },
            ExprNode::Constant {
                name: name("f"),
                levels: vec![level, level],
            },
            ExprNode::Apply {
                function: eid(offset + 2),
                argument: eid(offset + 1),
            },
            ExprNode::Lambda {
                binder_name: name("x"),
                binder_type: eid(offset),
                body: eid(offset + 3),
                style: BinderStyle::Implicit,
            },
            ExprNode::Forall {
                binder_name: name("A"),
                binder_type: eid(offset),
                body: eid(offset + 4),
                style: BinderStyle::StrictImplicit,
            },
            ExprNode::Let {
                declaration_name: name("y"),
                type_: eid(offset),
                value: eid(offset + 2),
                body: eid(offset + 5),
                non_dependent: true,
            },
            ExprNode::Metadata {
                entries: metadata.clone(),
                expression: eid(offset + 6),
            },
            ExprNode::Projection {
                structure_name: name("Pair"),
                index: 1,
                expression: eid(offset + 7),
            },
        ]
    };
    let mut nodes = vec![ExprNode::StringLiteral("dead prefix".to_owned())];
    nodes.extend(make_nodes(1, lid(1)));
    let term = WireExpr::from_parts(
        nodes,
        vec![LevelNode::Zero, LevelNode::Parameter(name("u"))],
        eid(9),
    );
    let replacement = WireLevel::from_parts(vec![LevelNode::Parameter(name("v"))], lid(0));
    let result = complete(instantiate_term_parameters(
        &term,
        &[name("u")],
        &[replacement],
        TermBudget::unlimited(),
    ));
    assert_eq!(result.nodes(), make_nodes(0, lid(0)).as_slice());
    assert_eq!(result.levels(), &[LevelNode::Parameter(name("v"))]);
    assert_eq!(result.root(), eid(8));
}

#[test]
fn leaf_payloads_are_not_reinterpreted() {
    for node in [
        ExprNode::Bound { index: 19 },
        ExprNode::Free { name: name("free") },
        ExprNode::Meta { name: name("hole") },
        ExprNode::NatLiteral {
            limbs_le: vec![u64::MAX, 1],
        },
        ExprNode::StringLiteral("α\0β".to_owned()),
    ] {
        let term = WireExpr::from_parts(
            vec![ExprNode::Bound { index: 0 }, node.clone()],
            vec![LevelNode::Zero],
            eid(1),
        );
        let result = complete(instantiate_term_parameters(
            &term,
            &[],
            &[],
            TermBudget::unlimited(),
        ));
        assert_eq!(result.nodes(), &[node]);
        assert!(result.levels().is_empty());
    }
}

#[test]
fn substitution_remains_simultaneous_and_repeated_roots_stay_shared() {
    let term = WireExpr::from_parts(
        vec![ExprNode::Constant {
            name: name("c"),
            levels: vec![lid(0), lid(1), lid(0)],
        }],
        vec![LevelNode::Parameter(name("u")), LevelNode::Parameter(name("v"))],
        eid(0),
    );
    let result = complete(instantiate_term_parameters(
        &term,
        &[name("u"), name("v")],
        &[
            WireLevel::from_parts(vec![LevelNode::Parameter(name("v"))], lid(0)),
            WireLevel::from_parts(vec![LevelNode::Zero, LevelNode::Succ(lid(0))], lid(1)),
        ],
        TermBudget::unlimited(),
    ));
    let ExprNode::Constant { levels, .. } = &result.nodes()[0] else {
        panic!("constant expected");
    };
    assert_eq!(levels[0], levels[2]);
    assert!(matches!(result.level(levels[0]), Some(LevelNode::Parameter(n)) if n == &name("v")));
    assert!(matches!(result.level(levels[1]), Some(LevelNode::Succ(_))));
    assert_eq!(result.levels().len(), 3);
}

#[test]
fn unchanged_maximum_is_literal_but_changed_ancestors_use_smart_constructors() {
    let subject = WireLevel::from_parts(
        vec![
            LevelNode::Zero,
            LevelNode::Parameter(name("u")),
            LevelNode::Max(lid(0), lid(1)),
        ],
        lid(2),
    );
    let untouched = complete(instantiate_level_parameters(
        &subject,
        &[],
        &[],
        TermBudget::unlimited(),
    ));
    assert_eq!(untouched, subject);
    let changed = complete(instantiate_level_parameters(
        &subject,
        &[name("u")],
        &[WireLevel::from_parts(vec![LevelNode::Parameter(name("v"))], lid(0))],
        TermBudget::unlimited(),
    ));
    assert_eq!(changed.node(changed.root()), Some(&LevelNode::Parameter(name("v"))));
}

#[test]
fn compact_term_agrees_with_the_previous_whole_arena_implementation() {
    let term = WireExpr::from_parts(
        vec![
            ExprNode::Sort { level: lid(2) },
            ExprNode::Bound { index: 0 },
            ExprNode::Lambda {
                binder_name: name("x"),
                binder_type: eid(0),
                body: eid(1),
                style: BinderStyle::Default,
            },
        ],
        vec![
            LevelNode::Zero,
            LevelNode::Parameter(name("u")),
            LevelNode::Max(lid(0), lid(1)),
        ],
        eid(2),
    );
    let parameters = [name("u")];
    let values = [WireLevel::from_parts(vec![LevelNode::Parameter(name("v"))], lid(0))];
    assert_eq!(
        complete(instantiate_term_parameters(
            &term,
            &parameters,
            &values,
            TermBudget::unlimited(),
        )),
        legacy_term(&term, &parameters, &values),
    );
}

#[test]
fn generated_level_dags_agree_with_the_previous_implementation() {
    let parameters = [name("u"), name("v")];
    let values = [
        WireLevel::from_parts(
            vec![LevelNode::Zero, LevelNode::Parameter(name("v")), LevelNode::Max(lid(0), lid(1))],
            lid(2),
        ),
        WireLevel::from_parts(vec![LevelNode::Zero, LevelNode::Succ(lid(0))], lid(1)),
    ];
    for seed in 0_u64..128 {
        let mut state = seed;
        let mut next = |bound: usize| {
            state = state.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (state % bound as u64) as usize
        };
        let mut nodes = vec![
            LevelNode::Zero,
            LevelNode::Parameter(name("u")),
            LevelNode::Parameter(name("v")),
            LevelNode::Meta(name("m")),
        ];
        for index in 4..128 {
            let left = lid(next(index));
            let right = lid(next(index));
            nodes.push(match next(3) {
                0 => LevelNode::Succ(left),
                1 => LevelNode::Max(left, right),
                _ => LevelNode::IMax(left, right),
            });
        }
        let subject = WireLevel::from_parts(nodes, lid(127));
        let actual = complete(instantiate_level_parameters(
            &subject,
            &parameters,
            &values,
            TermBudget::unlimited(),
        ));
        assert_same_level(&actual, &legacy_level(&subject, &parameters, &values));
    }
}

#[test]
fn deep_shared_terms_and_levels_use_heap_frames_and_linear_work() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let depth = 4_000;
            let mut nodes = vec![ExprNode::NatLiteral { limbs_le: vec![0] }];
            let mut levels = vec![LevelNode::Zero];
            for index in 1..=depth {
                nodes.push(ExprNode::Apply {
                    function: eid(index - 1),
                    argument: eid(index - 1),
                });
                levels.push(LevelNode::Succ(lid(index - 1)));
            }
            let term = WireExpr::from_parts(nodes, Vec::new(), eid(depth));
            let result = complete(instantiate_term_parameters(
                &term,
                &[],
                &[],
                TermBudget::new(depth as u64 + 1, depth as u64 + 2),
            ));
            assert_eq!(result, term);
            let level = WireLevel::from_parts(levels, lid(depth));
            let result = complete(instantiate_level_parameters(
                &level,
                &[],
                &[],
                TermBudget::new(depth as u64 + 1, depth as u64 + 1),
            ));
            assert_eq!(result, level);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn malformed_reachable_references_remain_internal_faults() {
    let bad_level = WireLevel::from_parts(vec![LevelNode::Succ(lid(1))], lid(0));
    assert!(matches!(
        instantiate_level_parameters(&bad_level, &[], &[], TermBudget::unlimited()),
        InstantiationOutcome::InternalFault(InstantiationFault::NonBackwardLevelReference {
            input: InstantiationInput::Subject,
            parent: 0,
            child: 1,
        })
    ));
    let missing_level = WireLevel::from_parts(Vec::new(), lid(0));
    assert!(matches!(
        instantiate_level_parameters(&missing_level, &[], &[], TermBudget::unlimited()),
        InstantiationOutcome::InternalFault(InstantiationFault::MissingLevel { .. })
    ));
    let missing_term = WireExpr::from_parts(Vec::new(), Vec::new(), eid(0));
    assert!(matches!(
        instantiate_term_parameters(&missing_term, &[], &[], TermBudget::unlimited()),
        InstantiationOutcome::InternalFault(InstantiationFault::MissingExpression { index: 0 })
    ));
    let bad_sort = WireExpr::from_parts(vec![ExprNode::Sort { level: lid(0) }], Vec::new(), eid(0));
    assert!(matches!(
        instantiate_term_parameters(&bad_sort, &[], &[], TermBudget::unlimited()),
        InstantiationOutcome::InternalFault(InstantiationFault::MissingLevel {
            input: InstantiationInput::Subject,
            index: 0,
        })
    ));
}

#[test]
fn all_resource_limits_remain_typed_nonanswers() {
    let term = WireExpr::from_parts(
        vec![ExprNode::NatLiteral { limbs_le: vec![7] }],
        Vec::new(),
        eid(0),
    );
    for (budget, expected) in [
        (TermBudget::new(0, 100), TermLimit::Steps),
        (TermBudget::new(100, 1), TermLimit::OutputUnits),
        (
            TermBudget::new(100, 100).with_max_arena_nodes(0),
            TermLimit::ArenaNodes,
        ),
    ] {
        assert!(matches!(
            instantiate_term_parameters(&term, &[], &[], budget),
            InstantiationOutcome::Inconclusive(TermStop::Resource { limit, .. }) if limit == expected
        ));
    }
}

#[test]
fn cancellation_at_each_reachable_checkpoint_never_publishes_partial_output() {
    let term = WireExpr::from_parts(
        vec![ExprNode::Constant { name: name("c"), levels: vec![lid(0), lid(0)] }],
        vec![LevelNode::Parameter(name("u"))],
        eid(0),
    );
    let parameters = [name("u")];
    let values = [WireLevel::from_parts(vec![LevelNode::Zero, LevelNode::Succ(lid(0))], lid(1))];
    let mut total = 0;
    complete(instantiate_term_parameters_with(
        &term,
        &parameters,
        &values,
        TermBudget::unlimited(),
        || {
            total += 1;
            false
        },
    ));
    assert!(total > 4);
    for stop_at in 1..=total {
        let mut polls = 0;
        assert!(matches!(
            instantiate_term_parameters_with(
                &term,
                &parameters,
                &values,
                TermBudget::unlimited(),
                || {
                    polls += 1;
                    polls == stop_at
                },
            ),
            InstantiationOutcome::Inconclusive(TermStop::Cancelled { .. })
        ));
    }
}
