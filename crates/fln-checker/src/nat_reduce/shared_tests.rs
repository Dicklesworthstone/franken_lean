//! Shared arithmetic is checked over independent wire graphs, not expanded trees.
use super::*;

fn id(index: usize) -> ExprId {
    ExprId::from_index(index).unwrap()
}
fn name(namespace: &str, leaf: &str) -> WireName {
    WireName::from_parts(vec![
        NamePart::Text(namespace.into()),
        NamePart::Text(leaf.into()),
    ])
}
fn literal(value: u64) -> WireExpr {
    WireExpr::from_parts(
        vec![ExprNode::NatLiteral {
            limbs_le: if value == 0 { vec![] } else { vec![value] },
        }],
        vec![],
        id(0),
    )
}
fn doubling(depth: usize) -> WireExpr {
    let mut nodes = vec![
        ExprNode::Constant {
            name: name("Nat", "add"),
            levels: vec![],
        },
        ExprNode::NatLiteral { limbs_le: vec![1] },
    ];
    let mut root = id(1);
    for _ in 0..depth {
        let partial = id(nodes.len());
        nodes.push(ExprNode::Apply {
            function: id(0),
            argument: root,
        });
        nodes.push(ExprNode::Apply {
            function: partial,
            argument: root,
        });
        root = id(nodes.len() - 1);
    }
    WireExpr::from_parts(nodes, vec![], root)
}
fn result(outcome: NatReductionOutcome) -> NatReductionResult {
    match outcome {
        NatReductionOutcome::Reduced(result) => result,
        other => panic!("expected completed arithmetic, got {other:?}"),
    }
}
fn value(term: &WireExpr) -> &[u64] {
    match term.node(term.root()).unwrap() {
        ExprNode::NatLiteral { limbs_le } => limbs_le,
        other => panic!("expected natural, got {other:?}"),
    }
}

#[test]
fn shared_doubling_uses_graph_work_not_exponential_tree_work() {
    let input = doubling(32);
    assert_eq!(input.nodes().len(), 66);
    let mut budget = NatReductionBudget::unlimited();
    budget.max_steps = 10_000;
    budget.max_work_items = 10_000;
    let computed = result(reduce_nat(
        &input,
        &literal(0),
        &WhnfContext::default(),
        budget,
    ));
    assert_eq!(value(&computed.term), &[1 << 32]);
    assert_eq!(computed.progress.numeric_reductions, 32);
}

#[test]
fn deep_shared_arithmetic_and_large_literals_use_the_heap() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let input = doubling(1024);
            let mut budget = NatReductionBudget::unlimited();
            budget.max_steps = 100_000;
            budget.max_work_items = 100_000;
            let computed = result(reduce_nat(
                &input,
                &literal(0),
                &WhnfContext::default(),
                budget,
            ));
            let mut expected = vec![0; 17];
            expected[16] = 1;
            assert_eq!(value(&computed.term), expected);
            assert_eq!(computed.progress.numeric_reductions, 1024);
        })
        .unwrap()
        .join()
        .unwrap();
}

fn apply(nodes: &mut Vec<ExprNode>, function: ExprId, argument: ExprId) -> ExprId {
    let root = id(nodes.len());
    nodes.push(ExprNode::Apply { function, argument });
    root
}

#[test]
fn independently_generated_shared_dags_agree_with_bounded_integer_arithmetic() {
    let mut random = 71_u64;
    for _ in 0..128 {
        let mut nodes: Vec<_> = ["add", "sub", "xor", "land", "lor"]
            .into_iter()
            .map(|op| ExprNode::Constant {
                name: name("Nat", op),
                levels: vec![],
            })
            .collect();
        let mut values = Vec::new();
        for n in [0_u64, 1, 7, 23] {
            values.push((id(nodes.len()), n));
            nodes.push(ExprNode::NatLiteral {
                limbs_le: if n == 0 { vec![] } else { vec![n] },
            });
        }
        for _ in 0..80 {
            random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
            let a = values[(random as usize) % values.len()];
            let b = values[((random >> 32) as usize) % values.len()];
            let operation = (random >> 16) as usize % 5;
            let expected = match operation {
                0 => a.1.checked_add(b.1).unwrap(),
                1 => a.1.saturating_sub(b.1),
                2 => a.1 ^ b.1,
                3 => a.1 & b.1,
                _ => a.1 | b.1,
            };
            let partial = apply(&mut nodes, id(operation), a.0);
            let root = apply(&mut nodes, partial, b.0);
            values.push((root, expected));
        }
        let (root, expected) = *values.last().unwrap();
        let input = WireExpr::from_parts(nodes, vec![], root);
        let computed = result(reduce_nat(
            &input,
            &literal(0),
            &WhnfContext::default(),
            NatReductionBudget::unlimited(),
        ));
        assert_eq!(value(&computed.term), value(&literal(expected)));
    }
}

#[test]
fn distinct_normalized_arenas_never_alias_equal_numeric_indices() {
    use crate::wire::BinderStyle;
    // (fun x => Nat.add x x) 7 and the same lambda at 11 have the
    // same source body but acquire different materialized argument arenas.
    let mut nodes = vec![
        ExprNode::Constant {
            name: name("Nat", "add"),
            levels: vec![],
        },
        ExprNode::Constant {
            name: WireName::from_parts(vec![NamePart::Text("Nat".into())]),
            levels: vec![],
        },
        ExprNode::Bound { index: 0 },
    ];
    let partial = apply(&mut nodes, id(0), id(2));
    let body = apply(&mut nodes, partial, id(2));
    let lambda = id(nodes.len());
    nodes.push(ExprNode::Lambda {
        binder_name: name("local", "x"),
        binder_type: id(1),
        body,
        style: BinderStyle::Default,
    });
    let mut operands = Vec::new();
    for n in [7, 11] {
        let arg = id(nodes.len());
        nodes.push(ExprNode::NatLiteral { limbs_le: vec![n] });
        operands.push(apply(&mut nodes, lambda, arg));
    }
    let partial = apply(&mut nodes, id(0), operands[0]);
    let root = apply(&mut nodes, partial, operands[1]);
    let input = WireExpr::from_parts(nodes, vec![], root);
    let computed = result(reduce_nat(
        &input,
        &literal(0),
        &WhnfContext::default(),
        NatReductionBudget::unlimited(),
    ));
    assert_eq!(value(&computed.term), &[36]);
}

#[test]
fn a_completed_subgraph_cannot_hide_a_later_malformed_or_non_natural_operand() {
    for bad in [
        ExprNode::NatLiteral { limbs_le: vec![0] },
        ExprNode::StringLiteral("not a natural".into()),
    ] {
        let shared = doubling(8);
        let mut nodes = shared.nodes().to_vec();
        let other = id(nodes.len());
        nodes.push(bad);
        let partial = apply(&mut nodes, id(0), shared.root());
        let root = apply(&mut nodes, partial, other);
        let input = WireExpr::from_parts(nodes, vec![], root);
        assert!(!matches!(
            reduce_nat(
                &input,
                &literal(0),
                &WhnfContext::default(),
                NatReductionBudget::unlimited()
            ),
            NatReductionOutcome::Reduced(_)
        ));
    }
}

#[test]
fn completed_results_never_cross_contexts_or_closed_pair_gates() {
    use crate::environment::{
        ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety, DefinitionBody,
        DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
    };
    let input = WireExpr::from_parts(
        vec![
            ExprNode::Constant {
                name: name("Nat", "add"),
                levels: vec![],
            },
            ExprNode::Constant {
                name: name("Fixture", "input"),
                levels: vec![],
            },
            ExprNode::Apply {
                function: id(0),
                argument: id(1),
            },
            ExprNode::Apply {
                function: id(2),
                argument: id(1),
            },
            ExprNode::Apply {
                function: id(0),
                argument: id(3),
            },
            ExprNode::Apply {
                function: id(4),
                argument: id(3),
            },
        ],
        vec![],
        id(5),
    );
    for n in [7, 11, 7] {
        let declaration = ConstantDeclaration::definition(
            vec![],
            literal(0),
            ConstantSafety::Safe,
            DefinitionBody::new(
                literal(n),
                ReducibilityHint::Regular(1),
                DefinitionSafety::Safe,
                vec![],
            ),
        );
        let environment = match ConstantEnvironment::build(
            vec![ConstantEntry::new(name("Fixture", "input"), declaration)],
            EnvironmentBudget::unlimited(),
        ) {
            EnvironmentOutcome::Complete { environment, .. } => environment,
            other => panic!("invalid context: {other:?}"),
        };
        let context = WhnfContext::new(vec![], vec![], environment);
        let computed = result(reduce_nat(
            &input,
            &literal(0),
            &context,
            NatReductionBudget::unlimited(),
        ));
        assert_eq!(value(&computed.term), &[4 * n]);
        let open = WireExpr::from_parts(
            vec![ExprNode::Free {
                name: name("local", "open"),
            }],
            vec![],
            id(0),
        );
        assert!(matches!(
            reduce_nat(&input, &open, &context, NatReductionBudget::unlimited()),
            NatReductionOutcome::NotReduced {
                reason: NatNotReduced::OpenPair {
                    input: NatReductionInput::Companion
                },
                ..
            }
        ));
    }
}

#[test]
fn every_shared_reduction_cancellation_checkpoint_remains_a_nonanswer() {
    let input = doubling(8);
    let companion = literal(0);
    let mut polls = 0;
    let expected = result(reduce_nat_with(
        &input,
        &companion,
        &WhnfContext::default(),
        NatReductionBudget::unlimited(),
        || {
            polls += 1;
            false
        },
    ));
    for stop in 1..=polls {
        let mut current = 0;
        assert!(
            matches!(
                reduce_nat_with(
                    &input,
                    &companion,
                    &WhnfContext::default(),
                    NatReductionBudget::unlimited(),
                    || {
                        current += 1;
                        current == stop
                    }
                ),
                NatReductionOutcome::Inconclusive(_)
            ),
            "cancellation {stop}/{polls} was lost"
        );
    }
    let recovered = result(reduce_nat(
        &input,
        &companion,
        &WhnfContext::default(),
        NatReductionBudget::unlimited(),
    ));
    assert_eq!(recovered, expected);
}

#[test]
fn shared_reduction_exact_and_one_less_budgets_include_cache_copies() {
    let input = doubling(16);
    let companion = literal(0);
    let context = WhnfContext::default();
    let computed = result(reduce_nat(
        &input,
        &companion,
        &context,
        NatReductionBudget::unlimited(),
    ));
    let p = computed.progress;
    let exact = NatReductionBudget::new(
        p.steps,
        p.work_items,
        p.generated_arenas,
        p.materialized_arena_nodes,
        p.materialized_owned_units,
        p.output_units,
        WhnfBudget::new(
            p.whnf_steps,
            p.whnf_reductions,
            crate::term::TermBudget::unlimited(),
        ),
        NatBudget::new(p.numeric_steps, p.numeric_materialized_limbs),
    );
    assert_eq!(
        result(reduce_nat(&input, &companion, &context, exact)),
        computed
    );
    for dimension in 0..8 {
        let mut limited = exact;
        let limit = match dimension {
            0 => &mut limited.max_steps,
            1 => &mut limited.max_work_items,
            2 => &mut limited.max_generated_arenas,
            3 => &mut limited.max_materialized_arena_nodes,
            4 => &mut limited.max_materialized_owned_units,
            5 => &mut limited.max_output_units,
            6 => &mut limited.numeric.max_steps,
            _ => &mut limited.numeric.max_materialized_limbs,
        };
        assert!(*limit > 0);
        *limit -= 1;
        assert!(
            matches!(
                reduce_nat(&input, &companion, &context, limited),
                NatReductionOutcome::Inconclusive(_)
            ),
            "dimension {dimension} was not accounted for"
        );
    }
}

fn definition_chain(depth: usize) -> (WireExpr, WhnfContext) {
    use crate::environment::{
        ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety, DefinitionBody,
        DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
    };
    let mut entries = Vec::new();
    for index in 0..depth {
        let body = if index == 0 {
            literal(1)
        } else {
            WireExpr::from_parts(
                vec![
                    ExprNode::Constant {
                        name: name("Nat", "add"),
                        levels: vec![],
                    },
                    ExprNode::Constant {
                        name: name("Fixture", &format!("n{}", index - 1)),
                        levels: vec![],
                    },
                    ExprNode::Apply {
                        function: id(0),
                        argument: id(1),
                    },
                    ExprNode::Apply {
                        function: id(2),
                        argument: id(1),
                    },
                ],
                vec![],
                id(3),
            )
        };
        let type_ = WireExpr::from_parts(
            vec![ExprNode::Constant {
                name: WireName::from_parts(vec![NamePart::Text("Nat".into())]),
                levels: vec![],
            }],
            vec![],
            id(0),
        );
        entries.push(ConstantEntry::new(
            name("Fixture", &format!("n{index}")),
            ConstantDeclaration::definition(
                vec![],
                type_,
                ConstantSafety::Safe,
                DefinitionBody::new(
                    body,
                    ReducibilityHint::Regular(index as u32),
                    DefinitionSafety::Safe,
                    vec![],
                ),
            ),
        ));
    }
    let environment = match ConstantEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("invalid definition chain: {other:?}"),
    };
    let input = WireExpr::from_parts(
        vec![
            ExprNode::Constant {
                name: name("Nat", "add"),
                levels: vec![],
            },
            ExprNode::Constant {
                name: name("Fixture", &format!("n{}", depth - 1)),
                levels: vec![],
            },
            ExprNode::Apply {
                function: id(0),
                argument: id(1),
            },
            ExprNode::Apply {
                function: id(2),
                argument: id(1),
            },
        ],
        vec![],
        id(3),
    );
    (input, WhnfContext::new(vec![], vec![], environment))
}

#[test]
fn shared_definition_bodies_reuse_the_original_operand_after_delta() {
    let (input, context) = definition_chain(32);
    let mut budget = NatReductionBudget::unlimited();
    budget.max_steps = 10_000;
    budget.max_work_items = 10_000;
    let computed = result(reduce_nat(&input, &literal(0), &context, budget));
    assert_eq!(value(&computed.term), &[1 << 32]);
    assert_eq!(computed.progress.numeric_reductions, 32);
    assert!(computed.progress.generated_arenas < 256);
}

#[test]
fn shared_beta_redexes_reuse_only_the_value_under_their_own_argument() {
    use crate::wire::BinderStyle;
    let body = doubling(12);
    let mut nodes = body.nodes().to_vec();
    let nat = id(nodes.len());
    nodes.push(ExprNode::Constant {
        name: WireName::from_parts(vec![NamePart::Text("Nat".into())]),
        levels: vec![],
    });
    let variable = id(nodes.len());
    nodes.push(ExprNode::Bound { index: 0 });
    let partial = apply(&mut nodes, id(0), body.root());
    let result_body = apply(&mut nodes, partial, variable);
    let lambda = id(nodes.len());
    nodes.push(ExprNode::Lambda {
        binder_name: name("local", "x"),
        binder_type: nat,
        body: result_body,
        style: BinderStyle::Default,
    });
    let argument = id(nodes.len());
    nodes.push(ExprNode::NatLiteral { limbs_le: vec![7] });
    let redex = apply(&mut nodes, lambda, argument);
    let partial = apply(&mut nodes, id(0), redex);
    let root = apply(&mut nodes, partial, redex);
    let input = WireExpr::from_parts(nodes, vec![], root);
    let computed = result(reduce_nat(
        &input,
        &literal(0),
        &WhnfContext::default(),
        NatReductionBudget::unlimited(),
    ));
    assert_eq!(value(&computed.term), &[2 * ((1 << 12) + 7)]);
    assert_eq!(computed.progress.numeric_reductions, 14);
}

#[test]
fn conversion_distinguishes_the_wrong_result_from_exhaustion() {
    use crate::defeq::{DefEqBudget, DefEqOutcome, def_eq};
    let (input, context) = definition_chain(24);
    let mut budget = DefEqBudget::unlimited();
    budget.nat.max_steps = 20_000;
    assert!(matches!(
        def_eq(&input, &literal(1 << 24), &context, budget),
        DefEqOutcome::Equal(_)
    ));
    assert!(matches!(
        def_eq(&input, &literal((1 << 24) + 1), &context, budget),
        DefEqOutcome::NotEqual { .. }
    ));
    budget.nat.max_steps = 1;
    assert!(matches!(
        def_eq(&input, &literal(1 << 24), &context, budget),
        DefEqOutcome::Inconclusive(_)
    ));
}

#[test]
fn every_definition_reuse_checkpoint_remains_cancellable() {
    let (input, context) = definition_chain(4);
    let companion = literal(0);
    let mut polls = 0;
    let expected = result(reduce_nat_with(
        &input,
        &companion,
        &context,
        NatReductionBudget::unlimited(),
        || {
            polls += 1;
            false
        },
    ));
    for stop in 1..=polls {
        let mut current = 0;
        // WhnfContext retains validated environment caches. Rebuild the cold
        // context so each run traverses the same checkpoints as the measured run.
        let (input, context) = definition_chain(4);
        let outcome = reduce_nat_with(
            &input,
            &companion,
            &context,
            NatReductionBudget::unlimited(),
            || {
                current += 1;
                current == stop
            },
        );
        assert!(
            matches!(outcome, NatReductionOutcome::Inconclusive(_)),
            "definition cancellation {stop}/{polls} was lost: {outcome:?}"
        );
    }
    assert_eq!(
        result(reduce_nat(
            &input,
            &companion,
            &context,
            NatReductionBudget::unlimited()
        )),
        expected
    );
}

#[test]
fn polymorphic_constants_are_never_keyed_by_name_alone() {
    use crate::wire::{LevelId, LevelNode};
    let constant = name("Fixture", "polymorphic");
    let input = WireExpr::from_parts(
        vec![
            ExprNode::Constant {
                name: constant.clone(),
                levels: vec![LevelId::from_index(0).unwrap()],
            },
            ExprNode::Constant {
                name: constant,
                levels: vec![LevelId::from_index(1).unwrap()],
            },
        ],
        vec![
            LevelNode::Zero,
            LevelNode::Succ(LevelId::from_index(0).unwrap()),
        ],
        id(1),
    );
    for index in 0..2 {
        assert!(matches!(
            operand_name(
                Cursor {
                    source: ArenaSource::Candidate,
                    root: id(index)
                },
                &input,
                &[]
            ),
            Ok(None)
        ));
    }
}

#[test]
fn a_cached_monomorphic_name_cannot_hide_a_later_universe_arity_error() {
    use crate::wire::{LevelId, LevelNode};
    let (_, context) = definition_chain(4);
    let shared_name = name("Fixture", "n3");
    let mut nodes = vec![
        ExprNode::Constant {
            name: name("Nat", "add"),
            levels: vec![],
        },
        ExprNode::Constant {
            name: shared_name.clone(),
            levels: vec![],
        },
        ExprNode::Constant {
            name: shared_name,
            levels: vec![LevelId::from_index(0).unwrap()],
        },
    ];
    // The first operand completes and makes its monomorphic name available.
    // The later occurrence is NOT that constant application: it has bad arity.
    let partial = apply(&mut nodes, id(0), id(1));
    let root = apply(&mut nodes, partial, id(2));
    let term = WireExpr::from_parts(nodes, vec![LevelNode::Zero], root);
    assert!(matches!(
        reduce_nat(
            &term,
            &literal(0),
            &context,
            NatReductionBudget::unlimited()
        ),
        NatReductionOutcome::Refused { .. }
    ));
}

#[test]
fn warm_definition_contexts_keep_their_own_cancellation_checkpoints() {
    let (input, context) = definition_chain(4);
    let zero = literal(0);
    result(reduce_nat(
        &input,
        &zero,
        &context,
        NatReductionBudget::unlimited(),
    ));
    let mut polls = 0;
    let expected = result(reduce_nat_with(
        &input,
        &zero,
        &context,
        NatReductionBudget::unlimited(),
        || {
            polls += 1;
            false
        },
    ));
    for stop in 1..=polls {
        let mut current = 0;
        let outcome = reduce_nat_with(
            &input,
            &zero,
            &context,
            NatReductionBudget::unlimited(),
            || {
                current += 1;
                current == stop
            },
        );
        assert!(
            matches!(outcome, NatReductionOutcome::Inconclusive(_)),
            "warm checkpoint {stop}/{polls}: {outcome:?}"
        );
    }
    assert_eq!(
        result(reduce_nat(
            &input,
            &zero,
            &context,
            NatReductionBudget::unlimited()
        )),
        expected
    );
}
