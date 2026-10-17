use super::*;

fn level(index: usize) -> LevelId {
    LevelId::from_index(index).unwrap()
}
fn parameter(name: &str) -> LevelNode {
    LevelNode::Parameter(checker_atom(name))
}
fn sort(nodes: Vec<LevelNode>, root: usize) -> WireExpr {
    WireExpr::from_parts(
        vec![ExprNode::Sort { level: level(root) }],
        nodes,
        ExprId::from_index(0).unwrap(),
    )
}
fn inferred() -> WireExpr {
    sort(
        vec![
            LevelNode::Zero,
            LevelNode::Succ(level(0)),
            parameter("u"),
            LevelNode::Succ(level(2)),
            parameter("v"),
            LevelNode::Succ(level(4)),
            LevelNode::Max(level(1), level(3)),
            LevelNode::Max(level(6), level(5)),
        ],
        7,
    )
}
fn expected() -> WireExpr {
    sort(
        vec![
            parameter("u"),
            LevelNode::Succ(level(0)),
            parameter("v"),
            LevelNode::Succ(level(2)),
            LevelNode::Max(level(1), level(3)),
        ],
        4,
    )
}
fn compare(left: &WireExpr, right: &WireExpr, mode: ReconstructionMode) -> bool {
    structural_expression_equal(
        left,
        right,
        &mut StructuralComparisonControl::new(QuickDefEqBudget::unlimited()),
        mode,
        &mut || false,
    )
    .unwrap()
    .unwrap()
}

#[test]
fn inferred_lower_bounds_and_reordered_maxima_use_independent_universe_equality() {
    let a = inferred();
    let b = expected();
    let mut reordered = b.levels().to_vec();
    reordered[4] = LevelNode::Max(level(3), level(1));
    let c = sort(reordered, 4);
    for (left, right) in [(&a, &b), (&b, &a), (&a, &c), (&c, &a)] {
        assert!(compare(left, right, ReconstructionMode::Inductive));
        assert!(!compare(left, right, ReconstructionMode::Quotient));
    }
    assert!(compare(&a, &a, ReconstructionMode::Quotient));
}

#[test]
fn equivalent_parent_roots_do_not_cache_unequal_children_as_equal() {
    let nodes = vec![
        parameter("u"),
        parameter("v"),
        LevelNode::Max(level(0), level(1)),
        LevelNode::Max(level(1), level(0)),
    ];
    let constant = |roots| {
        WireExpr::from_parts(
            vec![ExprNode::Constant {
                name: checker_atom("Family"),
                levels: roots,
            }],
            nodes.clone(),
            ExprId::from_index(0).unwrap(),
        )
    };
    let left = constant(vec![level(2), level(0)]);
    let right = constant(vec![level(3), level(1)]);
    assert!(!compare(&left, &right, ReconstructionMode::Inductive));
    assert!(!compare(&right, &left, ReconstructionMode::Inductive));
    let same_children = constant(vec![level(3), level(0)]);
    assert!(compare(
        &left,
        &same_children,
        ReconstructionMode::Inductive
    ));
}

#[test]
fn contingent_imax_and_one_pass_incompleteness_are_not_normalized_away() {
    let nodes = vec![
        parameter("u"),
        parameter("v"),
        LevelNode::IMax(level(0), level(1)),
        LevelNode::Max(level(0), level(1)),
    ];
    assert!(!compare(
        &sort(nodes.clone(), 2),
        &sort(nodes, 3),
        ReconstructionMode::Inductive
    ));
    // succ (imax v (succ u)) is deliberately NOT equated with its twice
    // normalized form by KR-501. Reconstructing a type must not take a fixpoint.
    let x = sort(
        vec![
            parameter("u"),
            parameter("v"),
            LevelNode::Succ(level(0)),
            LevelNode::IMax(level(1), level(2)),
            LevelNode::Succ(level(3)),
        ],
        4,
    );
    let twice = sort(
        vec![
            parameter("u"),
            parameter("v"),
            LevelNode::Succ(level(0)),
            LevelNode::Succ(level(1)),
            LevelNode::Succ(level(2)),
            LevelNode::Max(level(3), level(4)),
        ],
        5,
    );
    assert!(!compare(&x, &twice, ReconstructionMode::Inductive));
    assert!(!compare(&twice, &x, ReconstructionMode::Inductive));
}

#[test]
fn only_universes_convert_and_inductive_binder_annotations_remain_exact() {
    let mut levels = expected().levels().to_vec();
    levels[0] = parameter("other");
    assert!(!compare(
        &inferred(),
        &sort(levels, 4),
        ReconstructionMode::Inductive
    ));
    let pi = |style| {
        WireExpr::from_parts(
            vec![
                ExprNode::Sort { level: level(0) },
                ExprNode::Forall {
                    binder_name: checker_atom("x"),
                    binder_type: ExprId::from_index(0).unwrap(),
                    body: ExprId::from_index(0).unwrap(),
                    style,
                },
            ],
            vec![LevelNode::Zero],
            ExprId::from_index(1).unwrap(),
        )
    };
    assert!(!compare(
        &pi(BinderStyle::Default),
        &pi(BinderStyle::Implicit),
        ReconstructionMode::Inductive
    ));
    assert!(compare(
        &pi(BinderStyle::Default),
        &pi(BinderStyle::Implicit),
        ReconstructionMode::Quotient
    ));
}

#[test]
fn level_limits_and_every_cancellation_boundary_remain_nonanswers() {
    let left = inferred();
    let right = expected();
    let mut control = StructuralComparisonControl::new(QuickDefEqBudget::unlimited());
    assert!(
        structural_expression_equal(
            &left,
            &right,
            &mut control,
            ReconstructionMode::Inductive,
            &mut || false
        )
        .unwrap()
        .unwrap()
    );
    for allowed in 0..control.comparisons {
        let budget = QuickDefEqBudget::new(allowed, u64::MAX);
        assert!(matches!(
            structural_expression_equal(
                &left,
                &right,
                &mut StructuralComparisonControl::new(budget),
                ReconstructionMode::Inductive,
                &mut || false
            ),
            Ok(Err(QuickDefEqStop::Resource {
                limit: QuickDefEqLimit::Comparisons,
                ..
            }))
        ));
    }
    let size = (left.levels().len() + right.levels().len()) as u64;
    assert!(matches!(
        structural_expression_equal(
            &left,
            &right,
            &mut StructuralComparisonControl::new(QuickDefEqBudget::new(u64::MAX, size - 1)),
            ReconstructionMode::Inductive,
            &mut || false
        ),
        Ok(Err(QuickDefEqStop::Resource {
            limit: QuickDefEqLimit::LevelArenaNodes,
            ..
        }))
    ));
    for at in 1..=control.polls {
        let mut polls = 0;
        let mut cancel = || {
            polls += 1;
            polls == at
        };
        assert!(
            matches!(
                structural_expression_equal(
                    &left,
                    &right,
                    &mut StructuralComparisonControl::new(QuickDefEqBudget::unlimited()),
                    ReconstructionMode::Inductive,
                    &mut cancel
                ),
                Ok(Err(QuickDefEqStop::Cancelled { .. }))
            ),
            "poll {at}"
        );
    }
    assert!(compare(&left, &right, ReconstructionMode::Inductive));
}

#[test]
fn malformed_level_arenas_cannot_be_rescued_by_normalization() {
    for nodes in [
        vec![LevelNode::Succ(level(0))],
        vec![LevelNode::Max(level(0), level(9))],
    ] {
        let broken = sort(nodes, 0);
        assert!(matches!(
            structural_expression_equal(
                &broken,
                &expected(),
                &mut StructuralComparisonControl::new(QuickDefEqBudget::unlimited()),
                ReconstructionMode::Inductive,
                &mut || false
            ),
            Err(QuickDefEqFault::Universe {
                error: crate::universe::UniverseError::InvalidArena,
                ..
            })
        ));
    }
}

#[test]
fn shared_contingent_universes_use_heap_normalization_without_tree_expansion() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut nodes = vec![parameter("u"), parameter("v")];
            let mut root = 0;
            for _ in 0..2048 {
                let branch = nodes.len();
                nodes.push(LevelNode::IMax(level(1), level(root)));
                let next = nodes.len();
                nodes.push(LevelNode::IMax(level(root), level(branch)));
                root = next;
            }
            let left = sort(nodes.clone(), root);
            nodes.push(LevelNode::Max(level(root), level(root)));
            let right = sort(nodes, root + 1);
            assert!(compare(&left, &right, ReconstructionMode::Inductive));
        })
        .unwrap()
        .join()
        .unwrap();
}
