//! Completed arithmetic nodes within one evaluation, never across queries.
//!
//! Candidate and generated arenas have disjoint, stable identities and remain
//! alive for the whole evaluation. Each key therefore denotes one immutable
//! term under the same context and reduction policy. Only a completed natural
//! result is stored; booleans, refusals, resource stops and partial frames are
//! not reusable natural operands. Context validation still precedes any hit.
mod names;

use super::{Control, Cursor, Halt, NatValue, WireName};
use std::collections::HashMap;
use std::sync::Arc;

const MAX_ENTRIES: usize = 4_096;
const MAX_RETAINED_LIMBS: usize = 65_536;

#[derive(Default)]
pub(super) struct NaturalMemo {
    entries: HashMap<Cursor, Arc<NatValue>>,
    limbs: usize,
    names: names::Names,
}

impl NaturalMemo {
    pub(super) fn recall_operand(
        &self,
        cursor: Cursor,
        name: Option<&WireName>,
        control: &mut Control<'_>,
    ) -> Result<Option<Arc<NatValue>>, Halt> {
        if let Some(value) = self.recall(cursor, control)? {
            return Ok(Some(value));
        }
        if let Some(name) = name
            && let Some(original) = self.names.recall(name, cursor, control)?
        {
            return self.recall(original, control);
        }
        Ok(None)
    }

    pub(super) fn remember_operand(
        &mut self,
        cursor: Cursor,
        name: Option<&WireName>,
        value: &Arc<NatValue>,
        control: &mut Control<'_>,
    ) -> Result<(), Halt> {
        self.remember(cursor, value, control)?;
        // Aliases index retained values only. Saturation of the existing memo
        // cannot produce a dangling alias or circumvent its value/limb caps.
        if let Some(name) = name
            && self.entries.contains_key(&cursor)
        {
            self.names.remember(name, cursor, control)?;
        }
        Ok(())
    }

    pub(super) fn recall(
        &self,
        cursor: Cursor,
        control: &mut Control<'_>,
    ) -> Result<Option<Arc<NatValue>>, Halt> {
        control.step(cursor.root.index())?;
        // Sharing the immutable numeric allocation copies no limbs. The
        // evaluation worklist already bounds the number of live references.
        Ok(self.entries.get(&cursor).map(Arc::clone))
    }

    pub(super) fn remember(
        &mut self,
        cursor: Cursor,
        value: &Arc<NatValue>,
        control: &mut Control<'_>,
    ) -> Result<(), Halt> {
        control.step(cursor.root.index())?;
        let limbs = value.limbs_le().len();
        if self.entries.len() >= MAX_ENTRIES
            || limbs > MAX_RETAINED_LIMBS.saturating_sub(self.limbs)
            || self.entries.contains_key(&cursor)
        {
            return Ok(());
        }
        // Retention is optional. Allocation failure or saturation leaves the
        // ordinary metered evaluator available, with no semantic refusal.
        if self.entries.try_reserve(1).is_err() {
            return Ok(());
        }
        self.entries.insert(cursor, Arc::clone(value));
        self.limbs += limbs;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;

    fn id(n: usize) -> ExprId {
        ExprId::from_index(n).unwrap()
    }
    fn nat(n: u64) -> ExprNode {
        ExprNode::NatLiteral {
            limbs_le: if n == 0 { vec![] } else { vec![n] },
        }
    }
    fn op(s: &str) -> ExprNode {
        ExprNode::Constant {
            name: WireName::from_parts(vec![
                NamePart::Text("Nat".into()),
                NamePart::Text(s.into()),
            ]),
            levels: vec![],
        }
    }
    fn literal(n: u64) -> WireExpr {
        WireExpr::from_parts(vec![nat(n)], vec![], id(0))
    }
    fn push(nodes: &mut Vec<ExprNode>, node: ExprNode) -> ExprId {
        let n = id(nodes.len());
        nodes.push(node);
        n
    }
    fn app(nodes: &mut Vec<ExprNode>, f: ExprId, a: ExprId) -> ExprId {
        push(
            nodes,
            ExprNode::Apply {
                function: f,
                argument: a,
            },
        )
    }
    fn doubling(depth: usize) -> WireExpr {
        let mut nodes = vec![op("add"), nat(1)];
        let mut root = id(1);
        for _ in 0..depth {
            let partial = app(&mut nodes, id(0), root);
            root = app(&mut nodes, partial, root);
        }
        WireExpr::from_parts(nodes, vec![], root)
    }
    fn value(outcome: NatReductionOutcome) -> NatReductionResult {
        match outcome {
            NatReductionOutcome::Reduced(r) => r,
            other => panic!("expected a complete arithmetic result: {other:?}"),
        }
    }
    #[test]
    fn shared_arithmetic_dag_is_evaluated_by_nodes_not_paths() {
        let term = doubling(32);
        let mut budget = NatReductionBudget::unlimited();
        budget.max_steps = 5_000;
        budget.max_work_items = 5_000;
        budget.numeric = NatBudget::new(5_000, 5_000);
        let result = value(reduce_nat(
            &term,
            &literal(0),
            &WhnfContext::default(),
            budget,
        ));
        assert_eq!(
            result.term.node(result.term.root()),
            Some(&nat(1_u64 << 32))
        );
        assert_eq!(result.progress.numeric_reductions, 32);
        assert!(result.progress.steps < 5_000);
    }
    #[test]
    fn shared_multi_limb_results_are_not_mutated_by_their_consumers() {
        let mut term = doubling(128);
        let root = term.root();
        let mut nodes = term.nodes().to_vec();
        let sub = push(&mut nodes, op("sub"));
        let partial = app(&mut nodes, sub, root);
        let zero = app(&mut nodes, partial, root);
        let partial = app(&mut nodes, id(0), root);
        let sum = app(&mut nodes, partial, zero);
        term = WireExpr::from_parts(nodes, vec![], sum);
        let result = value(reduce_nat(
            &term,
            &literal(0),
            &WhnfContext::default(),
            NatReductionBudget::unlimited(),
        ));
        assert_eq!(
            result.term.node(result.term.root()),
            Some(&ExprNode::NatLiteral {
                limbs_le: vec![0, 0, 1]
            })
        );
        assert_eq!(result.progress.numeric_reductions, 130);
    }

    #[test]
    fn generated_arithmetic_dags_match_an_independent_bounded_model() {
        for seed in 0..128_u64 {
            let mut state = seed + 1;
            let mut random = || {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
                state
            };
            let mut nodes = vec![
                op("add"),
                op("sub"),
                op("land"),
                op("lor"),
                op("xor"),
                nat(7),
                nat(11),
            ];
            let mut values = vec![(id(5), 7_u64), (id(6), 11_u64)];
            for _ in 0..48 {
                let (left, a) = values[random() as usize % values.len()];
                let (right, b) = values[random() as usize % values.len()];
                let operation = random() as usize % 5;
                let expected = match operation {
                    0 => a + b,
                    1 => a.saturating_sub(b),
                    2 => a & b,
                    3 => a | b,
                    _ => a ^ b,
                };
                let partial = app(&mut nodes, id(operation), left);
                let root = app(&mut nodes, partial, right);
                values.push((root, expected));
            }
            let (root, expected) = *values.last().unwrap();
            let term = WireExpr::from_parts(nodes, vec![], root);
            let result = value(reduce_nat(
                &term,
                &literal(0),
                &WhnfContext::default(),
                NatReductionBudget::unlimited(),
            ));
            assert_eq!(
                result.term.node(result.term.root()),
                Some(&nat(expected)),
                "seed={seed}"
            );
            assert!(result.progress.numeric_reductions <= 48);
        }
    }

    #[test]
    fn every_cancellation_checkpoint_returns_a_nonanswer_and_fresh_work_recovers() {
        let term = doubling(8);
        let zero = literal(0);
        let mut polls = 0;
        value(reduce_nat_with(
            &term,
            &zero,
            &WhnfContext::default(),
            NatReductionBudget::unlimited(),
            || {
                polls += 1;
                false
            },
        ));
        for stop_at in 1..=polls {
            let mut seen = 0;
            let result = reduce_nat_with(
                &term,
                &zero,
                &WhnfContext::default(),
                NatReductionBudget::unlimited(),
                || {
                    seen += 1;
                    seen == stop_at
                },
            );
            assert!(
                matches!(result, NatReductionOutcome::Inconclusive(_)),
                "poll {stop_at}: {result:?}"
            );
        }
        let result = value(reduce_nat(
            &term,
            &zero,
            &WhnfContext::default(),
            NatReductionBudget::unlimited(),
        ));
        assert_eq!(result.term.node(result.term.root()), Some(&nat(256)));
    }

    #[test]
    fn exact_resources_succeed_and_one_less_remains_inconclusive() {
        let term = doubling(8);
        let zero = literal(0);
        let result = value(reduce_nat(
            &term,
            &zero,
            &WhnfContext::default(),
            NatReductionBudget::unlimited(),
        ));
        let p = result.progress;
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
        value(reduce_nat(&term, &zero, &WhnfContext::default(), exact));
        for dimension in 0..8 {
            let mut smaller = exact;
            let limit = match dimension {
                0 => &mut smaller.max_steps,
                1 => &mut smaller.max_work_items,
                2 => &mut smaller.max_generated_arenas,
                3 => &mut smaller.max_materialized_arena_nodes,
                4 => &mut smaller.max_materialized_owned_units,
                5 => &mut smaller.max_output_units,
                6 => &mut smaller.numeric.max_steps,
                _ => &mut smaller.numeric.max_materialized_limbs,
            };
            assert!(*limit > 0);
            *limit -= 1;
            let outcome = reduce_nat(&term, &zero, &WhnfContext::default(), smaller);
            assert!(
                matches!(outcome, NatReductionOutcome::Inconclusive(_)),
                "dimension={dimension}: {outcome:?}"
            );
        }
    }

    #[test]
    fn memo_results_never_cross_contexts_queries_or_scope_policies() {
        let name = WireName::from_parts(vec![NamePart::Text("x".into())]);
        let mut nodes = vec![op("add"), ExprNode::Free { name: name.clone() }];
        let partial = app(&mut nodes, id(0), id(1));
        let shared = app(&mut nodes, partial, id(1));
        let partial = app(&mut nodes, id(0), shared);
        let root = app(&mut nodes, partial, shared);
        let term = WireExpr::from_parts(nodes, vec![], root);
        let zero = literal(0);
        for n in [7, 11, 7] {
            let context = WhnfContext::new(
                vec![crate::whnf::FreeBinding::new(name.clone(), literal(n))],
                vec![],
                Default::default(),
            );
            let result = value(reduce_nat_at_with(
                NatReductionQuery::new(&term, root, &zero, zero.root(), &context),
                NatReductionBudget::unlimited(),
                NatReductionScope::WhnfHead,
                &mut || false,
            ));
            assert_eq!(result.term.node(result.term.root()), Some(&nat(4 * n)));
            assert!(matches!(
                reduce_nat(&term, &zero, &context, NatReductionBudget::unlimited()),
                NatReductionOutcome::NotReduced {
                    reason: NatNotReduced::OpenPair { .. },
                    ..
                }
            ));
        }
        let invalid = WhnfContext::new(
            vec![
                crate::whnf::FreeBinding::new(name.clone(), literal(1)),
                crate::whnf::FreeBinding::new(name, literal(2)),
            ],
            vec![],
            Default::default(),
        );
        assert!(matches!(
            reduce_nat(
                &doubling(8),
                &zero,
                &invalid,
                NatReductionBudget::unlimited()
            ),
            NatReductionOutcome::Refused { .. }
        ));
    }

    #[test]
    fn boolean_operands_and_capped_powers_do_not_gain_natural_results() {
        let mut nodes = vec![op("beq"), nat(3), op("add")];
        let partial = app(&mut nodes, id(0), id(1));
        let boolean = app(&mut nodes, partial, id(1));
        let partial = app(&mut nodes, id(2), boolean);
        let root = app(&mut nodes, partial, boolean);
        let term = WireExpr::from_parts(nodes, vec![], root);
        assert!(matches!(
            reduce_nat(
                &term,
                &literal(0),
                &WhnfContext::default(),
                NatReductionBudget::unlimited()
            ),
            NatReductionOutcome::NotReduced {
                reason: NatNotReduced::OperandNotNatural { .. },
                ..
            }
        ));
        let mut nodes = vec![
            op("pow"),
            nat(2),
            nat(crate::numeric::REDUCE_POW_MAX_EXP + 1),
            op("add"),
        ];
        let partial = app(&mut nodes, id(0), id(1));
        let power = app(&mut nodes, partial, id(2));
        let partial = app(&mut nodes, id(3), power);
        let root = app(&mut nodes, partial, power);
        let term = WireExpr::from_parts(nodes, vec![], root);
        assert!(matches!(
            reduce_nat(
                &term,
                &literal(0),
                &WhnfContext::default(),
                NatReductionBudget::unlimited()
            ),
            NatReductionOutcome::NotReduced {
                reason: NatNotReduced::PowExponentAbovePinCap { .. },
                ..
            }
        ));
    }

    #[test]
    fn distinct_arena_namespaces_cannot_alias_the_same_numeric_node() {
        use super::NaturalMemo;
        let candidate = Cursor {
            source: ArenaSource::Candidate,
            root: id(3),
        };
        let generated = Cursor {
            source: ArenaSource::Generated(0),
            root: id(3),
        };
        let mut memo = NaturalMemo::default();
        let mut never = || false;
        let mut control = Control::new(NatReductionBudget::unlimited(), &mut never);
        let first = Arc::new(NatValue::from_u64(7));
        let second = Arc::new(NatValue::from_u64(19));
        memo.remember(candidate, &first, &mut control)
            .unwrap_or_else(|_| panic!("unexpected memo stop"));
        memo.remember(generated, &second, &mut control)
            .unwrap_or_else(|_| panic!("unexpected memo stop"));
        assert!(Arc::ptr_eq(
            &memo
                .recall(candidate, &mut control)
                .unwrap_or_else(|_| panic!("unexpected memo stop"))
                .unwrap(),
            &first
        ));
        assert!(Arc::ptr_eq(
            &memo
                .recall(generated, &mut control)
                .unwrap_or_else(|_| panic!("unexpected memo stop"))
                .unwrap(),
            &second
        ));
        assert!(
            memo.recall(
                Cursor {
                    source: ArenaSource::Generated(1),
                    root: id(3)
                },
                &mut control
            )
            .unwrap_or_else(|_| panic!("unexpected memo stop"))
            .is_none()
        );
    }

    #[test]
    fn retention_capacity_declines_new_entries_without_losing_old_results() {
        use super::{MAX_ENTRIES, MAX_RETAINED_LIMBS, NaturalMemo};
        let mut memo = NaturalMemo::default();
        let mut never = || false;
        let mut control = Control::new(NatReductionBudget::unlimited(), &mut never);
        let value = Arc::new(NatValue::one());
        for n in 0..=MAX_ENTRIES {
            memo.remember(
                Cursor {
                    source: ArenaSource::Candidate,
                    root: id(n),
                },
                &value,
                &mut control,
            )
            .unwrap_or_else(|_| panic!("unexpected memo stop"));
        }
        assert_eq!(memo.entries.len(), MAX_ENTRIES);
        assert!(
            memo.recall(
                Cursor {
                    source: ArenaSource::Candidate,
                    root: id(MAX_ENTRIES)
                },
                &mut control
            )
            .unwrap_or_else(|_| panic!("unexpected memo stop"))
            .is_none()
        );
        assert!(
            memo.recall(
                Cursor {
                    source: ArenaSource::Candidate,
                    root: id(0)
                },
                &mut control
            )
            .unwrap_or_else(|_| panic!("unexpected memo stop"))
            .is_some()
        );
        let mut memo = NaturalMemo::default();
        let large = Arc::new(NatValue::from_limbs_le(vec![1; MAX_RETAINED_LIMBS]).unwrap());
        let cursor = Cursor {
            source: ArenaSource::Candidate,
            root: id(0),
        };
        memo.remember(cursor, &large, &mut control)
            .unwrap_or_else(|_| panic!("unexpected memo stop"));
        memo.remember(
            Cursor {
                root: id(1),
                ..cursor
            },
            &value,
            &mut control,
        )
        .unwrap_or_else(|_| panic!("unexpected memo stop"));
        assert_eq!(memo.entries.len(), 1);
        assert_eq!(memo.limbs, MAX_RETAINED_LIMBS);
        memo.remember(cursor, &value, &mut control)
            .unwrap_or_else(|_| panic!("unexpected memo stop"));
        assert!(Arc::ptr_eq(
            &memo
                .recall(cursor, &mut control)
                .unwrap_or_else(|_| panic!("unexpected memo stop"))
                .unwrap(),
            &large
        ));
    }

    #[test]
    fn a_deep_chain_survives_memo_saturation_on_a_small_host_stack() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut nodes = vec![op("succ"), nat(0)];
                let mut root = id(1);
                for _ in 0..4_200 {
                    root = app(&mut nodes, id(0), root);
                }
                let term = WireExpr::from_parts(nodes, vec![], root);
                let result = value(reduce_nat(
                    &term,
                    &literal(0),
                    &WhnfContext::default(),
                    NatReductionBudget::unlimited(),
                ));
                assert_eq!(result.term.node(result.term.root()), Some(&nat(4_200)));
            })
            .unwrap()
            .join()
            .unwrap();
    }
    fn wrapped_doubling(depth: usize, kind: u8) -> WireExpr {
        use crate::wire::BinderStyle;
        let nat_name = WireName::from_parts(vec![NamePart::Text("Nat".into())]);
        let mut nodes = vec![
            op("add"),
            nat(1),
            ExprNode::Constant {
                name: nat_name,
                levels: vec![],
            },
            ExprNode::Bound { index: 0 },
        ];
        let identity = push(
            &mut nodes,
            ExprNode::Lambda {
                binder_name: WireName::default(),
                binder_type: id(2),
                body: id(3),
                style: BinderStyle::Default,
            },
        );
        let mut root = id(1);
        for n in 0..depth {
            let partial = app(&mut nodes, id(0), root);
            root = app(&mut nodes, partial, root);
            if n + 1 != depth {
                root = match kind {
                    0 => push(
                        &mut nodes,
                        ExprNode::Metadata {
                            entries: vec![],
                            expression: root,
                        },
                    ),
                    1 => app(&mut nodes, identity, root),
                    _ => push(
                        &mut nodes,
                        ExprNode::Let {
                            declaration_name: WireName::default(),
                            type_: id(2),
                            value: root,
                            body: id(3),
                            non_dependent: false,
                        },
                    ),
                };
            }
        }
        WireExpr::from_parts(nodes, vec![], root)
    }
    #[test]
    fn normalized_shared_operands_retain_their_original_demand_identity() {
        for kind in 0..3 {
            let term = wrapped_doubling(24, kind);
            let mut budget = NatReductionBudget::unlimited();
            budget.max_steps = 10_000;
            let result = value(reduce_nat(
                &term,
                &literal(0),
                &WhnfContext::default(),
                budget,
            ));
            assert_eq!(result.term.node(result.term.root()), Some(&nat(1 << 24)));
            assert_eq!(
                result.progress.numeric_reductions, 24,
                "wrapper kind {kind}"
            );
        }
    }

    #[test]
    fn normalized_demand_reuse_observes_every_cancellation_checkpoint() {
        use std::cell::Cell;
        for kind in 0..3 {
            let term = wrapped_doubling(5, kind);
            let other = literal(0);
            let polls = Cell::new(0);
            value(reduce_nat_with(
                &term,
                &other,
                &WhnfContext::default(),
                NatReductionBudget::unlimited(),
                || {
                    polls.set(polls.get() + 1);
                    false
                },
            ));
            for stop_at in 1..=polls.get() {
                let mut called = 0;
                let stopped = reduce_nat_with(
                    &term,
                    &other,
                    &WhnfContext::default(),
                    NatReductionBudget::unlimited(),
                    || {
                        called += 1;
                        called == stop_at
                    },
                );
                assert!(
                    matches!(stopped, NatReductionOutcome::Inconclusive(_)),
                    "wrapper {kind}, checkpoint {stop_at}: {stopped:?}"
                );
            }
            let result = value(reduce_nat(
                &term,
                &other,
                &WhnfContext::default(),
                NatReductionBudget::unlimited(),
            ));
            assert_eq!(result.term.node(result.term.root()), Some(&nat(32)));
        }
    }
}
