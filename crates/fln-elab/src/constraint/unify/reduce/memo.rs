//! Completed demand results belong only to one `whnf` call. In particular, no
//! entry can cross an assignment generation, local context or delta policy.
//! Keep source allocations alive so their identities cannot be recycled.
//! A bounded structural index also recognizes equal demands rebuilt by beta
//! substitution. Hashes only select candidates; metered comparison proves hits.
use super::*;

const MAX_ENTRIES: usize = 4_096;
const MAX_ARGUMENTS: usize = 16_384;
const MAX_BUCKET_ENTRIES: usize = 8;

#[derive(Default)]
pub(super) struct DemandMemo {
    entries: HashMap<usize, (Expr, Expr, Vec<Expr>)>,
    buckets: HashMap<u64, Vec<usize>>,
    arguments: usize,
}

// This is exact syntax equality, not the unifier's alpha/metadata-insensitive
// reflexivity test. Reusing a result must also preserve names, binder styles,
// let flags and annotations that later elaboration can retain in its output.
fn same_demand(left: &Expr, right: &Expr, meter: &mut Meter<'_>) -> Result<bool, UnificationError> {
    let mut pending = vec![(left, right)];
    let mut seen = HashSet::new();
    while let Some((left, right)) = pending.pop() {
        meter.node()?;
        if left.data() != right.data() {
            return Ok(false);
        }
        if left.allocation_identity() == right.allocation_identity() {
            continue;
        }
        if !seen.insert((left.allocation_identity(), right.allocation_identity())) {
            continue;
        }
        match (left.node(), right.node()) {
            (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
            (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) if a == b => {}
            (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) if a == b => {}
            (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => {
                if !same_levels(a, b, meter)? {
                    return Ok(false);
                }
            }
            (
                ExprNode::Const {
                    name: a,
                    levels: al,
                },
                ExprNode::Const {
                    name: b,
                    levels: bl,
                },
            ) if a == b && al.len() == bl.len() => {
                for (a, b) in al.iter().zip(bl) {
                    if !same_levels(a, b, meter)? {
                        return Ok(false);
                    }
                }
            }
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                pending.push((aa, ba));
                pending.push((af, bf));
            }
            (
                ExprNode::Lam {
                    binder_name: an,
                    binder_type: at,
                    body: ab,
                    binder_info: ai,
                },
                ExprNode::Lam {
                    binder_name: bn,
                    binder_type: bt,
                    body: bb,
                    binder_info: bi,
                },
            )
            | (
                ExprNode::ForallE {
                    binder_name: an,
                    binder_type: at,
                    body: ab,
                    binder_info: ai,
                },
                ExprNode::ForallE {
                    binder_name: bn,
                    binder_type: bt,
                    body: bb,
                    binder_info: bi,
                },
            ) if an == bn && ai == bi => {
                pending.push((ab, bb));
                pending.push((at, bt));
            }
            (
                ExprNode::LetE {
                    decl_name: an,
                    type_: at,
                    value: av,
                    body: ab,
                    non_dep: ad,
                },
                ExprNode::LetE {
                    decl_name: bn,
                    type_: bt,
                    value: bv,
                    body: bb,
                    non_dep: bd,
                },
            ) if an == bn && ad == bd => {
                pending.push((ab, bb));
                pending.push((av, bv));
                pending.push((at, bt));
            }
            (
                ExprNode::Lit {
                    literal: Literal::Nat(a),
                },
                ExprNode::Lit {
                    literal: Literal::Nat(b),
                },
            ) => {
                if a.limbs_le().len() != b.limbs_le().len() {
                    return Ok(false);
                }
                for (a, b) in a.limbs_le().iter().zip(b.limbs_le()) {
                    meter.node()?;
                    if a != b {
                        return Ok(false);
                    }
                }
            }
            (
                ExprNode::Lit {
                    literal: Literal::Str(a),
                },
                ExprNode::Lit {
                    literal: Literal::Str(b),
                },
            ) => {
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.bytes().zip(b.bytes()) {
                    meter.node()?;
                    if a != b {
                        return Ok(false);
                    }
                }
            }
            (ExprNode::MData { data: a, expr: av }, ExprNode::MData { data: b, expr: bv }) => {
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.entries().iter().zip(b.entries()) {
                    meter.node()?;
                    if a != b {
                        return Ok(false);
                    }
                }
                pending.push((av, bv));
            }
            (
                ExprNode::Proj {
                    struct_name: an,
                    idx: ai,
                    expr: av,
                },
                ExprNode::Proj {
                    struct_name: bn,
                    idx: bi,
                    expr: bv,
                },
            ) if an == bn && ai == bi => {
                pending.push((av, bv));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

impl DemandMemo {
    fn find(
        &self,
        subject: &Expr,
        meter: &mut Meter<'_>,
    ) -> Result<Option<(Expr, Vec<Expr>)>, UnificationError> {
        meter.tick()?;
        let mut found = self.entries.get(&subject.allocation_identity());
        if found.is_none()
            && let Some(candidates) = self.buckets.get(&subject.hash())
        {
            for key in candidates {
                meter.tick()?;
                let entry = &self.entries[key];
                if same_demand(subject, &entry.0, meter)? {
                    found = Some(entry);
                    break;
                }
            }
        }
        let Some((_, head, args)) = found else {
            return Ok(None);
        };
        // Reusing a result still pays for retaining its spine and observes
        // cancellation before proportional allocation. Literal payloads and
        // term nodes are immutable shared Expr allocations, not deep clones.
        meter.node()?;
        for _ in args {
            meter.node()?;
        }
        Ok(Some((head.clone(), args.clone())))
    }

    pub(super) fn remember(
        &mut self,
        subject: Expr,
        head: &Expr,
        args: &[Expr],
        meter: &mut Meter<'_>,
    ) -> Result<(), UnificationError> {
        meter.tick()?;
        let key = subject.allocation_identity();
        if self.entries.contains_key(&key)
            || self.entries.len() >= MAX_ENTRIES
            || args.len() > MAX_ARGUMENTS.saturating_sub(self.arguments)
        {
            // A full cache is not a semantic refusal. The same metered
            // evaluator remains available without remembering another result.
            return Ok(());
        }
        let hash = subject.hash();
        let index = self.buckets.get(&hash).map_or(0, Vec::len) < MAX_BUCKET_ENTRIES;
        meter.node()?;
        for _ in args {
            meter.node()?;
        }
        if index {
            // Charge both indexes before publishing either of them. Colliding
            // buckets saturate without replacing an earlier result; pointer
            // reuse remains available for entries outside the structural cap.
            meter.node()?;
        }
        self.arguments += args.len();
        self.entries
            .insert(key, (subject, head.clone(), args.to_vec()));
        if index {
            self.buckets.entry(hash).or_default().push(key);
        }
        Ok(())
    }
}

impl Engine<'_> {
    /// Begin an operand/major demand after its semantic continuation is pushed.
    /// Only these nested demands use eager delta; putting a Remember frame at
    /// the root would incorrectly enable delta in lazy outer comparisons.
    pub(super) fn demand(
        &mut self,
        subject: Expr,
        memo: &mut DemandMemo,
        continuations: &mut Vec<Continuation>,
    ) -> Result<(Expr, Vec<Expr>, bool), UnificationError> {
        if let Some((head, args)) = memo.find(&subject, &mut self.meter)? {
            return Ok((head, args, true));
        }
        continuations.push(Continuation::Remember {
            subject: subject.clone(),
        });
        Ok((subject, Vec::new(), false))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::BinderInfo;
    use std::cell::Cell;

    fn number(n: u64) -> Expr {
        Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(n)))
    }
    fn meter(cancelled: &dyn Fn() -> bool) -> Meter<'_> {
        Meter {
            steps: 0,
            nodes: 0,
            max_steps: u64::MAX,
            max_nodes: usize::MAX,
            heartbeat_bound: false,
            cancelled,
        }
    }

    #[test]
    fn memo_capacity_falls_back_without_replacing_an_existing_result() {
        let mut cache = DemandMemo::default();
        let mut meter = meter(&|| false);
        let inputs: Vec<_> = (0..=MAX_ENTRIES).map(|n| number(n as u64)).collect();
        for input in &inputs {
            cache
                .remember(input.clone(), input, &[], &mut meter)
                .unwrap();
        }
        assert_eq!(cache.entries.len(), MAX_ENTRIES);
        assert!(
            cache
                .find(&inputs[MAX_ENTRIES], &mut meter)
                .unwrap()
                .is_none()
        );
        cache
            .remember(inputs[0].clone(), &number(99), &[], &mut meter)
            .unwrap();
        let (value, args) = cache.find(&inputs[0], &mut meter).unwrap().unwrap();
        assert_eq!(value, inputs[0]);
        assert!(args.is_empty());
    }

    #[test]
    fn retained_spines_have_an_exact_aggregate_cap_and_preserve_order() {
        let mut cache = DemandMemo::default();
        let mut meter = meter(&|| false);
        let input = number(9);
        let second = number(10); // a distinct demand still obeys the aggregate cap
        let args: Vec<_> = (0..MAX_ARGUMENTS).map(|n| number(n as u64)).collect();
        cache
            .remember(input.clone(), &number(0), &args, &mut meter)
            .unwrap();
        assert_eq!(cache.arguments, MAX_ARGUMENTS);
        let (head, found) = cache.find(&input, &mut meter).unwrap().unwrap();
        assert_eq!(head, number(0));
        assert_eq!(found, args);
        assert!(cache.find(&second, &mut meter).unwrap().is_none());
        cache
            .remember(second.clone(), &number(1), &[number(2)], &mut meter)
            .unwrap();
        assert!(cache.find(&second, &mut meter).unwrap().is_none());
        cache
            .remember(second.clone(), &number(1), &[], &mut meter)
            .unwrap();
        assert!(cache.find(&second, &mut meter).unwrap().is_some());
        assert_eq!(cache.arguments, MAX_ARGUMENTS);
    }

    #[test]
    fn cancellation_and_node_stops_cannot_publish_a_partial_cache_entry() {
        let calls = Cell::new(0);
        let cancelled = || {
            calls.set(calls.get() + 1);
            calls.get() == 4
        };
        let mut cache = DemandMemo::default();
        let mut cancelled_meter = meter(&cancelled);
        let input = number(7);
        assert!(matches!(
            cache.remember(
                input.clone(),
                &number(0),
                &[number(1), number(2)],
                &mut cancelled_meter
            ),
            Err(UnificationError::Cancelled)
        ));
        assert!(cache.entries.is_empty());
        assert_eq!(cache.arguments, 0);
        let mut limited = meter(&|| false);
        limited.max_nodes = 2;
        assert!(matches!(
            cache.remember(
                input.clone(),
                &number(0),
                &[number(1), number(2)],
                &mut limited
            ),
            Err(UnificationError::NodeLimit { .. })
        ));
        assert!(cache.entries.is_empty());
        assert_eq!(cache.arguments, 0);
        cache
            .remember(
                input.clone(),
                &number(0),
                &[number(1), number(2)],
                &mut meter(&|| false),
            )
            .unwrap();
        let mut limited = meter(&|| false);
        limited.max_nodes = 2;
        assert!(matches!(
            cache.find(&input, &mut limited),
            Err(UnificationError::NodeLimit { .. })
        ));
        assert_eq!(cache.entries.len(), 1);
    }

    #[test]
    fn rebuilt_equal_demands_reuse_the_completed_spine() {
        let make = || {
            Expr::app(
                Expr::const_(Name::from_components(["operation"]), vec![]),
                number(7),
            )
        };
        let input = make();
        let rebuilt = make();
        assert_ne!(input.allocation_identity(), rebuilt.allocation_identity());
        let mut cache = DemandMemo::default();
        let mut meter = meter(&|| false);
        cache
            .remember(input, &number(42), &[number(3), number(5)], &mut meter)
            .unwrap();
        let (result, args) = cache.find(&rebuilt, &mut meter).unwrap().unwrap();
        assert_eq!(result, number(42));
        assert_eq!(args, [number(3), number(5)]);
        assert_eq!(cache.entries.len(), 1);
        assert_eq!(cache.arguments, 2);
        assert!(
            DemandMemo::default()
                .find(&rebuilt, &mut meter)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn colliding_demands_are_compared_and_saturated_buckets_keep_pointer_fallback() {
        let make = |i| {
            Expr::const_(
                Name::num_overflowing(Name::from_components(["collision"]), i),
                vec![],
            )
        };
        let inputs: Vec<_> = (0..MAX_BUCKET_ENTRIES + 3)
            .map(|i| make(i as u64))
            .collect();
        let mut cache = DemandMemo::default();
        let mut meter = meter(&|| false);
        for (i, input) in inputs.iter().enumerate() {
            assert_eq!(input.hash(), inputs[0].hash(), "the collision must be real");
            cache
                .remember(input.clone(), &number(i as u64), &[], &mut meter)
                .unwrap();
        }
        assert_eq!(cache.buckets.len(), 1);
        assert_eq!(cache.buckets[&inputs[0].hash()].len(), MAX_BUCKET_ENTRIES);
        for (i, input) in inputs.iter().enumerate() {
            let result = cache.find(input, &mut meter).unwrap().unwrap();
            assert_eq!(result.0, number(i as u64));
            let rebuilt = make(i as u64);
            let found = cache.find(&rebuilt, &mut meter).unwrap();
            if i < MAX_BUCKET_ENTRIES {
                assert_eq!(found.unwrap().0, number(i as u64));
            } else {
                assert!(
                    found.is_none(),
                    "full structural bucket falls back to evaluation"
                );
            }
        }
        assert!(cache.find(&make(99), &mut meter).unwrap().is_none());
    }

    #[test]
    fn structural_hits_are_metered_cancellable_and_do_not_mutate_the_cache() {
        let make = || {
            (0..24).fold(number(7), |inner, _| {
                Expr::app(Expr::const_(Name::from_components(["f"]), vec![]), inner)
            })
        };
        let input = make();
        let rebuilt = make();
        let mut cache = DemandMemo::default();
        cache
            .remember(input, &number(42), &[], &mut meter(&|| false))
            .unwrap();
        let mut complete = meter(&|| false);
        assert_eq!(
            cache.find(&rebuilt, &mut complete).unwrap().unwrap().0,
            number(42)
        );
        assert!(complete.nodes > 24);
        for allowance in [0, complete.nodes / 2, complete.nodes - 1] {
            let mut limited = meter(&|| false);
            limited.max_nodes = allowance;
            assert!(matches!(
                cache.find(&rebuilt, &mut limited),
                Err(UnificationError::NodeLimit { .. })
            ));
            assert_eq!(cache.entries.len(), 1);
            assert_eq!(cache.buckets.len(), 1);
        }
        let calls = Cell::new(0);
        let cancelled = || {
            calls.set(calls.get() + 1);
            calls.get() == 10
        };
        assert!(matches!(
            cache.find(&rebuilt, &mut meter(&cancelled)),
            Err(UnificationError::Cancelled)
        ));
        let mut retry = meter(&|| false);
        assert_eq!(
            cache.find(&rebuilt, &mut retry).unwrap().unwrap().0,
            number(42)
        );
        assert_eq!(retry.nodes, complete.nodes);
        assert_eq!(retry.steps, complete.steps);
    }

    #[test]
    fn the_last_index_charge_cannot_publish_half_an_entry() {
        let mut cache = DemandMemo::default();
        let input = number(7);
        let mut limited = meter(&|| false);
        limited.max_nodes = 3;
        assert!(matches!(
            cache.remember(
                input.clone(),
                &number(0),
                &[number(1), number(2)],
                &mut limited
            ),
            Err(UnificationError::NodeLimit { .. })
        ));
        assert!(cache.entries.is_empty());
        assert!(cache.buckets.is_empty());
        assert_eq!(cache.arguments, 0);
        cache
            .remember(
                input,
                &number(0),
                &[number(1), number(2)],
                &mut meter(&|| false),
            )
            .unwrap();
        assert_eq!(cache.entries.len(), 1);
        assert_eq!(cache.buckets.len(), 1);
        assert_eq!(cache.arguments, 2);
    }

    #[test]
    fn result_reuse_preserves_binder_names_styles_let_flags_and_metadata() {
        use fln_core::options::{DataValue, KVMap};
        let name = |s| Name::from_components([s]);
        let domain = Expr::sort(Level::one());
        let body = Expr::bvar(0).unwrap();
        let left = Expr::lam(
            name("first"),
            domain.clone(),
            body.clone(),
            BinderInfo::Default,
        );
        let renamed = Expr::lam(
            name("second"),
            domain.clone(),
            body.clone(),
            BinderInfo::Default,
        );
        let implicit = Expr::lam(
            name("first"),
            domain.clone(),
            body.clone(),
            BinderInfo::Implicit,
        );
        let let_a = Expr::let_e(name("x"), domain.clone(), number(1), body.clone(), false);
        let let_b = Expr::let_e(name("x"), domain, number(1), body, true);
        let meta_a = Expr::mdata(
            KVMap::from_entries(vec![(name("note"), DataValue::OfNat(1))]),
            number(7),
        );
        let meta_b = Expr::mdata(
            KVMap::from_entries(vec![(name("note"), DataValue::OfNat(2))]),
            number(7),
        );
        for (a, b) in [
            (&left, &renamed),
            (&left, &implicit),
            (&let_a, &let_b),
            (&meta_a, &meta_b),
        ] {
            assert!(
                same_terms(a, b, &mut meter(&|| false)).unwrap(),
                "definitional reflexivity is weaker"
            );
            assert_ne!(a, b);
            assert!(!same_demand(a, b, &mut meter(&|| false)).unwrap());
            let mut cache = DemandMemo::default();
            cache
                .remember(a.clone(), &number(42), &[], &mut meter(&|| false))
                .unwrap();
            assert!(cache.find(b, &mut meter(&|| false)).unwrap().is_none());
        }
    }

    #[test]
    fn exact_demand_comparison_is_bounded_on_independently_rebuilt_dags() {
        let build = || (0..24).fold(number(1), |value, _| Expr::app(value.clone(), value));
        let left = build();
        let right = build();
        let mut complete = meter(&|| false);
        assert!(same_demand(&left, &right, &mut complete).unwrap());
        assert!(
            complete.nodes < 100,
            "shared syntax must not expand to a tree"
        );
        let mut limited = meter(&|| false);
        limited.max_nodes = complete.nodes - 1;
        assert!(matches!(
            same_demand(&left, &right, &mut limited),
            Err(UnificationError::NodeLimit { .. })
        ));
        let unequal = Expr::proj(Name::from_components(["family"]), 1, right.clone());
        assert_eq!(
            same_demand(&left, &unequal, &mut meter(&|| false)).unwrap(),
            left == unequal
        );
        for value in [
            Expr::sort(Level::one()),
            Expr::const_(Name::from_components(["f"]), vec![Level::one()]),
            Expr::lit(Literal::Str("λ界".into())),
            Expr::proj(Name::from_components(["family"]), 0, right),
        ] {
            assert!(same_demand(&value, &value.clone(), &mut meter(&|| false)).unwrap());
        }
    }
}
