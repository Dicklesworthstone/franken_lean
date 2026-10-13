//! Completed demand results belong only to one `whnf` call. In particular, no
//! entry can cross an assignment generation, local context or delta policy.
//! Keep source allocations alive so their identities cannot be recycled.
use super::*;

const MAX_ENTRIES: usize = 4_096;
const MAX_ARGUMENTS: usize = 16_384;

#[derive(Default)]
pub(super) struct DemandMemo {
    entries: HashMap<usize, (Expr, Expr, Vec<Expr>)>,
    arguments: usize,
}

impl DemandMemo {
    fn find(
        &self,
        subject: &Expr,
        meter: &mut Meter<'_>,
    ) -> Result<Option<(Expr, Vec<Expr>)>, UnificationError> {
        meter.tick()?;
        let Some((_, head, args)) = self.entries.get(&subject.allocation_identity()) else {
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
        meter.node()?;
        for _ in args {
            meter.node()?;
        }
        self.arguments += args.len();
        self.entries
            .insert(key, (subject, head.clone(), args.to_vec()));
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
        let second = number(9); // equal structure, distinct allocation: not a hit
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
}
