//! Answers to the regular same-head argument comparisons of one conversion.
//!
//! Lazy delta tries the same-head shortcut at every unfolding step, and a chain
//! such as `List.merge` -> `List.merge._unary` -> `WellFounded.fix` puts the same
//! argument pair to it at each step. The nested comparisons then ask the same
//! small questions again inside every attempt. The pin keeps `failed_before` and
//! its equivalence manager for the life of the type checker for this reason.
//! This memo does the same for one top-level conversion.
//!
//! A remembered answer is the answer a recomputation would give:
//! - every comparison of one conversion runs under the same `WhnfContext`;
//! - an entry matches only an exactly equal pair of materialized terms, under the
//!   same Nat scope;
//! - "not proven" only declines the shortcut, so lazy delta goes on unfolding as it
//!   would have;
//! - "equal" is recorded only when the comparison proved it;
//! - a stop is never recorded.
use super::*;
use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Remembered {
    Equal,
    NotProven,
}

struct Entry {
    left: WireExpr,
    right: WireExpr,
    nat_scope: NatReductionScope,
    answer: Remembered,
}

/// Past either bound the memo stops growing; lookups continue. Both keep the
/// memo's memory proportional to what one conversion already materialized.
const MAX_ENTRIES: usize = 1 << 16;
const MAX_STORED_NODES: usize = 1 << 20;

#[derive(Default)]
pub(super) struct ArgumentMemo {
    /// Keyed by a fixed-key fingerprint, so the order of answers never depends on
    /// the process; entries in a bucket are compared exactly.
    buckets: HashMap<u64, Vec<Entry>>,
    entries: usize,
    stored_nodes: usize,
}

fn fingerprint(left: &WireExpr, right: &WireExpr, nat_scope: NatReductionScope) -> u64 {
    let mut hasher = DefaultHasher::new();
    left.hash(&mut hasher);
    right.hash(&mut hasher);
    nat_scope.hash(&mut hasher);
    hasher.finish()
}

impl ArgumentMemo {
    pub(super) fn recall(
        &self,
        left: &WireExpr,
        right: &WireExpr,
        nat_scope: NatReductionScope,
    ) -> Option<Remembered> {
        self.buckets
            .get(&fingerprint(left, right, nat_scope))?
            .iter()
            .find(|entry| {
                entry.nat_scope == nat_scope && entry.left == *left && entry.right == *right
            })
            .map(|entry| entry.answer)
    }

    pub(super) fn remember(
        &mut self,
        left: WireExpr,
        right: WireExpr,
        nat_scope: NatReductionScope,
        answer: Remembered,
    ) {
        let nodes = left.nodes().len().saturating_add(right.nodes().len());
        if self.entries >= MAX_ENTRIES
            || self.stored_nodes.saturating_add(nodes) > MAX_STORED_NODES
            || self.recall(&left, &right, nat_scope).is_some()
        {
            return;
        }
        self.buckets
            .entry(fingerprint(&left, &right, nat_scope))
            .or_default()
            .push(Entry {
                left,
                right,
                nat_scope,
                answer,
            });
        self.entries += 1;
        self.stored_nodes += nodes;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::ExprId;

    fn nat(value: u64) -> WireExpr {
        let root = ExprId::from_index(0).expect("zero expression index");
        WireExpr::from_parts(
            vec![ExprNode::NatLiteral {
                limbs_le: vec![value],
            }],
            Vec::new(),
            root,
        )
    }

    #[test]
    fn a_remembered_answer_belongs_to_exactly_its_pair_and_scope() {
        let closed = NatReductionScope::ClosedPair;
        let mut memo = ArgumentMemo::default();
        let (one, two) = (nat(1), nat(2));
        assert_eq!(memo.recall(&one, &two, closed), None);

        memo.remember(one.clone(), two.clone(), closed, Remembered::NotProven);
        assert_eq!(memo.recall(&one, &two, closed), Some(Remembered::NotProven));
        assert_eq!(
            memo.recall(&two, &one, closed),
            None,
            "order is part of the pair"
        );
        assert_eq!(memo.recall(&one, &one, closed), None);
        assert_eq!(
            memo.recall(&one, &two, NatReductionScope::EagerOpenPair),
            None,
            "the Nat scope is part of the pair"
        );

        memo.remember(one.clone(), one.clone(), closed, Remembered::Equal);
        assert_eq!(memo.recall(&one, &one, closed), Some(Remembered::Equal));
        assert_eq!(
            memo.recall(&one, &two, closed),
            Some(Remembered::NotProven),
            "a second pair leaves the first pair's answer alone"
        );
    }
}
