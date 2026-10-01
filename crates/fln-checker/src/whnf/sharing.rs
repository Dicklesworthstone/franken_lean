//! Exact output-node sharing during checker-owned materialization.
//!
//! A reduced function and its pending arguments may come from different flat
//! arenas even when they contain the same subterms. Source-pointer memoization
//! alone then duplicates their common DAG on every application rebuild. After
//! mapping child IDs into the output arena, shallow node equality is enough to
//! recover that sharing. No recursive comparison or semantic conversion occurs.
//! Only copies from different input arenas are merged: one input's occurrence
//! shape and newly built application nodes retain their original behavior.
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};

// Retention is optional: a full table or bucket declines new entries, never
// changes a term's meaning or raises a semantic checking limit. The table owns
// only output indices, not a second copy of names, metadata or literal payloads.
const MAX_ENTRIES: usize = 1 << 20;
const MAX_BUCKET: usize = 8;

#[derive(Default)]
pub(super) struct Interned {
    buckets: BTreeMap<u64, Vec<(usize, usize)>>,
    entries: usize,
}

/// Candidates are compared exactly, so the hash needs only speed and a fixed
/// key: `std`'s SipHash here was 6.5 % of a heavy K-cast proof's check
/// (Std.Tactic.BVDecide ... Circuit.Lemmas, `go_Inv_of_Inv`).
pub(super) fn fingerprint(node: &impl Hash) -> u64 {
    let mut hasher = super::memo::Fingerprinter::default();
    node.hash(&mut hasher);
    hasher.finish()
}

impl Interned {
    /// Hashes select candidates only. Compare all shallow payloads and mapped
    /// children exactly. The caller has already charged the node's owned units;
    /// the fixed bucket cap bounds hashing/comparison work per charged payload.
    /// A tree over the hashes also avoids adversarial hash-table probe chains.
    pub(super) fn find<T: Eq>(
        &self,
        hash: u64,
        node: &T,
        arena: &[T],
        source: usize,
    ) -> Option<usize> {
        self.buckets
            .get(&hash)?
            .iter()
            .filter_map(|&(index, origin)| (origin != source).then_some(index))
            .find(|&index| arena.get(index) == Some(node))
    }

    /// Called only for a freshly appended, already budget-admitted output node.
    pub(super) fn record(&mut self, hash: u64, index: usize, source: usize) {
        if self.entries >= MAX_ENTRIES {
            return;
        }
        let bucket = self.buckets.entry(hash).or_default();
        if bucket.len() < MAX_BUCKET {
            bucket.push((index, source));
            self.entries += 1;
        }
    }
}

#[cfg(test)]
mod tests;
