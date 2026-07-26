//! The environment-extension registry (plan §7.1): every extension declares its
//! merge and checkpoint semantics **in a registry**, so branching and merging an
//! environment includes its extensions *by contract*, not by each author's memory.
//!
//! The honesty laws, structural here:
//! * an extension payload understood only as opaque bytes is preserved losslessly,
//!   is **flagged in provenance** ([`ExtensionState::provenance`] reports
//!   [`PayloadProvenance::Opaque`]), and **honestly blocks fine-grained
//!   invalidation** through it ([`ExtensionState::supports_fine_invalidation`] is
//!   `false`) — never guessed safe;
//! * import-time replay preserves the Reference's entry ordering exactly: entries
//!   are an append-only journal, and replay yields them in recorded order.

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::sync::Arc;

use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, Outcome, ResourceUsage};
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::domain::{Digest, Domain, hash};

use crate::modules::{CancellationProbe, ModuleEpoch};
use crate::provenance::ExtensionEntryId;

/// The epoch fixtures capture under, so the ~35 existing `checkpoint` call sites keep
/// their shape. Test-only: production capture takes its epoch from the caller.
#[cfg(test)]
pub(crate) fn fixture_epoch() -> ModuleEpoch {
    ModuleEpoch::new("v4.32.0", "0000000000000000000000000000000000000000")
}

/// Declared merge semantics for one extension — the contract branch/merge consults.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeSemantics {
    /// Entries concatenate in branch order (the common upstream replay shape).
    AppendOrdered,
    /// The derived semantic view is a set keyed by exact payload bytes. The raw
    /// replay journal remains lossless and ordered: branch merges retain every
    /// entry, including duplicates, in a canonical branch order.
    SetUnion,
    /// The extension cannot be merged automatically; a branch merge touching it is
    /// a semantic conflict surfaced to the caller (plan §15.3b), never silent.
    ConflictsRequireReview,
}

/// Declared checkpoint semantics: what a snapshot must capture.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckpointSemantics {
    /// The journal suffix since the base commit fully describes the state.
    JournalSuffix,
    /// The full journal must be captured (state is order-sensitive beyond suffixes).
    FullJournal,
}

/// How well the toolchain understands a payload — provenance, not a guess.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PayloadProvenance {
    /// The payload schema is native-understood; fine-grained invalidation may see
    /// through it.
    Understood,
    /// Opaque bytes: preserved losslessly, flagged, and conservatively blocking.
    Opaque,
}

/// One registered extension: identity plus declared contracts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionDescriptor {
    pub name: Name,
    pub merge: MergeSemantics,
    pub checkpoint: CheckpointSemantics,
    pub provenance: PayloadProvenance,
}

/// One replay entry: bytes as imported, order-significant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionEntry {
    pub payload: Arc<[u8]>,
}

const JOURNAL_CHUNK_CAPACITY: usize = 32;
const JOURNAL_BITS: u32 = 5;

#[derive(Debug, Clone)]
struct JournalRecord {
    entry: ExtensionEntry,
    prefix_digest: Digest,
    prefix_payload_bytes: u128,
}

#[derive(Debug)]
enum JournalNode {
    Branch { children: Vec<Arc<JournalNode>> },
    Leaf { records: Vec<JournalRecord> },
}

/// A 32-way persistent vector specialized for append-only extension histories.
///
/// The root `Arc` makes clone and non-final drop one reference-count operation.
/// Append path-copies at most one node per level; depth is bounded by the number
/// of five-bit groups in `usize`, independent of the current journal length as a
/// machine-level resource bound. A final drop visits only the uniquely owned tree,
/// with the same bounded depth. Iterators borrow the journal and stream entries
/// oldest-to-newest without allocating a flattened buffer. Equality is exact
/// ordered-entry equality, not root identity. Prefix validation uses cached digest,
/// byte-count, and length facts for bounded lookup; detailed mismatch diagnostics
/// scan only when a prefix actually disagrees. Entry count and payload bytes are
/// cached explicitly so checkpoint limits never depend on an unbounded pre-scan.
#[derive(Debug, Clone)]
struct ExtensionJournal {
    root: Option<Arc<JournalNode>>,
    len: usize,
    depth: u32,
    digest: Digest,
    payload_bytes: u128,
}

impl Default for ExtensionJournal {
    fn default() -> Self {
        ExtensionJournal {
            root: None,
            len: 0,
            depth: 0,
            digest: empty_journal_digest(),
            payload_bytes: 0,
        }
    }
}

impl ExtensionJournal {
    fn from_entries(entries: impl IntoIterator<Item = ExtensionEntry>) -> ExtensionJournal {
        let mut leaves = Vec::new();
        let mut records = Vec::with_capacity(JOURNAL_CHUNK_CAPACITY);
        let mut len = 0usize;
        let mut digest = empty_journal_digest();
        let mut payload_bytes = 0u128;
        for entry in entries {
            len += 1;
            digest = next_journal_digest(digest, &entry.payload);
            payload_bytes += entry.payload.len() as u128;
            records.push(JournalRecord {
                entry,
                prefix_digest: digest,
                prefix_payload_bytes: payload_bytes,
            });
            if records.len() == JOURNAL_CHUNK_CAPACITY {
                leaves.push(Arc::new(JournalNode::Leaf { records }));
                records = Vec::with_capacity(JOURNAL_CHUNK_CAPACITY);
            }
        }
        if !records.is_empty() {
            leaves.push(Arc::new(JournalNode::Leaf { records }));
        }
        if leaves.is_empty() {
            return ExtensionJournal::default();
        }

        let mut nodes = leaves;
        let mut depth = 0u32;
        while nodes.len() > 1 {
            let mut parents = Vec::with_capacity(nodes.len().div_ceil(JOURNAL_CHUNK_CAPACITY));
            for children in nodes.chunks(JOURNAL_CHUNK_CAPACITY) {
                parents.push(Arc::new(JournalNode::Branch {
                    children: children.to_vec(),
                }));
            }
            nodes = parents;
            depth += 1;
        }
        ExtensionJournal {
            root: nodes.pop(),
            len,
            depth,
            digest,
            payload_bytes,
        }
    }

    fn push(&self, entry: ExtensionEntry) -> ExtensionJournal {
        let digest = next_journal_digest(self.digest, &entry.payload);
        let payload_bytes = self.payload_bytes + entry.payload.len() as u128;
        let record = JournalRecord {
            entry,
            prefix_digest: digest,
            prefix_payload_bytes: payload_bytes,
        };
        let (root, depth) = match &self.root {
            None => (new_journal_path(0, record), 0),
            Some(root) if self.len == journal_capacity(self.depth) => (
                Arc::new(JournalNode::Branch {
                    children: vec![Arc::clone(root), new_journal_path(self.depth, record)],
                }),
                self.depth + 1,
            ),
            Some(root) => (
                journal_insert(root, self.depth, self.len, record),
                self.depth,
            ),
        };
        ExtensionJournal {
            root: Some(root),
            len: self.len + 1,
            depth,
            digest,
            payload_bytes,
        }
    }

    /// Whether these are the same journal **by construction** — the same root node,
    /// not merely equal contents.
    ///
    /// `O(1)`, and it is a *proof*, not an accelerator: sharing a root node means the
    /// two values were built from one another, which digest equality can never
    /// establish. Deliberately conservative in one direction — an independently
    /// rebuilt journal with identical contents answers `false` and must then be proved
    /// by exact comparison, which is the slow path rather than a refusal.
    ///
    /// The pointer is **compared, never recorded**: no address enters a digest, a
    /// canonical encoding, or any evidence record.
    fn is_same_structure(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (None, None) => true,
            (Some(mine), Some(theirs)) => Arc::ptr_eq(mine, theirs) && self.len == other.len,
            (None, Some(_)) | (Some(_), None) => false,
        }
    }

    fn records(&self) -> JournalIter<'_> {
        let mut stack = Vec::with_capacity(self.depth as usize + 1);
        if let Some(root) = &self.root {
            stack.push((root.as_ref(), 0));
        }
        JournalIter { stack }
    }

    fn records_from(&self, index: usize) -> JournalIter<'_> {
        if index >= self.len {
            return JournalIter { stack: Vec::new() };
        }
        let mut stack = Vec::with_capacity(self.depth as usize + 1);
        let mut node = self.root.as_deref();
        let mut depth = self.depth;
        while let Some(current) = node {
            match (depth, current) {
                (0, JournalNode::Leaf { .. }) => {
                    stack.push((current, index & (JOURNAL_CHUNK_CAPACITY - 1)));
                    break;
                }
                (_, JournalNode::Branch { children }) => {
                    let slot = (index >> (JOURNAL_BITS * depth)) & (JOURNAL_CHUNK_CAPACITY - 1);
                    stack.push((current, slot + 1));
                    node = children.get(slot).map(Arc::as_ref);
                    depth -= 1;
                }
                _ => return JournalIter { stack: Vec::new() },
            }
        }
        JournalIter { stack }
    }

    fn prefix_facts(&self, len: usize) -> Option<(Digest, u128, usize)> {
        if len == 0 {
            return Some((empty_journal_digest(), 0, 0));
        }
        if len > self.len {
            return None;
        }
        let mut node = self.root.as_deref()?;
        let mut depth = self.depth;
        let index = len - 1;
        let mut lookup_steps = 1;
        loop {
            match (depth, node) {
                (0, JournalNode::Leaf { records }) => {
                    let record = records.get(index & (JOURNAL_CHUNK_CAPACITY - 1))?;
                    return Some((
                        record.prefix_digest,
                        record.prefix_payload_bytes,
                        lookup_steps,
                    ));
                }
                (_, JournalNode::Branch { children }) => {
                    let slot = (index >> (JOURNAL_BITS * depth)) & (JOURNAL_CHUNK_CAPACITY - 1);
                    node = children.get(slot)?.as_ref();
                    depth -= 1;
                    lookup_steps += 1;
                }
                _ => return None,
            }
        }
    }

    fn integrity(&self) -> Result<(), &'static str> {
        if self.root.is_some() != (self.len != 0) {
            return Err("journal root/length mismatch");
        }
        let mut observed_len = 0usize;
        let mut observed_digest = empty_journal_digest();
        let mut observed_payload_bytes = 0u128;
        for record in self.records() {
            observed_len += 1;
            observed_digest = next_journal_digest(observed_digest, &record.entry.payload);
            observed_payload_bytes += record.entry.payload.len() as u128;
            if record.prefix_digest != observed_digest
                || record.prefix_payload_bytes != observed_payload_bytes
            {
                return Err("journal prefix facts do not match payload history");
            }
        }
        if observed_len != self.len {
            return Err("journal entry count mismatch");
        }
        if observed_digest != self.digest {
            return Err("journal digest mismatch");
        }
        if observed_payload_bytes != self.payload_bytes {
            return Err("journal payload-byte count mismatch");
        }
        Ok(())
    }

    #[cfg(test)]
    fn node_ptrs(&self) -> Vec<*const ()> {
        fn walk(node: &Arc<JournalNode>, out: &mut Vec<*const ()>) {
            out.push(Arc::as_ptr(node).cast());
            if let JournalNode::Branch { children } = node.as_ref() {
                for child in children {
                    walk(child, out);
                }
            }
        }
        let mut out = Vec::new();
        if let Some(root) = &self.root {
            walk(root, &mut out);
        }
        out
    }

    #[cfg(test)]
    fn next_append_work(&self) -> JournalAppendWork {
        let Some(mut node) = self.root.as_deref() else {
            return JournalAppendWork {
                node_allocations: 1,
                ..JournalAppendWork::default()
            };
        };
        if self.len == journal_capacity(self.depth) {
            return JournalAppendWork {
                node_allocations: self.depth as usize + 2,
                copied_child_slots: 1,
                copied_entry_slots: 0,
            };
        }

        let mut work = JournalAppendWork::default();
        let mut depth = self.depth;
        loop {
            work.node_allocations += 1;
            match (depth, node) {
                (0, JournalNode::Leaf { records }) => {
                    work.copied_entry_slots += records.len();
                    return work;
                }
                (_, JournalNode::Branch { children }) => {
                    work.copied_child_slots += children.len();
                    let slot = (self.len >> (JOURNAL_BITS * depth)) & (JOURNAL_CHUNK_CAPACITY - 1);
                    let Some(child) = children.get(slot) else {
                        work.node_allocations += depth as usize;
                        return work;
                    };
                    node = child.as_ref();
                    depth -= 1;
                }
                _ => return work,
            }
        }
    }
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct JournalAppendWork {
    node_allocations: usize,
    copied_child_slots: usize,
    copied_entry_slots: usize,
}

fn empty_journal_digest() -> Digest {
    let mut w = CanonWriter::new();
    w.str("fln.extension-journal-history");
    w.u16(1);
    w.u8(0);
    hash(Domain::ExtensionDelta, &w.into_bytes())
}

fn next_journal_digest(previous: Digest, payload: &[u8]) -> Digest {
    let mut w = CanonWriter::new();
    w.str("fln.extension-journal-history");
    w.u16(1);
    w.u8(1);
    w.bytes(&previous.0);
    w.bytes(payload);
    hash(Domain::ExtensionDelta, &w.into_bytes())
}

fn journal_capacity(depth: u32) -> usize {
    1usize
        .checked_shl(JOURNAL_BITS * (depth + 1))
        .unwrap_or(usize::MAX)
}

fn new_journal_path(depth: u32, record: JournalRecord) -> Arc<JournalNode> {
    if depth == 0 {
        Arc::new(JournalNode::Leaf {
            records: vec![record],
        })
    } else {
        Arc::new(JournalNode::Branch {
            children: vec![new_journal_path(depth - 1, record)],
        })
    }
}

fn journal_insert(
    node: &Arc<JournalNode>,
    depth: u32,
    index: usize,
    record: JournalRecord,
) -> Arc<JournalNode> {
    match (depth, node.as_ref()) {
        (0, JournalNode::Leaf { records }) => {
            let mut next = records.clone();
            next.push(record);
            Arc::new(JournalNode::Leaf { records: next })
        }
        (depth, JournalNode::Branch { children }) => {
            let shift = JOURNAL_BITS * depth;
            let slot = (index >> shift) & (JOURNAL_CHUNK_CAPACITY - 1);
            let mut next = children.clone();
            if let Some(child) = next.get_mut(slot) {
                *child = journal_insert(child, depth - 1, index, record);
            } else {
                next.push(new_journal_path(depth - 1, record));
            }
            Arc::new(JournalNode::Branch { children: next })
        }
        _ => unreachable!("journal depth and node kind disagree"),
    }
}

impl PartialEq for ExtensionJournal {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len
            && self
                .records()
                .map(|record| &record.entry)
                .eq(other.records().map(|record| &record.entry))
    }
}

impl Eq for ExtensionJournal {}

struct JournalIter<'a> {
    stack: Vec<(&'a JournalNode, usize)>,
}

impl<'a> Iterator for JournalIter<'a> {
    type Item = &'a JournalRecord;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (node, index) = *self.stack.last()?;
            match node {
                JournalNode::Leaf { records } => {
                    if let Some(record) = records.get(index) {
                        self.stack.last_mut()?.1 += 1;
                        return Some(record);
                    }
                    self.stack.pop();
                }
                JournalNode::Branch { children } => {
                    if let Some(child) = children.get(index) {
                        self.stack.last_mut()?.1 += 1;
                        self.stack.push((child.as_ref(), 0));
                    } else {
                        self.stack.pop();
                    }
                }
            }
        }
    }
}

/// Independent environment-boundary limits for exact SetUnion projection and
/// merge. Limits cover the complete raw product, including duplicates, because
/// every admitted raw entry remains authoritative replay evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetUnionLimits {
    pub max_entries: usize,
    pub max_payload_bytes: u128,
    pub max_entry_bytes: usize,
}

impl SetUnionLimits {
    pub const fn new(max_entries: usize, max_payload_bytes: u128, max_entry_bytes: usize) -> Self {
        SetUnionLimits {
            max_entries,
            max_payload_bytes,
            max_entry_bytes,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SetUnionResource {
    Entries,
    PayloadBytes,
    EntryBytes,
}

/// Deterministic accounting for one SetUnion projection attempt.
///
/// Count and cumulative-byte limits are checked from cached journal facts in
/// O(1), so their refusal consumes no entries. Once those limits admit the raw
/// product, merge performs one length-only O(n) preflight before any payload
/// comparison, at most one O(n) lexicographic suffix comparison, and an exact
/// projection using `BTreeSet<&[u8]>`: O(n log u) exact-byte comparisons and
/// O(u) borrowed keys for `n` raw entries and `u` first occurrences, with no
/// payload-byte copies. `examined_*` records the logical raw-product extent of
/// the terminal preflight or projection, not repeated iterator visits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetUnionFacts {
    pub limits: SetUnionLimits,
    pub raw_entries: usize,
    pub raw_payload_bytes: u128,
    pub examined_entries: usize,
    pub examined_payload_bytes: u128,
    pub maximum_entry_bytes: usize,
    pub semantic_entries: usize,
    pub duplicate_entries: usize,
}

impl SetUnionFacts {
    fn new(limits: SetUnionLimits, raw_entries: usize, raw_payload_bytes: u128) -> Self {
        SetUnionFacts {
            limits,
            raw_entries,
            raw_payload_bytes,
            examined_entries: 0,
            examined_payload_bytes: 0,
            maximum_entry_bytes: 0,
            semantic_entries: 0,
            duplicate_entries: 0,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetUnionInconclusive {
    pub extension: Name,
    pub resource: SetUnionResource,
    pub limit: u128,
    pub actual: u128,
}

/// A bounded semantic projection. An inconclusive result exposes accounting but
/// never exposes the partially built semantic view.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SetUnionProjection<'a> {
    Complete {
        entries: Vec<&'a ExtensionEntry>,
        facts: SetUnionFacts,
    },
    Inconclusive {
        reason: SetUnionInconclusive,
        facts: SetUnionFacts,
    },
}

/// The merge result keeps resource exhaustion structurally distinct from both a
/// semantic conflict and a completed product (FL-INV-07). The inconclusive
/// variant contains no state, so a partial journal/root cannot be published.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtensionMergeOutcome {
    Complete {
        state: ExtensionState,
        set_union_facts: Option<SetUnionFacts>,
    },
    Inconclusive {
        reason: SetUnionInconclusive,
        facts: SetUnionFacts,
    },
}

/// The first entry index at which two extension states' journals differ, or `None`
/// when they are exactly equal over the shorter of the two.
///
/// Deterministic exact comparison: it compares *values*, in order, and stops at the
/// first divergence. This is the proof that digest equality cannot supply, and it is
/// the reason a content-identical base rebuilt from scratch is accepted while a
/// same-length or same-digest different history is not.
///
/// Cost is linear in the compared prefix and is not yet bounded by an explicit budget.
/// Making exhaustion here a typed FL-INV-07 inconclusive requires `restore` to return
/// an `Outcome` rather than a `Result`, because a `CheckpointError` is a rejection type
/// and reporting "we ran out of comparison budget" as a rejection would be the exact
/// collapse this bead exists to prevent. That signature change is the next slice.
/// Fixture-only unbounded form. `#[cfg(test)]` because with the production path bounded
/// there is no reason for an uncharged comparison to be reachable.
#[cfg(test)]
fn first_entry_divergence(left: &ExtensionState, right: &ExtensionState) -> Option<usize> {
    bounded_entry_divergence(left, right, ProofBudget::UNBOUNDED)
        .expect("an unbounded budget cannot bind")
}

/// [`first_entry_divergence`], charged against a budget.
///
/// Charges before comparing, so the entry that would exceed the budget is never
/// examined: a budget that is only checked after the work is a budget that permits one
/// unbounded step. Both dimensions are charged per entry, and payload bytes are charged
/// from the *left* side, which is the retained base — the side whose size the caller can
/// actually bound.
fn bounded_entry_divergence(
    left: &ExtensionState,
    right: &ExtensionState,
    budget: ProofBudget,
) -> BoundedComparison {
    let mut index = 0usize;
    let mut compared_bytes = 0u128;
    let mut left_entries = left.entries();
    let mut right_entries = right.entries();
    loop {
        match (left_entries.next(), right_entries.next()) {
            (Some(mine), Some(theirs)) => {
                if index >= budget.max_compared_entries {
                    return Err((
                        ProofDimension::ComparedEntries,
                        u128::try_from(budget.max_compared_entries).unwrap_or(u128::MAX),
                        u128::try_from(index).unwrap_or(u128::MAX).saturating_add(1),
                    ));
                }
                let next_bytes =
                    compared_bytes.saturating_add(u128::try_from(mine.payload.len()).unwrap_or(0));
                if next_bytes > budget.max_compared_payload_bytes {
                    return Err((
                        ProofDimension::ComparedPayloadBytes,
                        budget.max_compared_payload_bytes,
                        next_bytes,
                    ));
                }
                compared_bytes = next_bytes;
                if mine != theirs {
                    return Ok(Some(index));
                }
                index += 1;
            }
            (None, None) => return Ok(None),
            // One ran out first: they diverge at that length. The digest fast path
            // already rejects a length mismatch, so reaching this means a genuinely
            // inconsistent input rather than an ordinary short base.
            (None, Some(_)) | (Some(_), None) => return Ok(Some(index)),
        }
    }
}

/// What a caller allows one base-identity proof to cost.
///
/// Separate from [`CheckpointLimits`], which bounds the entries a checkpoint *carries*.
/// This bounds the entries a proof *compares*, which is a different quantity over a
/// different input: a one-entry suffix over a million-entry base carries one entry and
/// may compare a million. Conflating them would let a tight carry limit imply a bound
/// it does not provide.
///
/// `UNBOUNDED` and the `Default` mirror [`CheckpointLimits`]' neighbours in this crate,
/// so an unset budget behaves exactly as the pre-budget code did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofBudget {
    /// Entries the exact comparison may examine.
    pub max_compared_entries: usize,
    /// Canonical payload bytes the exact comparison may examine.
    pub max_compared_payload_bytes: u128,
}

impl ProofBudget {
    pub const UNBOUNDED: ProofBudget = ProofBudget {
        max_compared_entries: usize::MAX,
        max_compared_payload_bytes: u128::MAX,
    };

    pub const fn new(max_compared_entries: usize, max_compared_payload_bytes: u128) -> Self {
        ProofBudget {
            max_compared_entries,
            max_compared_payload_bytes,
        }
    }
}

impl Default for ProofBudget {
    fn default() -> Self {
        Self::UNBOUNDED
    }
}

/// Which quantity a [`ProofBudget`] bound.
///
/// A fact on the report, not a new [`StructuralUnit`]: both are `ProducedNodes` under
/// the closed D8 taxonomy, whose bar for a new unit is that a caller must react
/// differently, and the reaction to both is the same — raise the budget or accept that
/// this base cannot be proved here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofDimension {
    ComparedEntries,
    ComparedPayloadBytes,
}

impl ProofDimension {
    const fn as_str(self) -> &'static str {
        match self {
            ProofDimension::ComparedEntries => "compared_entries",
            ProofDimension::ComparedPayloadBytes => "compared_payload_bytes",
        }
    }
}

/// A bounded exact comparison: either it finished, or it ran out.
///
/// `Ok(None)` means the histories are exactly equal over the compared range, `Ok(Some)`
/// names the first divergence, and `Err` means the budget bound before either could be
/// established — which is a non-answer, never a divergence. Returning "diverged" for a
/// comparison that never finished is the precise defect this bead exists to prevent.
type BoundedComparison = Result<Option<usize>, (ProofDimension, u128, u128)>;

fn proof_stop(dimension: ProofDimension, allowed: u128, observed: u128) -> Inconclusive {
    Inconclusive::resource(ResourceUsage {
        reason: ResourceReason::StructuralBudget {
            unit: StructuralUnit::ProducedNodes,
        },
        allowed: u64::try_from(allowed).unwrap_or(u64::MAX),
        // A stop must report spending past its allowance or it is not a stop, and
        // `is_genuine_exhaustion` depends on it.
        observed: u64::try_from(observed)
            .unwrap_or(u64::MAX)
            .max(u64::try_from(allowed).unwrap_or(u64::MAX).saturating_add(1)),
    })
    .with_progress(dimension.as_str())
}

/// How a base-identity proof was discharged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HistoryProofKind {
    /// The presented base was the retained base by construction. `O(1)`, charged nothing.
    SharedStructure,
    /// Proved entry by entry against the retained base.
    ExactComparison,
    /// `FullJournal`: self-contained, so there was no base to prove.
    SelfContained,
}

/// Exact work one base-identity proof consumed.
///
/// **Phase-local**: it describes the proof, not the whole restore, and it is a logical
/// attributed count of entries and canonical payload bytes examined — never allocator
/// bytes, RSS, or wall time. Recorded on the plan so a later phase that recharged the
/// same proof would be visible rather than merely wasteful.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HistoryProofUsage {
    pub kind: HistoryProofKind,
    pub compared_entries: usize,
    pub compared_payload_bytes: u128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum HistoryMaterial {
    Suffix {
        base: ExtensionState,
        suffix: ExtensionJournal,
    },
    Full {
        state: ExtensionState,
    },
}

/// One restored extension state, with what committing it cost.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionHistoryRestored {
    pub state: ExtensionState,
    /// Work **this commit** consumed. Zero by contract in every mode: the proof was
    /// discharged at plan time and is never recomputed. A non-zero value here means
    /// something recharged the history proof, which is why the field exists.
    pub commit_usage: HistoryProofUsage,
}

/// An immutable, non-authoritative extension-history identity plan (bead
/// `fln-extension-history-checkpoint-identity-41s`).
///
/// Bound to the exact base, schema, descriptor and limits it was decided under.
/// Deliberately the twin of `franken_lean-j8h`'s declaration-admission plan rather than
/// a second shape: holding material is not authority, nothing here is reachable as an
/// extension state, it is never cacheable, and committing revalidates before applying.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedExtensionHistory {
    schema: u16,
    descriptor: ExtensionDescriptor,
    limits: CheckpointLimits,
    usage: HistoryProofUsage,
    material: HistoryMaterial,
}

impl PreparedExtensionHistory {
    /// **Never.** A plan is a decision in flight, not a result.
    pub const fn is_cacheable(&self) -> bool {
        false
    }

    /// What the base-identity proof cost. Available before commit because it describes
    /// work already done; the state it authorises is not available until commit.
    pub const fn proof_usage(&self) -> &HistoryProofUsage {
        &self.usage
    }

    pub const fn descriptor(&self) -> &ExtensionDescriptor {
        &self.descriptor
    }

    /// Whether this plan is still meaningful for `base`.
    ///
    /// `O(1)` and charges nothing: the plan holds the base it proved against, so
    /// revalidation is a structural-identity check rather than a second comparison.
    /// A plan decided against one base and committed against another is refused even
    /// when the two are content-identical, because the plan's recorded proof describes
    /// the base it was given.
    pub fn is_valid_for(&self, base: Option<&ExtensionState>) -> bool {
        if self.schema != EXTENSION_CHECKPOINT_SCHEMA_VERSION {
            return false;
        }
        match (&self.material, base) {
            (HistoryMaterial::Suffix { base: planned, .. }, Some(presented)) => {
                planned.journal.is_same_structure(&presented.journal)
                    && planned.descriptor == presented.descriptor
            }
            (HistoryMaterial::Full { .. }, None) => true,
            _ => false,
        }
    }

    /// Revalidate and apply exactly once.
    ///
    /// Three things are rechecked and **nothing is recomputed**: the plan's schema, its
    /// base binding, and cancellation. The base-identity proof is *consumed*, not
    /// repeated — repeating it would charge the same work twice and could disagree with
    /// the decision the plan already records.
    ///
    /// Applying is immutable: the base is never mutated, so every non-applied arm leaves
    /// the caller's state the same value it already held, with the same content digest
    /// and the same structural sharing.
    pub fn commit(
        &self,
        base: Option<&ExtensionState>,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<ExtensionHistoryRestored, CheckpointError> {
        if !self.is_valid_for(base) {
            return Err(CheckpointError::PlanSuperseded {
                extension: self.descriptor.name.clone(),
            });
        }
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            // A cancelled commit is a non-answer, and this signature cannot carry one —
            // so callers that thread cancellation must sample it themselves before
            // committing. `try_restore` does exactly that at
            // `CheckpointProofCheckpoint::BeforePublication`. Reaching here means the
            // probe tripped between that sample and this one; refusing to apply is the
            // conservative half, and the caller's own outcome carries the authority.
            return Err(CheckpointError::PlanSuperseded {
                extension: self.descriptor.name.clone(),
            });
        }
        let state = match &self.material {
            HistoryMaterial::Suffix { base, suffix } => {
                let mut restored = base.clone();
                for record in suffix.records() {
                    restored = restored.push_entry(Arc::clone(&record.entry.payload));
                }
                restored
            }
            HistoryMaterial::Full { state } => state.clone(),
        };
        Ok(ExtensionHistoryRestored {
            state,
            // Zero in every mode: applying a suffix examines the SUFFIX, never the base,
            // and the base is the only thing the proof measured.
            commit_usage: HistoryProofUsage {
                kind: self.usage.kind,
                compared_entries: 0,
                compared_payload_bytes: 0,
            },
        })
    }
}

/// Frozen cancellation observation points for the checkpoint identity proofs.
///
/// Numbered and fixed for the same reason the declaration-admission checkpoints are: a
/// probe that trips must name the same point every run, or the outcome is
/// schedule-dependent. The digest accelerators are deliberately *not* checkpoints —
/// they are constant work and there is nothing to abandon there, and claiming a
/// checkpoint that cannot fire is an untruthful contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckpointProofCheckpoint {
    /// Before any input-sized base-identity proof work.
    BeforeBaseProof,
    /// After the proof succeeded and before the restored state is handed back.
    BeforePublication,
}

impl std::fmt::Display for CheckpointProofCheckpoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheckpointProofCheckpoint::BeforeBaseProof => write!(f, "before-base-proof"),
            CheckpointProofCheckpoint::BeforePublication => write!(f, "before-publication"),
        }
    }
}

/// The first index at which `base` is not a prefix of `target`, or `None` when it is
/// exactly a prefix.
///
/// The capture-side counterpart of [`first_entry_divergence`], and the proof that the
/// stored cumulative prefix digest cannot supply. `base` shorter than `target` is the
/// normal case; a base that runs longer than the target is a divergence at the target's
/// length, which the caller's own length arithmetic would otherwise underflow on.
/// Fixture-only unbounded form — see [`first_entry_divergence`].
#[cfg(test)]
fn prefix_divergence(target: &ExtensionState, base: &ExtensionState) -> Option<usize> {
    bounded_prefix_divergence(target, base, ProofBudget::UNBOUNDED)
        .expect("an unbounded budget cannot bind")
}

/// [`prefix_divergence`], charged against a budget, with the same charge-before-compare
/// rule as [`bounded_entry_divergence`].
fn bounded_prefix_divergence(
    target: &ExtensionState,
    base: &ExtensionState,
    budget: ProofBudget,
) -> BoundedComparison {
    let mut target_entries = target.entries();
    let mut compared_bytes = 0u128;
    for (index, base_entry) in base.entries().enumerate() {
        if index >= budget.max_compared_entries {
            return Err((
                ProofDimension::ComparedEntries,
                u128::try_from(budget.max_compared_entries).unwrap_or(u128::MAX),
                u128::try_from(index).unwrap_or(u128::MAX).saturating_add(1),
            ));
        }
        let next_bytes =
            compared_bytes.saturating_add(u128::try_from(base_entry.payload.len()).unwrap_or(0));
        if next_bytes > budget.max_compared_payload_bytes {
            return Err((
                ProofDimension::ComparedPayloadBytes,
                budget.max_compared_payload_bytes,
                next_bytes,
            ));
        }
        compared_bytes = next_bytes;
        match target_entries.next() {
            Some(target_entry) if target_entry == base_entry => {}
            _ => return Ok(Some(index)),
        }
    }
    Ok(None)
}

/// Content identities for the entries a checkpoint carries, in journal order.
///
/// Uses the crate's existing [`ExtensionEntryId::derive`], which binds epoch tag, epoch
/// commit, descriptor name and all three descriptor semantic tags, then the payload. So one
/// mechanism binds epoch, descriptor and value together, and the payload is hashed rather
/// than retained.
fn derive_entry_ids(
    epoch: &ModuleEpoch,
    descriptor: &ExtensionDescriptor,
    journal: &ExtensionJournal,
) -> Arc<[ExtensionEntryId]> {
    journal
        .records()
        .map(|record| ExtensionEntryId::derive(epoch, descriptor, &record.entry.payload))
        .collect()
}

/// The logical footprint a checkpoint retains beyond the entries it carries.
///
/// **Logical attributed accounting, not allocator ownership.** These are counts of
/// entries and canonical payload bytes the retained base denotes. They are not RSS,
/// not allocator-resident bytes, and not a claim that those bytes belong exclusively to
/// this checkpoint — the base is *shared*, which is the whole point of retaining a
/// handle instead of copying. No address or allocation identity appears here or in any
/// evidence derived from it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RetainedBaseFacts {
    /// Entries in the retained base.
    pub entries: usize,
    /// Canonical payload bytes the retained base denotes.
    pub payload_bytes: u128,
}

/// The only checkpoint schema version this build accepts. Unknown versions are a
/// typed refusal; they are never guessed compatible.
pub const EXTENSION_CHECKPOINT_SCHEMA_VERSION: u16 = 1;

/// Explicit resource limits for capture and restore. Limits apply to the entries
/// carried by the checkpoint: the suffix for [`CheckpointSemantics::JournalSuffix`]
/// and the complete journal for [`CheckpointSemantics::FullJournal`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckpointLimits {
    pub max_entries: usize,
    pub max_payload_bytes: u128,
}

impl CheckpointLimits {
    pub const fn new(max_entries: usize, max_payload_bytes: u128) -> Self {
        CheckpointLimits {
            max_entries,
            max_payload_bytes,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CheckpointPayload {
    JournalSuffix {
        base_len: usize,
        base_history_digest: Digest,
        base_state_digest: Digest,
        /// The retained base, held as an `Arc` so the journal nodes are **shared, not
        /// copied** (bead `fln-extension-history-checkpoint-identity-41s`).
        ///
        /// This exists because the recorded digests above cannot establish that a
        /// presented base *is* this base — they can only reject one that plainly is
        /// not. Restore proves base equality against this handle, by shared structural
        /// identity when the presented base was built from it and by deterministic
        /// exact comparison otherwise. Retaining it is what makes that proof possible,
        /// and it is reported through
        /// [`ExtensionCheckpoint::retained_base_facts`] because a checkpoint that
        /// silently keeps its base alive has a footprint a caller must be able to see.
        base: Arc<ExtensionState>,
        journal: ExtensionJournal,
    },
    FullJournal {
        journal: ExtensionJournal,
    },
}

/// A self-describing extension checkpoint. Its internals are private so callers
/// cannot manufacture an unchecked journal; durable decoding will construct this
/// value only after validating the same schema and limits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionCheckpoint {
    schema_version: u16,
    descriptor: ExtensionDescriptor,
    /// The epoch this checkpoint was captured under (bead
    /// `fln-extension-history-checkpoint-identity-41s`).
    ///
    /// Bound at CAPTURE time, not supplied at restore, because a self-contained checkpoint
    /// that cannot state its own epoch is not self-contained. It is also an input to every
    /// [`ExtensionEntryId`] below, so the binding is by DERIVATION rather than comparison:
    /// the same payloads under a different epoch produce different ids.
    epoch: ModuleEpoch,
    /// Content identities of the carried entries, in journal order.
    ///
    /// Derived from epoch, descriptor and payload through the crate's existing
    /// [`ExtensionEntryId`] mechanism, not a new one. Identity is stored; the bytes stay
    /// `Arc`-backed in the journal, so payload identity is bound without copying payload.
    entry_ids: Arc<[ExtensionEntryId]>,
    captured_entries: usize,
    captured_payload_bytes: u128,
    payload: CheckpointPayload,
}

impl ExtensionCheckpoint {
    pub fn schema_version(&self) -> u16 {
        self.schema_version
    }

    pub fn descriptor(&self) -> &ExtensionDescriptor {
        &self.descriptor
    }

    pub fn mode(&self) -> CheckpointSemantics {
        match &self.payload {
            CheckpointPayload::JournalSuffix { .. } => CheckpointSemantics::JournalSuffix,
            CheckpointPayload::FullJournal { .. } => CheckpointSemantics::FullJournal,
        }
    }

    pub fn captured_entries(&self) -> usize {
        self.captured_entries
    }

    pub fn captured_payload_bytes(&self) -> u128 {
        self.captured_payload_bytes
    }

    /// The epoch this checkpoint was captured under.
    ///
    /// A caller that requires a checkpoint from its own epoch compares this and refuses;
    /// that policy is the caller's. Restore validates the entry ids against THIS epoch,
    /// which catches tampering but deliberately does not decide whose epoch is correct.
    pub fn epoch(&self) -> &ModuleEpoch {
        &self.epoch
    }

    /// Content identities of the carried entries, in journal order.
    pub fn entry_ids(&self) -> &[ExtensionEntryId] {
        &self.entry_ids
    }

    /// Bounded test seam: forge the recorded entry ids so they no longer re-derive.
    ///
    /// Needed because capture always derives ids consistently, so nothing in normal
    /// operation can make the restore-side check fire — and a check nothing can make fire
    /// is unfalsifiable.
    #[cfg(test)]
    fn forge_entry_ids(mut self, entry_ids: Arc<[ExtensionEntryId]>) -> Self {
        self.entry_ids = entry_ids;
        self
    }

    /// Bounded test seam: forge the declared schema version.
    #[cfg(test)]
    fn forge_schema_version(mut self, schema_version: u16) -> Self {
        self.schema_version = schema_version;
        self
    }

    /// Bounded test seam: forge the declared cumulative facts so they disagree with the
    /// journal they describe.
    #[cfg(test)]
    fn forge_cumulative_facts(mut self, captured_entries: usize) -> Self {
        self.captured_entries = captured_entries;
        self
    }

    /// Bounded test seam: forge the recorded base digests so a *wrong* base passes
    /// every fast-path check.
    ///
    /// A digest collision cannot be produced on demand, so the only way to test that
    /// equality is treated as an accelerator rather than a proof is to simulate the
    /// collision. This overwrites just the two recorded digests, leaving the retained
    /// base handle and every other field alone — so restore's fast paths accept, and
    /// only the exact comparison can catch it. Test-only, and it constructs no state a
    /// production path can reach.
    #[cfg(test)]
    fn forge_recorded_base_digests(mut self, history: Digest, state: Digest) -> Self {
        if let CheckpointPayload::JournalSuffix {
            base_history_digest,
            base_state_digest,
            ..
        } = &mut self.payload
        {
            *base_history_digest = history;
            *base_state_digest = state;
        }
        self
    }

    /// What this checkpoint retains beyond the entries it carries.
    ///
    /// `Some` for suffix mode, which holds a shared handle to its base so restore can
    /// *prove* base equality rather than infer it from a digest. `None` for
    /// `FullJournal`, which is self-contained and retains nothing — so the difference
    /// in footprint between the two modes is visible rather than implied.
    ///
    /// Reporting this is a requirement, not a convenience: a checkpoint that keeps its
    /// base alive changes what a caller can drop, and a footprint that is invisible is
    /// a footprint nobody budgets for. See [`RetainedBaseFacts`] for what the numbers
    /// do and do not claim.
    pub fn retained_base_facts(&self) -> Option<RetainedBaseFacts> {
        match &self.payload {
            CheckpointPayload::JournalSuffix { base, .. } => Some(RetainedBaseFacts {
                entries: base.len(),
                payload_bytes: base.journal.payload_bytes,
            }),
            CheckpointPayload::FullJournal { .. } => None,
        }
    }

    pub fn base_len(&self) -> Option<usize> {
        match &self.payload {
            CheckpointPayload::JournalSuffix { base_len, .. } => Some(*base_len),
            CheckpointPayload::FullJournal { .. } => None,
        }
    }

    pub fn base_state_digest(&self) -> Option<Digest> {
        match &self.payload {
            CheckpointPayload::JournalSuffix {
                base_state_digest, ..
            } => Some(*base_state_digest),
            CheckpointPayload::FullJournal { .. } => None,
        }
    }

    /// Entries physically carried by this checkpoint, in exact replay order.
    pub fn entries(&self) -> impl Iterator<Item = &ExtensionEntry> {
        let journal = match &self.payload {
            CheckpointPayload::JournalSuffix { journal, .. }
            | CheckpointPayload::FullJournal { journal } => journal,
        };
        journal.records().map(|record| &record.entry)
    }

    fn journal(&self) -> &ExtensionJournal {
        match &self.payload {
            CheckpointPayload::JournalSuffix { journal, .. }
            | CheckpointPayload::FullJournal { journal } => journal,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckpointResource {
    Entries,
    PayloadBytes,
}

/// Every checkpoint refusal is classified and leaves all input snapshots unchanged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckpointError {
    /// The carried entries' re-derived identities do not match the recorded ones.
    ///
    /// A completed determination. Epoch, descriptor and every payload value are inputs to
    /// [`ExtensionEntryId::derive`], so this fires when any of them has moved since
    /// capture — including ids carried over from a different epoch.
    EntryIdentityMismatch {
        extension: Name,
        epoch_tag: String,
        entries: usize,
    },
    /// A [`PreparedExtensionHistory`] was committed against a base it was not decided
    /// against, or under a superseded schema.
    ///
    /// A completed determination *about this plan* — the plan is unusable here — rather
    /// than a statement that the checkpoint is bad: re-planning against the current base
    /// may well succeed.
    PlanSuperseded {
        extension: Name,
    },
    /// The presented base agreed with every recorded digest and still is not the base
    /// this checkpoint was captured against (bead
    /// `fln-extension-history-checkpoint-identity-41s`).
    ///
    /// A *completed determination*, so a rejection rather than an inconclusive: the
    /// exact comparison finished and the histories differ. `first_divergence` is the
    /// entry index where they parted, which is what a caller needs to act; it is
    /// diagnostic, and no address or allocation identity appears in it.
    BaseNotExact {
        extension: Name,
        base_len: usize,
        first_divergence: usize,
    },
    UnsupportedVersion {
        found: u16,
        supported: u16,
    },
    MissingBase {
        extension: Name,
    },
    UnexpectedBase {
        extension: Name,
    },
    ExtensionNameMismatch {
        expected: Name,
        actual: Name,
    },
    ContractMismatch {
        expected: ExtensionDescriptor,
        actual: ExtensionDescriptor,
    },
    ModeMismatch {
        descriptor_mode: CheckpointSemantics,
        payload_mode: CheckpointSemantics,
    },
    HistoryMismatch {
        extension: Name,
        base_len: usize,
        target_len: usize,
        common_prefix: usize,
    },
    BaseLengthMismatch {
        extension: Name,
        expected: usize,
        actual: usize,
    },
    BaseHistoryMismatch {
        extension: Name,
        expected: Digest,
        actual: Digest,
    },
    BaseDigestMismatch {
        extension: Name,
        expected: Digest,
        actual: Digest,
    },
    ResourceLimitExceeded {
        extension: Name,
        resource: CheckpointResource,
        limit: u128,
        actual: u128,
    },
    MalformedCheckpoint {
        extension: Name,
        reason: &'static str,
    },
}

impl std::fmt::Display for CheckpointError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheckpointError::EntryIdentityMismatch {
                extension,
                epoch_tag,
                entries,
            } => write!(
                f,
                "extension `{}` checkpoint carries {entries} entries whose identities do not \
                 re-derive under its own epoch `{epoch_tag}`: a payload, the descriptor, or \
                 the epoch has moved since capture",
                extension.to_display_string()
            ),
            CheckpointError::PlanSuperseded { extension } => write!(
                f,
                "extension `{}` history plan was decided against a different base or schema; \
                 re-plan against the current base rather than reusing this one",
                extension.to_display_string()
            ),
            CheckpointError::BaseNotExact {
                extension,
                base_len,
                first_divergence,
            } => write!(
                f,
                "extension `{}` presented a base that matched every recorded digest but \
                 diverges from the captured base at entry {first_divergence} of {base_len}: \
                 digest equality is a rejection accelerator, not a proof of base identity",
                extension.to_display_string()
            ),
            CheckpointError::UnsupportedVersion { found, supported } => write!(
                f,
                "unsupported extension checkpoint schema version {found}; supported version is {supported}"
            ),
            CheckpointError::MissingBase { extension } => write!(
                f,
                "extension `{}` uses journal-suffix checkpoints and requires a base",
                extension.to_display_string()
            ),
            CheckpointError::UnexpectedBase { extension } => write!(
                f,
                "extension `{}` uses full-journal checkpoints and refuses an ambient base",
                extension.to_display_string()
            ),
            CheckpointError::ExtensionNameMismatch { expected, actual } => write!(
                f,
                "extension checkpoint name mismatch: expected `{}`, got `{}`",
                expected.to_display_string(),
                actual.to_display_string()
            ),
            CheckpointError::ContractMismatch { expected, actual } => write!(
                f,
                "extension checkpoint contract mismatch for `{}`: expected {:?}/{:?}/{:?}, got {:?}/{:?}/{:?}",
                expected.name.to_display_string(),
                expected.merge,
                expected.checkpoint,
                expected.provenance,
                actual.merge,
                actual.checkpoint,
                actual.provenance
            ),
            CheckpointError::ModeMismatch {
                descriptor_mode,
                payload_mode,
            } => write!(
                f,
                "extension checkpoint payload mode {payload_mode:?} disagrees with descriptor mode {descriptor_mode:?}"
            ),
            CheckpointError::HistoryMismatch {
                extension,
                base_len,
                target_len,
                common_prefix,
            } => write!(
                f,
                "extension `{}` target does not descend from its checkpoint base: base_len={base_len}, target_len={target_len}, common_prefix={common_prefix}",
                extension.to_display_string()
            ),
            CheckpointError::BaseLengthMismatch {
                extension,
                expected,
                actual,
            } => write!(
                f,
                "extension `{}` checkpoint base length mismatch: expected {expected}, got {actual}",
                extension.to_display_string()
            ),
            CheckpointError::BaseHistoryMismatch {
                extension,
                expected,
                actual,
            } => write!(
                f,
                "extension `{}` checkpoint base history mismatch: expected {expected}, got {actual}",
                extension.to_display_string()
            ),
            CheckpointError::BaseDigestMismatch {
                extension,
                expected,
                actual,
            } => write!(
                f,
                "extension `{}` checkpoint base state mismatch: expected {expected}, got {actual}",
                extension.to_display_string()
            ),
            CheckpointError::ResourceLimitExceeded {
                extension,
                resource,
                limit,
                actual,
            } => write!(
                f,
                "extension `{}` checkpoint exceeds {resource:?} limit: limit={limit}, actual={actual}",
                extension.to_display_string()
            ),
            CheckpointError::MalformedCheckpoint { extension, reason } => write!(
                f,
                "extension `{}` checkpoint is malformed: {reason}",
                extension.to_display_string()
            ),
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct CheckpointWork {
    prefix_lookup_steps: usize,
    captured_entries: usize,
}

/// Stable `Domain::ExtensionDelta` descriptor tags. These are schema values, not
/// Rust enum discriminants: changing one requires an explicit identity/epoch
/// decision. The `forbid` is the same compile-time guard `fln-env`'s declaration
/// tags carry — it is stronger than a test, because a cast cannot be reintroduced
/// silently even by an author who never reads this comment.
#[forbid(clippy::as_conversions)]
const fn merge_semantics_tag(semantics: MergeSemantics) -> u8 {
    match semantics {
        MergeSemantics::AppendOrdered => 0,
        MergeSemantics::SetUnion => 1,
        MergeSemantics::ConflictsRequireReview => 2,
    }
}

#[forbid(clippy::as_conversions)]
const fn checkpoint_semantics_tag(semantics: CheckpointSemantics) -> u8 {
    match semantics {
        CheckpointSemantics::JournalSuffix => 0,
        CheckpointSemantics::FullJournal => 1,
    }
}

#[forbid(clippy::as_conversions)]
const fn payload_provenance_tag(provenance: PayloadProvenance) -> u8 {
    match provenance {
        PayloadProvenance::Understood => 0,
        PayloadProvenance::Opaque => 1,
    }
}

/// Write the stable descriptor prefix of `Domain::ExtensionDelta`.
///
/// Contract fields precede journal identity deliberately. The explicit tag helpers
/// make additions fail compilation until their durable schema values are reviewed.
fn write_descriptor_identity(w: &mut CanonWriter, descriptor: &ExtensionDescriptor) {
    descriptor.name.write_body(w);
    w.u8(merge_semantics_tag(descriptor.merge));
    w.u8(checkpoint_semantics_tag(descriptor.checkpoint));
    w.u8(payload_provenance_tag(descriptor.provenance));
}

/// The state of one extension inside an environment: its descriptor plus the
/// append-only entry journal. Cloning is cheap (shared journal tail via `Arc`s in
/// the persistent environment map).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionState {
    pub descriptor: ExtensionDescriptor,
    journal: ExtensionJournal,
}

impl ExtensionState {
    pub fn new(descriptor: ExtensionDescriptor) -> ExtensionState {
        ExtensionState {
            descriptor,
            journal: ExtensionJournal::default(),
        }
    }

    /// Append one imported entry (replay order is the Reference's order).
    pub fn push_entry(&self, payload: impl Into<Arc<[u8]>>) -> ExtensionState {
        ExtensionState {
            descriptor: self.descriptor.clone(),
            journal: self.journal.push(ExtensionEntry {
                payload: payload.into(),
            }),
        }
    }

    /// Entries in exact recorded order — replay IS iteration.
    pub fn len(&self) -> usize {
        self.journal.len
    }

    pub fn is_empty(&self) -> bool {
        self.journal.len == 0
    }

    pub fn entries(&self) -> impl Iterator<Item = &ExtensionEntry> {
        self.journal.records().map(|record| &record.entry)
    }

    /// Exact-byte semantic set projection in first raw-occurrence order.
    ///
    /// Only [`MergeSemantics::SetUnion`] assigns semantic meaning to this view.
    /// The raw journal remains authoritative, and the view becomes observable
    /// only after all independent limits admit the complete projection.
    pub fn semantic_projection(&self, limits: SetUnionLimits) -> SetUnionProjection<'_> {
        project_set_union_entries(
            &self.descriptor.name,
            self.journal.records().map(|record| &record.entry),
            self.len(),
            self.journal.payload_bytes,
            limits,
        )
    }

    /// Stable semantic identity for the extension contract and its exact ordered
    /// journal. The cached history digest makes this O(1) in journal length.
    /// Bounded test seam: forge this state's journal digest and payload byte count so a
    /// *wrong* base satisfies the capture-side accelerator.
    ///
    /// Distinct from [`ExtensionCheckpoint::forge_recorded_base_digests`] because the
    /// two defects live on opposite sides: capture compares a base's OWN digest against
    /// a prefix digest computed from the target, so simulating that collision means
    /// forging the base, not the checkpoint. Test-only, and it constructs no state a
    /// production path can reach.
    #[cfg(test)]
    fn forge_journal_facts(mut self, digest: Digest, payload_bytes: u128) -> Self {
        self.journal.digest = digest;
        self.journal.payload_bytes = payload_bytes;
        self
    }

    pub fn content_digest(&self) -> Digest {
        let mut w = CanonWriter::new();
        w.str("fln.extension-state");
        w.u16(1);
        write_descriptor_identity(&mut w, &self.descriptor);
        w.u64(self.journal.len as u64);
        w.bytes(&self.journal.digest.0);
        hash(Domain::ExtensionDelta, &w.into_bytes())
    }

    /// Capture this state according to the descriptor's declared checkpoint mode.
    /// Successful suffix capture performs only a bounded-depth prefix lookup plus
    /// work proportional to the suffix; it never flattens the base history.
    /// Capture a checkpoint, able to report a non-answer.
    ///
    /// The capture-side twin of [`ExtensionState::try_restore`], widened for the same
    /// reason: ancestry is established by exact prefix comparison whenever the digest
    /// accelerator only passes, and that comparison can be cancelled or — once bounded —
    /// exhausted. Neither is a statement that the base is wrong, so neither may arrive
    /// as a [`CheckpointError`].
    pub fn try_checkpoint(
        &self,
        base: Option<&ExtensionState>,
        limits: CheckpointLimits,
        proof: ProofBudget,
        epoch: &ModuleEpoch,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<ExtensionCheckpoint, CheckpointError>> {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                CheckpointProofCheckpoint::BeforeBaseProof.to_string(),
            ));
        }
        let captured = match self.checkpoint_bounded(base, limits, proof, epoch) {
            Ok(captured) => captured,
            Err(stop) => return Outcome::Inconclusive(stop),
        };
        if captured.is_ok() && cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                CheckpointProofCheckpoint::BeforePublication.to_string(),
            ));
        }
        Outcome::complete(captured)
    }

    /// Unbounded, uncancellable capture. **Fixture path only** — see
    /// [`ExtensionState::restore`] for why this is `#[cfg(test)]` rather than a
    /// documented public path.
    #[cfg(test)]
    fn checkpoint(
        &self,
        base: Option<&ExtensionState>,
        limits: CheckpointLimits,
    ) -> Result<ExtensionCheckpoint, CheckpointError> {
        self.checkpoint_bounded(base, limits, ProofBudget::UNBOUNDED, &fixture_epoch())
            .expect("an unbounded proof budget cannot bind")
    }

    /// The proof-bounded capture body. Outer `Err` is a budget stop, inner is a verdict.
    fn checkpoint_bounded(
        &self,
        base: Option<&ExtensionState>,
        limits: CheckpointLimits,
        proof: ProofBudget,
        epoch: &ModuleEpoch,
    ) -> Result<Result<ExtensionCheckpoint, CheckpointError>, Inconclusive> {
        Ok(self
            .checkpoint_with_work(base, limits, proof, epoch)?
            .map(|(checkpoint, work)| {
                debug_assert_eq!(work.captured_entries, checkpoint.captured_entries);
                debug_assert!(work.prefix_lookup_steps <= self.journal.depth as usize + 1);
                checkpoint
            }))
    }

    /// Outer `Err` is a budget stop, inner is a verdict — see
    /// [`ExtensionState::restore_bounded`] for why the two live at different depths.
    fn checkpoint_with_work(
        &self,
        base: Option<&ExtensionState>,
        limits: CheckpointLimits,
        proof: ProofBudget,
        epoch: &ModuleEpoch,
    ) -> Result<Result<(ExtensionCheckpoint, CheckpointWork), CheckpointError>, Inconclusive> {
        match self.descriptor.checkpoint {
            CheckpointSemantics::JournalSuffix => {
                let Some(base) = base else {
                    return Ok(Err(CheckpointError::MissingBase {
                        extension: self.descriptor.name.clone(),
                    }));
                };
                if let Err(refusal) =
                    validate_checkpoint_descriptor(&self.descriptor, &base.descriptor)
                {
                    return Ok(Err(refusal));
                }
                let Some((prefix_digest, prefix_payload_bytes, lookup_steps)) =
                    self.journal.prefix_facts(base.len())
                else {
                    return Ok(Err(history_mismatch(base, self)));
                };
                if prefix_digest != base.journal.digest
                    || prefix_payload_bytes != base.journal.payload_bytes
                {
                    return Ok(Err(history_mismatch(base, self)));
                }

                // The check above is a REJECTION ACCELERATOR, exactly as on the restore
                // side. `prefix_digest` is a cumulative digest stored on this journal's
                // entry at `base.len() - 1`; it agreeing with the base's own digest can
                // rule out a base that plainly is not our prefix, but it cannot
                // establish that this base IS that prefix — that is the same
                // "equality proves a relation" error, wearing the ancestry hat instead
                // of the base-equality one.
                //
                // Ancestry is proved here: compare the claimed prefix of `self` against
                // the base's entries, in order, exactly. `records()` yields this
                // journal's entries from the start, so taking `base.len()` of them IS
                // the claimed prefix.
                // Charged, and a stop here is a non-answer rather than a divergence.
                match bounded_prefix_divergence(self, base, proof) {
                    Ok(Some(divergence)) => {
                        return Ok(Err(CheckpointError::BaseNotExact {
                            extension: self.descriptor.name.clone(),
                            base_len: base.len(),
                            first_divergence: divergence,
                        }));
                    }
                    Ok(None) => {}
                    Err((dimension, allowed, observed)) => {
                        return Err(proof_stop(dimension, allowed, observed));
                    }
                }

                let captured_entries = self.len() - base.len();
                let captured_payload_bytes =
                    self.journal.payload_bytes - base.journal.payload_bytes;
                if let Err(refusal) = enforce_checkpoint_limits(
                    &self.descriptor.name,
                    captured_entries,
                    captured_payload_bytes,
                    limits,
                ) {
                    return Ok(Err(refusal));
                }

                let journal = ExtensionJournal::from_entries(
                    self.journal
                        .records_from(base.len())
                        .map(|record| record.entry.clone()),
                );
                let checkpoint = ExtensionCheckpoint {
                    schema_version: EXTENSION_CHECKPOINT_SCHEMA_VERSION,
                    descriptor: self.descriptor.clone(),
                    epoch: epoch.clone(),
                    entry_ids: derive_entry_ids(epoch, &self.descriptor, &journal),
                    captured_entries,
                    captured_payload_bytes,
                    payload: CheckpointPayload::JournalSuffix {
                        base_len: base.len(),
                        base_history_digest: base.journal.digest,
                        base_state_digest: base.content_digest(),
                        // `clone` is O(1) structural sharing: the journal's root `Arc`
                        // is shared, so this retains the base rather than copying it.
                        base: Arc::new(base.clone()),
                        journal,
                    },
                };
                Ok(Ok((
                    checkpoint,
                    CheckpointWork {
                        prefix_lookup_steps: lookup_steps,
                        captured_entries,
                    },
                )))
            }
            CheckpointSemantics::FullJournal => {
                if base.is_some() {
                    return Ok(Err(CheckpointError::UnexpectedBase {
                        extension: self.descriptor.name.clone(),
                    }));
                }
                if let Err(refusal) = enforce_checkpoint_limits(
                    &self.descriptor.name,
                    self.len(),
                    self.journal.payload_bytes,
                    limits,
                ) {
                    return Ok(Err(refusal));
                }
                let journal = ExtensionJournal::from_entries(
                    self.journal.records().map(|record| record.entry.clone()),
                );
                let checkpoint = ExtensionCheckpoint {
                    schema_version: EXTENSION_CHECKPOINT_SCHEMA_VERSION,
                    descriptor: self.descriptor.clone(),
                    epoch: epoch.clone(),
                    entry_ids: derive_entry_ids(epoch, &self.descriptor, &journal),
                    captured_entries: self.len(),
                    captured_payload_bytes: self.journal.payload_bytes,
                    payload: CheckpointPayload::FullJournal { journal },
                };
                Ok(Ok((
                    checkpoint,
                    CheckpointWork {
                        prefix_lookup_steps: 0,
                        captured_entries: self.len(),
                    },
                )))
            }
        }
    }

    /// Restore a checkpoint atomically. Inputs are immutable and every validation
    /// completes before the returned snapshot can become observable.
    /// Restore a checkpoint, able to report a non-answer.
    ///
    /// # Why this returns an `Outcome` and the old `restore` could not
    /// (bead `fln-extension-history-checkpoint-identity-41s`)
    ///
    /// Base identity is established by exact comparison whenever structural identity
    /// does not apply, and an exact comparison over an input-sized history can run out
    /// of budget or be cancelled. Both are FL-INV-07 **inconclusive**: no verdict was
    /// reached about this checkpoint. [`CheckpointError`] is a *rejection* vocabulary
    /// and cannot say "I ran out" — so reporting a budget stop through it would make a
    /// resource exhaustion arrive as a failed comparison, which is precisely the
    /// collapse this bead exists to prevent.
    ///
    /// So the type is widened **before** the proofs are bounded. A completed
    /// determination — malformed checkpoint, wrong descriptor, base not exact — is a
    /// `Result::Err` inside [`Outcome::Complete`], because a finished traversal
    /// reporting a refusal is a verdict (decision `fln-um4a`). Only cancellation and,
    /// once bounded, comparison exhaustion are non-answers.
    ///
    /// Cancellation is sampled at fixed [`CheckpointProofCheckpoint`]s, exhaustion is
    /// charged against `proof` before each compared entry, and neither is cacheable.
    pub fn try_restore(
        base: Option<&ExtensionState>,
        checkpoint: &ExtensionCheckpoint,
        limits: CheckpointLimits,
        proof: ProofBudget,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<ExtensionState, CheckpointError>> {
        // Sampled before any input-sized proof work: a caller who has given up must not
        // pay for a comparison, and must not have a state restored on their behalf.
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                CheckpointProofCheckpoint::BeforeBaseProof.to_string(),
            ));
        }
        let restored = match ExtensionState::restore_bounded(base, checkpoint, limits, proof) {
            Ok(restored) => restored,
            Err(stop) => return Outcome::Inconclusive(stop),
        };
        if restored.is_ok() && cancellation.is_some_and(CancellationProbe::is_cancelled) {
            // Proved, but the caller withdrew before publication. Discarding the result
            // is correct: a restored state nobody asked for any more is not a verdict.
            return Outcome::Inconclusive(Inconclusive::cancelled(
                CheckpointProofCheckpoint::BeforePublication.to_string(),
            ));
        }
        Outcome::complete(restored)
    }

    /// Unbounded, uncancellable restore. **Fixture path only.**
    ///
    /// `#[cfg(test)]` rather than documented-and-public, because with every production
    /// caller migrated to [`ExtensionState::try_restore`] there is no reason for an
    /// unbounded path to be reachable at all. Keeping it visible-but-public would be the
    /// compatibility path this bead forbids; keeping it test-only makes it a fixture
    /// helper whose non-authority is enforced by the compiler rather than by a comment.
    #[cfg(test)]
    fn restore(
        base: Option<&ExtensionState>,
        checkpoint: &ExtensionCheckpoint,
        limits: CheckpointLimits,
    ) -> Result<ExtensionState, CheckpointError> {
        ExtensionState::restore_bounded(base, checkpoint, limits, ProofBudget::UNBOUNDED)
            .expect("an unbounded proof budget cannot bind")
    }

    /// Restore as one preflighted transaction: plan, then commit.
    ///
    /// There is no second implementation — this *is* plan-then-commit, so the plan path
    /// and the direct path cannot drift apart. That is the same property
    /// `franken_lean-j8h`'s declaration admission has, and it is why the plan was added
    /// by refactoring the existing body rather than beside it.
    fn restore_bounded(
        base: Option<&ExtensionState>,
        checkpoint: &ExtensionCheckpoint,
        limits: CheckpointLimits,
        proof: ProofBudget,
    ) -> Result<Result<ExtensionState, CheckpointError>, Inconclusive> {
        let plan = match ExtensionState::plan_history_restore(base, checkpoint, limits, proof)? {
            Ok(plan) => plan,
            Err(refusal) => return Ok(Err(refusal)),
        };
        Ok(plan.commit(base, None).map(|restored| restored.state))
    }

    /// Preflight a checkpoint into an immutable, non-authoritative plan.
    ///
    /// Every validation and the whole base-identity proof happen here, once. The plan
    /// records what the proof cost so a later phase cannot charge it again — the bead's
    /// "consume the plan once, revalidate it, and never recompute or double-charge the
    /// history proof."
    ///
    /// The OUTER `Err` is a budget stop and never a verdict; the verdict lives in the
    /// inner `Result`. Keeping them at different depths is what makes "ran out" and
    /// "refused" impossible to confuse at a call site.
    fn plan_history_restore(
        base: Option<&ExtensionState>,
        checkpoint: &ExtensionCheckpoint,
        limits: CheckpointLimits,
        proof: ProofBudget,
    ) -> Result<Result<PreparedExtensionHistory, CheckpointError>, Inconclusive> {
        // Every `Ok(Err(..))` below is a completed VERDICT about this checkpoint. The
        // only `Err(..)` at the outer depth is a budget stop, and it appears exactly
        // once, at the bounded comparison. The extra `Ok(` is deliberate noise: it makes
        // each site say which kind of answer it is giving.
        if checkpoint.schema_version != EXTENSION_CHECKPOINT_SCHEMA_VERSION {
            return Ok(Err(CheckpointError::UnsupportedVersion {
                found: checkpoint.schema_version,
                supported: EXTENSION_CHECKPOINT_SCHEMA_VERSION,
            }));
        }
        let payload_mode = checkpoint.mode();
        if checkpoint.descriptor.checkpoint != payload_mode {
            return Ok(Err(CheckpointError::ModeMismatch {
                descriptor_mode: checkpoint.descriptor.checkpoint,
                payload_mode,
            }));
        }
        let journal = checkpoint.journal();
        if let Err(reason) = journal.integrity() {
            return Ok(Err(CheckpointError::MalformedCheckpoint {
                extension: checkpoint.descriptor.name.clone(),
                reason,
            }));
        }
        if journal.len != checkpoint.captured_entries
            || journal.payload_bytes != checkpoint.captured_payload_bytes
        {
            return Ok(Err(CheckpointError::MalformedCheckpoint {
                extension: checkpoint.descriptor.name.clone(),
                reason: "declared checkpoint measurements do not match its journal",
            }));
        }
        // Re-derive the carried entries' identities from the checkpoint's OWN epoch and
        // descriptor and compare against the recorded ids. Because the epoch is an input to
        // the derivation, one check binds epoch, descriptor and every payload value: a
        // tampered payload, a swapped descriptor, or ids carried over from another epoch all
        // fail here. It is not a substitute for a caller comparing `checkpoint.epoch()` to
        // its own — that is the caller's policy, and the accessor exists for it.
        if derive_entry_ids(&checkpoint.epoch, &checkpoint.descriptor, journal)
            != checkpoint.entry_ids
        {
            return Ok(Err(CheckpointError::EntryIdentityMismatch {
                extension: checkpoint.descriptor.name.clone(),
                epoch_tag: checkpoint.epoch.tag().to_owned(),
                entries: journal.len,
            }));
        }
        if let Err(refusal) = enforce_checkpoint_limits(
            &checkpoint.descriptor.name,
            journal.len,
            journal.payload_bytes,
            limits,
        ) {
            return Ok(Err(refusal));
        }

        match &checkpoint.payload {
            CheckpointPayload::JournalSuffix {
                base_len,
                base_history_digest,
                base_state_digest,
                base: retained_base,
                journal,
            } => {
                let Some(base) = base else {
                    return Ok(Err(CheckpointError::MissingBase {
                        extension: checkpoint.descriptor.name.clone(),
                    }));
                };
                if let Err(refusal) =
                    validate_checkpoint_descriptor(&checkpoint.descriptor, &base.descriptor)
                {
                    return Ok(Err(refusal));
                }
                if base.len() != *base_len {
                    return Ok(Err(CheckpointError::BaseLengthMismatch {
                        extension: checkpoint.descriptor.name.clone(),
                        expected: *base_len,
                        actual: base.len(),
                    }));
                }
                if base.journal.digest != *base_history_digest {
                    return Ok(Err(CheckpointError::BaseHistoryMismatch {
                        extension: checkpoint.descriptor.name.clone(),
                        expected: *base_history_digest,
                        actual: base.journal.digest,
                    }));
                }
                let actual_state_digest = base.content_digest();
                if actual_state_digest != *base_state_digest {
                    return Ok(Err(CheckpointError::BaseDigestMismatch {
                        extension: checkpoint.descriptor.name.clone(),
                        expected: *base_state_digest,
                        actual: actual_state_digest,
                    }));
                }

                // Everything above is a REJECTION ACCELERATOR. Length and both digests
                // can only rule a base out cheaply; passing them establishes nothing,
                // because two unequal histories may agree on any digest and equal
                // digests are not equal values. Base equality is proved here or not at
                // all.
                //
                // Two proofs, in cost order:
                //   * shared structural identity — the presented base and the retained
                //     one are the same journal by construction, which is O(1) and is
                //     the case whenever the caller kept the base it captured from;
                //   * deterministic exact comparison — entry by entry against the
                //     retained handle, which is what lets an independently rebuilt or
                //     sibling base with identical content SUCCEED rather than being
                //     refused for having a different allocation lineage.
                //
                // The comparison is CHARGED, and this is the one place in this function
                // that can produce a non-answer. A stop is not a divergence: reporting
                // "diverged" for a comparison that never finished would manufacture a
                // verdict out of running out of room, which is the defect this whole
                // bead is about.
                let usage = if base.journal.is_same_structure(&retained_base.journal) {
                    // Proved in O(1) and charged nothing, because nothing input-sized
                    // was examined. Recording zero here rather than omitting the fact is
                    // what lets a later double-charge be seen.
                    HistoryProofUsage {
                        kind: HistoryProofKind::SharedStructure,
                        compared_entries: 0,
                        compared_payload_bytes: 0,
                    }
                } else {
                    match bounded_entry_divergence(retained_base, base, proof) {
                        Ok(Some(divergence)) => {
                            return Ok(Err(CheckpointError::BaseNotExact {
                                extension: checkpoint.descriptor.name.clone(),
                                base_len: *base_len,
                                first_divergence: divergence,
                            }));
                        }
                        Ok(None) => HistoryProofUsage {
                            kind: HistoryProofKind::ExactComparison,
                            compared_entries: base.len(),
                            compared_payload_bytes: base.journal.payload_bytes,
                        },
                        Err((dimension, allowed, observed)) => {
                            return Err(proof_stop(dimension, allowed, observed));
                        }
                    }
                };
                Ok(Ok(PreparedExtensionHistory {
                    schema: checkpoint.schema_version,
                    descriptor: checkpoint.descriptor.clone(),
                    limits,
                    usage,
                    material: HistoryMaterial::Suffix {
                        base: base.clone(),
                        suffix: journal.clone(),
                    },
                }))
            }
            CheckpointPayload::FullJournal { journal } => {
                if base.is_some() {
                    return Ok(Err(CheckpointError::UnexpectedBase {
                        extension: checkpoint.descriptor.name.clone(),
                    }));
                }
                Ok(Ok(PreparedExtensionHistory {
                    schema: checkpoint.schema_version,
                    descriptor: checkpoint.descriptor.clone(),
                    limits,
                    // Self-contained: no base, so no base-identity proof and no charge.
                    // The mode difference is a reported fact rather than an implication.
                    usage: HistoryProofUsage {
                        kind: HistoryProofKind::SelfContained,
                        compared_entries: 0,
                        compared_payload_bytes: 0,
                    },
                    material: HistoryMaterial::Full {
                        state: ExtensionState {
                            descriptor: checkpoint.descriptor.clone(),
                            journal: journal.clone(),
                        },
                    },
                }))
            }
        }
    }

    pub fn provenance(&self) -> PayloadProvenance {
        self.descriptor.provenance
    }

    /// Fine-grained invalidation may only see through understood payloads; opaque
    /// ones block conservatively (plan §7.1: honestly blocks, never guessed safe).
    pub fn supports_fine_invalidation(&self) -> bool {
        self.descriptor.provenance == PayloadProvenance::Understood
    }

    /// Merge `ours` and `theirs` (both derived from `self` as the common base)
    /// under the DECLARED semantics. Returns `Err` with the extension name when the
    /// contract says the merge needs review — a typed conflict, never a silent
    /// union.
    pub fn merge(
        base: &ExtensionState,
        ours: &ExtensionState,
        theirs: &ExtensionState,
        set_union_limits: SetUnionLimits,
    ) -> Result<ExtensionMergeOutcome, MergeConflict> {
        validate_descriptor_admission(&base.descriptor, &ours.descriptor, &theirs.descriptor)?;
        let ours_common_prefix = base
            .entries()
            .zip(ours.entries())
            .take_while(|(base_entry, branch_entry)| base_entry == branch_entry)
            .count();
        let theirs_common_prefix = base
            .entries()
            .zip(theirs.entries())
            .take_while(|(base_entry, branch_entry)| base_entry == branch_entry)
            .count();
        if ours_common_prefix != base.len() || theirs_common_prefix != base.len() {
            return Err(MergeConflict::HistoryMismatch {
                extension: base.descriptor.name.clone(),
                base_len: base.len(),
                ours_len: ours.len(),
                theirs_len: theirs.len(),
                ours_common_prefix,
                theirs_common_prefix,
            });
        }
        match base.descriptor.merge {
            MergeSemantics::AppendOrdered => {
                let mut merged = ours.clone();
                for entry in theirs.entries().skip(base.len()) {
                    merged = merged.push_entry(Arc::clone(&entry.payload));
                }
                Ok(ExtensionMergeOutcome::Complete {
                    state: merged,
                    set_union_facts: None,
                })
            }
            MergeSemantics::SetUnion => {
                let raw_entries = ours.len() + (theirs.len() - base.len());
                let raw_payload_bytes = ours.journal.payload_bytes
                    + (theirs.journal.payload_bytes - base.journal.payload_bytes);
                let initial_facts =
                    SetUnionFacts::new(set_union_limits, raw_entries, raw_payload_bytes);
                if let Some((reason, facts)) =
                    set_union_cached_limit_refusal(&base.descriptor.name, initial_facts)
                {
                    return Ok(ExtensionMergeOutcome::Inconclusive { reason, facts });
                }
                if let Some((reason, facts)) = set_union_entry_limit_refusal(
                    &base.descriptor.name,
                    ours.entries().chain(theirs.entries().skip(base.len())),
                    initial_facts,
                ) {
                    return Ok(ExtensionMergeOutcome::Inconclusive { reason, facts });
                }

                let (first, second) = canonical_set_union_branch_order(base, ours, theirs);
                let projection = project_set_union_entries(
                    &base.descriptor.name,
                    first.entries().chain(second.entries().skip(base.len())),
                    raw_entries,
                    raw_payload_bytes,
                    set_union_limits,
                );
                let facts = match projection {
                    SetUnionProjection::Complete { facts, .. } => facts,
                    SetUnionProjection::Inconclusive { reason, facts } => {
                        return Ok(ExtensionMergeOutcome::Inconclusive { reason, facts });
                    }
                };
                let mut merged = first.clone();
                for entry in second.entries().skip(base.len()) {
                    merged = append_set_union_raw_entry(&merged, entry);
                }
                Ok(ExtensionMergeOutcome::Complete {
                    state: merged,
                    set_union_facts: Some(facts),
                })
            }
            MergeSemantics::ConflictsRequireReview => {
                let ours_changed = ours.len() != base.len();
                let theirs_changed = theirs.len() != base.len();
                if ours_changed && theirs_changed {
                    Err(MergeConflict::ConcurrentChanges {
                        extension: base.descriptor.name.clone(),
                    })
                } else if theirs_changed {
                    Ok(ExtensionMergeOutcome::Complete {
                        state: theirs.clone(),
                        set_union_facts: None,
                    })
                } else {
                    Ok(ExtensionMergeOutcome::Complete {
                        state: ours.clone(),
                        set_union_facts: None,
                    })
                }
            }
        }
    }
}

/// Stage 1 of the merge pipeline: bounded descriptor admission.
///
/// # The signature is the enforcement
///
/// The stage law says a descriptor refusal must "inspect zero journal entries, clone
/// zero payloads, select no policy, and expose no product or root". This function takes
/// the three **descriptors** and nothing else, so none of those is reachable: there is
/// no journal to walk, no payload to copy, and the success type is `()`, so no product
/// or root can leave here even by accident.
///
/// That is deliberately a *structural* constraint rather than an assertion. The planted
/// mutant `clone_payloads_during_refusal` — which deep-copied every `ours`/`theirs`
/// payload on this path — survived the entire suite, because the returned conflict is
/// byte-identical and nothing observed the copying. It is now not expressible here at
/// all: `ours.entries()` does not compile when `ours` is an `ExtensionDescriptor`. A
/// constraint cannot rot the way an assertion can be deleted or drift out of scope,
/// which is the failure mode this whole bead is about.
///
/// # What this does NOT establish
///
/// It proves the refusal *cannot* touch a journal or a payload. It does **not** produce
/// the operation/allocation *facts* the criteria separately demand — nothing here counts
/// or reports anything, and the refusal does still clone the three descriptors, which is
/// legitimate and is what the returned conflict is made of. Those are different claims
/// and are tracked separately in `MERGE_VALIDATION_MUTANTS`.
fn validate_descriptor_admission(
    base: &ExtensionDescriptor,
    ours: &ExtensionDescriptor,
    theirs: &ExtensionDescriptor,
) -> Result<(), MergeConflict> {
    if !descriptors_agree(base, ours, theirs) {
        return Err(MergeConflict::DescriptorMismatch {
            base: base.clone(),
            ours: ours.clone(),
            theirs: theirs.clone(),
        });
    }
    Ok(())
}

/// The stage-1 **decision**, parametric in the descriptor type.
///
/// # Parametricity is the enforcement
///
/// The stage law also says a descriptor refusal must "select no policy", and narrowing
/// stage 1 to `&ExtensionDescriptor` did **not** buy that: a descriptor carries `merge`,
/// so `match base.merge { .. }` still type-checks there. That gap was recorded rather
/// than glossed — `refusal_work_facts` reports `policy_selections: None`.
///
/// Here it is closed for the decision. With only `D: Eq` in scope the body cannot reach
/// **any** field of a descriptor, `merge` included: there is no `.merge` to read, because
/// `D` is opaque. Whether a refusal happens is therefore policy-blind by construction,
/// not by inspection and not by an assertion someone can delete.
///
/// Sealing `ExtensionDescriptor::merge` itself would be the total fix, and it is
/// deliberately not taken here: `merge` is a public field with 12 call sites across the
/// crate, so that is a cross-cutting API change rather than a repair to this stage.
///
/// # What this leaves open, stated because the remainder is the point
///
/// The decision is policy-blind. The *conflict construction* in
/// `validate_descriptor_admission` still holds concrete descriptors and could in
/// principle branch on `merge` to build a different conflict. That is a narrower hole
/// than the one this closes, and it is not closed.
fn descriptors_agree<D: Eq>(base: &D, ours: &D, theirs: &D) -> bool {
    base == ours && base == theirs
}

/// Pins the stage-1 signature, because the constraint above is only worth anything for
/// as long as the parameters stay narrow.
///
/// Widening these to `&ExtensionState` — the single edit that would silently restore the
/// ability to clone a payload during refusal, and the obvious "convenience" refactor for
/// someone who wants the journal lengths in a diagnostic — fails to compile *here*, at a
/// site that says why, rather than passing quietly and reopening the hole. Same device as
/// `MERGE_VALIDATION_MUTANTS` holding each killer as a function item rather than a string.
const _DESCRIPTOR_ADMISSION_STAYS_JOURNAL_FREE: fn(
    &ExtensionDescriptor,
    &ExtensionDescriptor,
    &ExtensionDescriptor,
) -> Result<(), MergeConflict> = validate_descriptor_admission;

fn set_union_cached_limit_refusal(
    extension: &Name,
    facts: SetUnionFacts,
) -> Option<(SetUnionInconclusive, SetUnionFacts)> {
    if facts.raw_entries > facts.limits.max_entries {
        return Some((
            SetUnionInconclusive {
                extension: extension.clone(),
                resource: SetUnionResource::Entries,
                limit: facts.limits.max_entries as u128,
                actual: facts.raw_entries as u128,
            },
            facts,
        ));
    }
    if facts.raw_payload_bytes > facts.limits.max_payload_bytes {
        return Some((
            SetUnionInconclusive {
                extension: extension.clone(),
                resource: SetUnionResource::PayloadBytes,
                limit: facts.limits.max_payload_bytes,
                actual: facts.raw_payload_bytes,
            },
            facts,
        ));
    }
    None
}

fn set_union_entry_limit_refusal<'a>(
    extension: &Name,
    entries: impl Iterator<Item = &'a ExtensionEntry>,
    mut facts: SetUnionFacts,
) -> Option<(SetUnionInconclusive, SetUnionFacts)> {
    for entry in entries {
        let entry_bytes = entry.payload.len();
        facts.examined_entries += 1;
        facts.examined_payload_bytes += entry_bytes as u128;
        facts.maximum_entry_bytes = facts.maximum_entry_bytes.max(entry_bytes);
    }
    if facts.maximum_entry_bytes > facts.limits.max_entry_bytes {
        return Some((
            SetUnionInconclusive {
                extension: extension.clone(),
                resource: SetUnionResource::EntryBytes,
                limit: facts.limits.max_entry_bytes as u128,
                actual: facts.maximum_entry_bytes as u128,
            },
            facts,
        ));
    }
    None
}

fn project_set_union_entries<'a>(
    extension: &Name,
    entries: impl Iterator<Item = &'a ExtensionEntry>,
    raw_entries: usize,
    raw_payload_bytes: u128,
    limits: SetUnionLimits,
) -> SetUnionProjection<'a> {
    let mut facts = SetUnionFacts::new(limits, raw_entries, raw_payload_bytes);
    if let Some((reason, facts)) = set_union_cached_limit_refusal(extension, facts) {
        return SetUnionProjection::Inconclusive { reason, facts };
    }

    let mut semantic = Vec::new();
    let mut seen = BTreeSet::<&'a [u8]>::new();
    for entry in entries {
        let entry_bytes = entry.payload.len();
        facts.examined_entries += 1;
        facts.examined_payload_bytes += entry_bytes as u128;
        facts.maximum_entry_bytes = facts.maximum_entry_bytes.max(entry_bytes);
        if entry_bytes > limits.max_entry_bytes {
            return SetUnionProjection::Inconclusive {
                reason: SetUnionInconclusive {
                    extension: extension.clone(),
                    resource: SetUnionResource::EntryBytes,
                    limit: limits.max_entry_bytes as u128,
                    actual: entry_bytes as u128,
                },
                facts,
            };
        }
        if seen.insert(entry.payload.as_ref()) {
            semantic.push(entry);
            facts.semantic_entries += 1;
        } else {
            facts.duplicate_entries += 1;
        }
    }
    debug_assert_eq!(facts.examined_entries, raw_entries);
    debug_assert_eq!(facts.examined_payload_bytes, raw_payload_bytes);
    SetUnionProjection::Complete {
        entries: semantic,
        facts,
    }
}

fn canonical_set_union_branch_order<'a>(
    base: &ExtensionState,
    ours: &'a ExtensionState,
    theirs: &'a ExtensionState,
) -> (&'a ExtensionState, &'a ExtensionState) {
    let order = ours
        .entries()
        .skip(base.len())
        .map(|entry| entry.payload.as_ref())
        .cmp(
            theirs
                .entries()
                .skip(base.len())
                .map(|entry| entry.payload.as_ref()),
        );
    match order {
        Ordering::Less | Ordering::Equal => (ours, theirs),
        Ordering::Greater => (theirs, ours),
    }
}

fn append_set_union_raw_entry(merged: &ExtensionState, entry: &ExtensionEntry) -> ExtensionState {
    merged.push_entry(Arc::clone(&entry.payload)) // FLN_SET_UNION_RAW_APPEND
}

fn validate_checkpoint_descriptor(
    expected: &ExtensionDescriptor,
    actual: &ExtensionDescriptor,
) -> Result<(), CheckpointError> {
    if expected.name != actual.name {
        return Err(CheckpointError::ExtensionNameMismatch {
            expected: expected.name.clone(),
            actual: actual.name.clone(),
        });
    }
    if expected != actual {
        return Err(CheckpointError::ContractMismatch {
            expected: expected.clone(),
            actual: actual.clone(),
        });
    }
    Ok(())
}

fn history_mismatch(base: &ExtensionState, target: &ExtensionState) -> CheckpointError {
    let common_prefix = base
        .entries()
        .zip(target.entries())
        .take_while(|(base_entry, target_entry)| base_entry == target_entry)
        .count();
    CheckpointError::HistoryMismatch {
        extension: target.descriptor.name.clone(),
        base_len: base.len(),
        target_len: target.len(),
        common_prefix,
    }
}

fn enforce_checkpoint_limits(
    extension: &Name,
    entries: usize,
    payload_bytes: u128,
    limits: CheckpointLimits,
) -> Result<(), CheckpointError> {
    if entries > limits.max_entries {
        return Err(CheckpointError::ResourceLimitExceeded {
            extension: extension.clone(),
            resource: CheckpointResource::Entries,
            limit: limits.max_entries as u128,
            actual: entries as u128,
        });
    }
    if payload_bytes > limits.max_payload_bytes {
        return Err(CheckpointError::ResourceLimitExceeded {
            extension: extension.clone(),
            resource: CheckpointResource::PayloadBytes,
            limit: limits.max_payload_bytes,
            actual: payload_bytes,
        });
    }
    Ok(())
}

/// A typed semantic-merge conflict (plan §15.3b: blocked and explained, the failure
/// mode Git cannot even see).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MergeConflict {
    DescriptorMismatch {
        base: ExtensionDescriptor,
        ours: ExtensionDescriptor,
        theirs: ExtensionDescriptor,
    },
    ConcurrentChanges {
        extension: Name,
    },
    HistoryMismatch {
        extension: Name,
        base_len: usize,
        ours_len: usize,
        theirs_len: usize,
        ours_common_prefix: usize,
        theirs_common_prefix: usize,
    },
}

impl std::fmt::Display for MergeConflict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MergeConflict::DescriptorMismatch { base, ours, theirs } => write!(
                f,
                "extension contracts differ: base=`{}`/{:?}/{:?}/{:?}, ours=`{}`/{:?}/{:?}/{:?}, theirs=`{}`/{:?}/{:?}/{:?}",
                base.name.to_display_string(),
                base.merge,
                base.checkpoint,
                base.provenance,
                ours.name.to_display_string(),
                ours.merge,
                ours.checkpoint,
                ours.provenance,
                theirs.name.to_display_string(),
                theirs.merge,
                theirs.checkpoint,
                theirs.provenance,
            ),
            MergeConflict::ConcurrentChanges { extension } => write!(
                f,
                "extension `{}` declares conflicts-require-review merge semantics and both branches changed it",
                extension.to_display_string()
            ),
            MergeConflict::HistoryMismatch {
                extension,
                base_len,
                ours_len,
                theirs_len,
                ours_common_prefix,
                theirs_common_prefix,
            } => write!(
                f,
                "extension `{}` branches do not descend from the supplied base: base_len={base_len}, ours_len={ours_len}, theirs_len={theirs_len}, ours_common_prefix={ours_common_prefix}, theirs_common_prefix={theirs_common_prefix}",
                extension.to_display_string()
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::environment::Environment;
    use fln_core::options::KVMap;
    use fln_core::outcome::{Authority, CacheAdmission, InconclusiveCause};
    use std::collections::HashSet;
    use std::time::Instant;

    /// **The field-boundary law for entry identity**, pinned as a property rather than
    /// left as a consequence of the encoder happening to be right.
    ///
    /// `ExtensionEntryId::derive` binds an epoch tag, an epoch commit, a descriptor name,
    /// three enum tags and a payload into ONE digest. Every such preimage is exposed to
    /// the same failure, and this project has now hit it twice in other places:
    /// `franken_lean-f6br`'s census witness and the intern key fixed in `bf9ef450`, both
    /// through `Name::to_display_string`, which joins components with `.` without
    /// escaping and renders a numeric component identically to a string one.
    ///
    /// The general shape behind all three: **a serialization is injective only if every
    /// variable-length field is self-delimiting and every sum type carries its tag.**
    /// Concatenate two variable-length fields without a length and the boundary between
    /// them stops being recoverable, so two different inputs produce the same bytes.
    ///
    /// This id is correct today because `CanonWriter` length-prefixes every string and
    /// byte run. That is a property of the ENCODER, not of this call site, so a future
    /// hand-rolled preimage here — which is exactly what `intern.rs` had — would
    /// reintroduce it silently. These cases fail if the boundary is ever lost.
    ///
    /// Note the asymmetry with the two earlier instances, because it decides urgency: an
    /// id collision here cannot forge a restore on its own, since a suffix restore proves
    /// its base by exact comparison and a FullJournal carries its own entries. This is a
    /// defence-in-depth binding, not the sole gate. It is pinned anyway — the bead's
    /// contract is that identity is exact under collisions, and "another check would
    /// probably catch it" is not exactness.
    #[test]
    fn entry_identity_survives_the_field_boundary_attack() {
        let payload: &[u8] = b"x";
        let desc = descriptor(MergeSemantics::AppendOrdered, PayloadProvenance::Understood);

        // 1. EPOCH TAG / COMMIT boundary. Two epochs whose concatenation is identical.
        //    Without a length prefix, ("ab","c") and ("a","bc") are the same bytes.
        let split_left = ModuleEpoch::new("ab", "c");
        let split_right = ModuleEpoch::new("a", "bc");
        assert_ne!(
            ExtensionEntryId::derive(&split_left, &desc, payload),
            ExtensionEntryId::derive(&split_right, &desc, payload),
            "the epoch tag/commit boundary must be recoverable: an unlength-prefixed \
             concatenation makes these two epochs the same preimage"
        );

        // 2. DESCRIPTOR NAME structure. Two components `a`,`b` versus one component
        //    literally spelled `a.b` — the exact f6br collision, which reaches this
        //    digest through the descriptor rather than through a declaration name.
        let nested = ExtensionDescriptor {
            name: Name::str(Name::str(Name::anonymous(), "a"), "b"),
            ..desc.clone()
        };
        let flat = ExtensionDescriptor {
            name: Name::str(Name::anonymous(), "a.b"),
            ..desc.clone()
        };
        assert_eq!(
            nested.name.to_display_string(),
            flat.name.to_display_string(),
            "premise: the display forms must actually collide, or this case proves nothing"
        );
        assert_ne!(
            ExtensionEntryId::derive(&fixture_epoch(), &nested, payload),
            ExtensionEntryId::derive(&fixture_epoch(), &flat, payload),
            "a descriptor component containing the display separator must not forge a \
             deeper path"
        );

        // 3. NAME / PAYLOAD boundary. The name's last component and the payload are
        //    adjacent variable-length fields, so they are a boundary too.
        let long_name = ExtensionDescriptor {
            name: Name::str(Name::anonymous(), "ex"),
            ..desc.clone()
        };
        let short_name = ExtensionDescriptor {
            name: Name::str(Name::anonymous(), "e"),
            ..desc.clone()
        };
        assert_ne!(
            ExtensionEntryId::derive(&fixture_epoch(), &long_name, b"t"),
            ExtensionEntryId::derive(&fixture_epoch(), &short_name, b"xt"),
            "the descriptor-name/payload boundary must be recoverable"
        );

        // 4. SUM TYPES carry their tags: the three descriptor semantics are part of
        //    identity, so two descriptors differing only in one must not collide.
        let other_merge = ExtensionDescriptor {
            merge: MergeSemantics::SetUnion,
            ..desc.clone()
        };
        assert_ne!(
            ExtensionEntryId::derive(&fixture_epoch(), &desc, payload),
            ExtensionEntryId::derive(&fixture_epoch(), &other_merge, payload),
            "declared merge semantics are part of entry identity"
        );
    }

    fn descriptor(merge: MergeSemantics, provenance: PayloadProvenance) -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: Name::str(Name::anonymous(), "simpExt"),
            merge,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance,
        }
    }

    #[derive(Debug, Clone, Copy)]
    struct DescriptorIdentityCase {
        merge: MergeSemantics,
        checkpoint: CheckpointSemantics,
        provenance: PayloadProvenance,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum DescriptorDigestModel {
        Canonical,
        OmitMerge,
        OmitCheckpoint,
        OmitProvenance,
        SwapMergeTagValues,
        SwapMergeAndCheckpointFields,
        DebugText,
        DescriptorAfterJournal,
    }

    /// Successor chains over every descriptor dimension that reaches
    /// `Domain::ExtensionDelta`.
    ///
    /// The tag matches already force a new `MergeSemantics`, `CheckpointSemantics`
    /// or `PayloadProvenance` variant to be *tagged*. These force it to be
    /// *covered*: the combination matrix used to be three hand-written literal
    /// arrays, so a new variant satisfied every exhaustive match and then quietly
    /// stayed out of the 3x2x2 classification, the mutant matrix and the E2E
    /// producer — tagged but untested identity. Rust has no enum reflection, so the
    /// forcing function has to be an exhaustive match that *generates* the matrix.
    /// Adding a variant fails to compile here until it joins a chain, and the chains
    /// are what build the matrix, so tagging and covering are one edit. This is the
    /// same convention `fln-amv.12` established for declaration tags rather than a
    /// second scheme.
    const fn succ_merge_semantics(semantics: MergeSemantics) -> Option<MergeSemantics> {
        match semantics {
            MergeSemantics::AppendOrdered => Some(MergeSemantics::SetUnion),
            MergeSemantics::SetUnion => Some(MergeSemantics::ConflictsRequireReview),
            MergeSemantics::ConflictsRequireReview => None,
        }
    }

    const fn succ_checkpoint_semantics(
        semantics: CheckpointSemantics,
    ) -> Option<CheckpointSemantics> {
        match semantics {
            CheckpointSemantics::JournalSuffix => Some(CheckpointSemantics::FullJournal),
            CheckpointSemantics::FullJournal => None,
        }
    }

    const fn succ_payload_provenance(provenance: PayloadProvenance) -> Option<PayloadProvenance> {
        match provenance {
            PayloadProvenance::Understood => Some(PayloadProvenance::Opaque),
            PayloadProvenance::Opaque => None,
        }
    }

    const FIRST_MERGE_SEMANTICS: MergeSemantics = MergeSemantics::AppendOrdered;
    const FIRST_CHECKPOINT_SEMANTICS: CheckpointSemantics = CheckpointSemantics::JournalSuffix;
    const FIRST_PAYLOAD_PROVENANCE: PayloadProvenance = PayloadProvenance::Understood;

    /// Frozen per-dimension variant counts and the frozen product. Lengthening a
    /// chain without bumping these fails const evaluation of the generator, and
    /// shortening one fails it too — that is the single way to satisfy an exhaustive
    /// match while orphaning a variant, so the count is checked in both directions
    /// rather than as an upper bound. `scripts/evidence.py` pins the same 12 for the
    /// `fln.e2e.extension-descriptor-matrix` bundle; the two move together.
    const MERGE_SEMANTICS_VARIANTS: usize = 3;
    const CHECKPOINT_SEMANTICS_VARIANTS: usize = 2;
    const PAYLOAD_PROVENANCE_VARIANTS: usize = 2;
    const DESCRIPTOR_COMBINATION_COUNT: usize =
        MERGE_SEMANTICS_VARIANTS * CHECKPOINT_SEMANTICS_VARIANTS * PAYLOAD_PROVENANCE_VARIANTS;

    const DESCRIPTOR_IDENTITY_CASES: [DescriptorIdentityCase; DESCRIPTOR_COMBINATION_COUNT] =
        derive_descriptor_identity_cases();

    const fn derive_descriptor_identity_cases()
    -> [DescriptorIdentityCase; DESCRIPTOR_COMBINATION_COUNT] {
        let mut cases = [DescriptorIdentityCase {
            merge: FIRST_MERGE_SEMANTICS,
            checkpoint: FIRST_CHECKPOINT_SEMANTICS,
            provenance: FIRST_PAYLOAD_PROVENANCE,
        }; DESCRIPTOR_COMBINATION_COUNT];
        let mut filled = 0;
        // Merge outermost, provenance innermost: the same order the hand-written
        // loops produced, so no golden, record order or frozen count moves.
        let mut merge = Some(FIRST_MERGE_SEMANTICS);
        while let Some(current_merge) = merge {
            let mut checkpoint = Some(FIRST_CHECKPOINT_SEMANTICS);
            while let Some(current_checkpoint) = checkpoint {
                let mut provenance = Some(FIRST_PAYLOAD_PROVENANCE);
                while let Some(current_provenance) = provenance {
                    // A chain that is too long, or one that cycles, is caught here
                    // rather than by writing past the end of the array.
                    assert!(
                        filled < DESCRIPTOR_COMBINATION_COUNT,
                        "descriptor successor chains yield more combinations than DESCRIPTOR_COMBINATION_COUNT"
                    );
                    cases[filled] = DescriptorIdentityCase {
                        merge: current_merge,
                        checkpoint: current_checkpoint,
                        provenance: current_provenance,
                    };
                    filled += 1;
                    provenance = succ_payload_provenance(current_provenance);
                }
                checkpoint = succ_checkpoint_semantics(current_checkpoint);
            }
            merge = succ_merge_semantics(current_merge);
        }
        assert!(
            filled == DESCRIPTOR_COMBINATION_COUNT,
            "descriptor successor chains yield fewer combinations than DESCRIPTOR_COMBINATION_COUNT: a variant is orphaned"
        );
        cases
    }

    fn descriptor_identity_cases() -> Vec<DescriptorIdentityCase> {
        DESCRIPTOR_IDENTITY_CASES.to_vec()
    }

    const fn modeled_merge_tag(semantics: MergeSemantics) -> u8 {
        match semantics {
            MergeSemantics::AppendOrdered => 0,
            MergeSemantics::SetUnion => 1,
            MergeSemantics::ConflictsRequireReview => 2,
        }
    }

    const fn modeled_checkpoint_tag(semantics: CheckpointSemantics) -> u8 {
        match semantics {
            CheckpointSemantics::JournalSuffix => 0,
            CheckpointSemantics::FullJournal => 1,
        }
    }

    const fn modeled_provenance_tag(provenance: PayloadProvenance) -> u8 {
        match provenance {
            PayloadProvenance::Understood => 0,
            PayloadProvenance::Opaque => 1,
        }
    }

    const fn merge_label(semantics: MergeSemantics) -> &'static str {
        match semantics {
            MergeSemantics::AppendOrdered => "append_ordered",
            MergeSemantics::SetUnion => "set_union",
            MergeSemantics::ConflictsRequireReview => "conflicts_require_review",
        }
    }

    const fn checkpoint_label(semantics: CheckpointSemantics) -> &'static str {
        match semantics {
            CheckpointSemantics::JournalSuffix => "journal_suffix",
            CheckpointSemantics::FullJournal => "full_journal",
        }
    }

    const fn provenance_label(provenance: PayloadProvenance) -> &'static str {
        match provenance {
            PayloadProvenance::Understood => "understood",
            PayloadProvenance::Opaque => "opaque",
        }
    }

    fn identity_descriptor(case: DescriptorIdentityCase, unique_name: bool) -> ExtensionDescriptor {
        let name = if unique_name {
            format!(
                "identityExt.{}.{}.{}",
                merge_label(case.merge),
                checkpoint_label(case.checkpoint),
                provenance_label(case.provenance)
            )
        } else {
            "identityExt".to_owned()
        };
        ExtensionDescriptor {
            name: Name::str(Name::anonymous(), name),
            merge: case.merge,
            checkpoint: case.checkpoint,
            provenance: case.provenance,
        }
    }

    fn write_modeled_descriptor(
        w: &mut CanonWriter,
        descriptor: &ExtensionDescriptor,
        model: DescriptorDigestModel,
    ) {
        descriptor.name.write_body(w);
        match model {
            DescriptorDigestModel::Canonical | DescriptorDigestModel::DescriptorAfterJournal => {
                w.u8(modeled_merge_tag(descriptor.merge));
                w.u8(modeled_checkpoint_tag(descriptor.checkpoint));
                w.u8(modeled_provenance_tag(descriptor.provenance));
            }
            DescriptorDigestModel::OmitMerge => {
                w.u8(modeled_checkpoint_tag(descriptor.checkpoint));
                w.u8(modeled_provenance_tag(descriptor.provenance));
            }
            DescriptorDigestModel::OmitCheckpoint => {
                w.u8(modeled_merge_tag(descriptor.merge));
                w.u8(modeled_provenance_tag(descriptor.provenance));
            }
            DescriptorDigestModel::OmitProvenance => {
                w.u8(modeled_merge_tag(descriptor.merge));
                w.u8(modeled_checkpoint_tag(descriptor.checkpoint));
            }
            DescriptorDigestModel::SwapMergeTagValues => {
                let merge = match descriptor.merge {
                    MergeSemantics::AppendOrdered => 1,
                    MergeSemantics::SetUnion => 0,
                    MergeSemantics::ConflictsRequireReview => 2,
                };
                w.u8(merge);
                w.u8(modeled_checkpoint_tag(descriptor.checkpoint));
                w.u8(modeled_provenance_tag(descriptor.provenance));
            }
            DescriptorDigestModel::SwapMergeAndCheckpointFields => {
                w.u8(modeled_checkpoint_tag(descriptor.checkpoint));
                w.u8(modeled_merge_tag(descriptor.merge));
                w.u8(modeled_provenance_tag(descriptor.provenance));
            }
            DescriptorDigestModel::DebugText => {
                w.str(&format!("{:?}", descriptor.merge));
                w.str(&format!("{:?}", descriptor.checkpoint));
                w.str(&format!("{:?}", descriptor.provenance));
            }
        }
    }

    fn write_modeled_journal_identity(w: &mut CanonWriter, state: &ExtensionState) {
        w.u64(state.journal.len as u64);
        w.bytes(&state.journal.digest.0);
    }

    /// Control-flow-independent model of the descriptor/journal layout. Primitive
    /// canonical codecs and the registered extension domain are intentionally shared.
    fn modeled_extension_content_digest(
        state: &ExtensionState,
        model: DescriptorDigestModel,
    ) -> Digest {
        let mut w = CanonWriter::new();
        w.str("fln.extension-state");
        w.u16(1);
        if model == DescriptorDigestModel::DescriptorAfterJournal {
            write_modeled_journal_identity(&mut w, state);
            write_modeled_descriptor(&mut w, &state.descriptor, model);
        } else {
            write_modeled_descriptor(&mut w, &state.descriptor, model);
            write_modeled_journal_identity(&mut w, state);
        }
        hash(Domain::ExtensionDelta, &w.into_bytes())
    }

    fn identity_state(case: DescriptorIdentityCase, unique_name: bool) -> ExtensionState {
        ExtensionState::new(identity_descriptor(case, unique_name))
            .push_entry(bytes(b"alpha"))
            .push_entry(bytes(b"beta"))
    }

    #[derive(Debug, Clone, Copy)]
    enum IdentityJournalOrder {
        AlphaThenBeta,
        BetaThenAlpha,
    }

    fn identity_environment_with_journal(
        cases: impl IntoIterator<Item = DescriptorIdentityCase>,
        journal_order: IdentityJournalOrder,
    ) -> Environment {
        let entries: [&[u8]; 2] = match journal_order {
            IdentityJournalOrder::AlphaThenBeta => [b"alpha".as_slice(), b"beta".as_slice()],
            IdentityJournalOrder::BetaThenAlpha => [b"beta".as_slice(), b"alpha".as_slice()],
        };
        let mut environment = Environment::new();
        for case in cases {
            let descriptor = identity_descriptor(case, true);
            let name = descriptor.name.clone();
            environment = environment
                .register_extension(descriptor)
                .expect("identity fixture environment builds");
            for entry in entries {
                environment = environment
                    .push_extension_entry(&name, bytes(entry))
                    .expect("identity fixture journal entry appends");
            }
        }
        environment
    }

    fn identity_environment(
        cases: impl IntoIterator<Item = DescriptorIdentityCase>,
    ) -> Environment {
        identity_environment_with_journal(cases, IdentityJournalOrder::AlphaThenBeta)
    }

    fn permuted_descriptor_cases(
        cases: &[DescriptorIdentityCase],
        worker_index: usize,
    ) -> Vec<DescriptorIdentityCase> {
        let steps = [1usize, 5, 7, 11];
        let start = worker_index % cases.len();
        let step = steps[(worker_index / cases.len()) % steps.len()];
        (0..cases.len())
            .map(|offset| cases[(start + offset * step) % cases.len()])
            .collect()
    }

    fn descriptor_order_id(cases: &[DescriptorIdentityCase]) -> Digest {
        let mut w = CanonWriter::new();
        w.str("fln.test.extension-descriptor-order");
        w.u16(1);
        w.u64(cases.len() as u64);
        for case in cases {
            w.str(merge_label(case.merge));
            w.str(checkpoint_label(case.checkpoint));
            w.str(provenance_label(case.provenance));
        }
        hash(Domain::Fixture, &w.into_bytes())
    }

    fn bytes(v: &[u8]) -> Arc<[u8]> {
        Arc::from(v.to_vec().into_boxed_slice())
    }

    /// Fold a checkpoint outcome to the `Result` these fixtures expect.
    ///
    /// Every fixture passes no cancellation probe, so a non-answer here is a test bug
    /// rather than a scenario — surfaced as one instead of silently becoming an `Err`,
    /// which is the collapse the widened signature exists to prevent.
    fn completed<T: std::fmt::Debug, E: std::fmt::Debug>(
        outcome: Outcome<Result<T, E>>,
    ) -> Result<T, E> {
        assert!(
            matches!(outcome, Outcome::Complete(_)),
            "fixtures pass no probe, so a non-answer is a test bug: {outcome:?}"
        );
        match outcome {
            Outcome::Complete(result) => result,
            _ => unreachable!("asserted just above"),
        }
    }

    fn merge_with_test_limits(
        base: &ExtensionState,
        ours: &ExtensionState,
        theirs: &ExtensionState,
    ) -> Result<ExtensionState, MergeConflict> {
        Ok(
            match ExtensionState::merge(base, ours, theirs, TEST_SET_UNION_LIMITS)? {
                ExtensionMergeOutcome::Complete { state, .. } => Some(state),
                ExtensionMergeOutcome::Inconclusive { .. } => None,
            }
            .expect("generous test limits must not be exhausted"),
        )
    }

    fn raw_payloads(state: &ExtensionState) -> Vec<Vec<u8>> {
        state
            .entries()
            .map(|entry| entry.payload.to_vec())
            .collect()
    }

    fn semantic_payloads(state: &ExtensionState) -> Vec<Vec<u8>> {
        match state.semantic_projection(TEST_SET_UNION_LIMITS) {
            SetUnionProjection::Complete { entries, .. } => Some(entries),
            SetUnionProjection::Inconclusive { .. } => None,
        }
        .expect("generous test limits must not be exhausted")
        .into_iter()
        .map(|entry| entry.payload.to_vec())
        .collect()
    }

    fn semantic_len(state: &ExtensionState) -> usize {
        match state.semantic_projection(TEST_SET_UNION_LIMITS) {
            SetUnionProjection::Complete { entries, .. } => Some(entries.len()),
            SetUnionProjection::Inconclusive { .. } => None,
        }
        .expect("generous test limits must not be exhausted")
    }

    fn stable_unique_model(raw: &[Vec<u8>]) -> Vec<Vec<u8>> {
        let mut unique = Vec::new();
        for payload in raw {
            if !unique.contains(payload) {
                unique.push(payload.clone());
            }
        }
        unique
    }

    fn canonical_set_union_raw_model(
        base: &[Vec<u8>],
        ours_suffix: &[Vec<u8>],
        theirs_suffix: &[Vec<u8>],
    ) -> Vec<Vec<u8>> {
        let (first, second) = if ours_suffix <= theirs_suffix {
            (ours_suffix, theirs_suffix)
        } else {
            (theirs_suffix, ours_suffix)
        };
        let mut raw = base.to_vec();
        raw.extend_from_slice(first);
        raw.extend_from_slice(second);
        raw
    }

    fn numbered_state(count: usize) -> ExtensionState {
        let mut state = ExtensionState::new(descriptor(
            MergeSemantics::AppendOrdered,
            PayloadProvenance::Understood,
        ));
        for index in 0..count {
            state = state.push_entry(bytes(&(index as u64).to_le_bytes()));
        }
        state
    }

    fn descriptor_with_checkpoint(checkpoint: CheckpointSemantics) -> ExtensionDescriptor {
        ExtensionDescriptor {
            checkpoint,
            ..descriptor(MergeSemantics::AppendOrdered, PayloadProvenance::Understood)
        }
    }

    fn state_with_checkpoint(count: usize, checkpoint: CheckpointSemantics) -> ExtensionState {
        let mut state = ExtensionState::new(descriptor_with_checkpoint(checkpoint));
        for index in 0..count {
            state = state.push_entry(bytes(&(index as u64).to_le_bytes()));
        }
        state
    }

    const TEST_LIMITS: CheckpointLimits = CheckpointLimits::new(200_000, u128::MAX);
    const TEST_SET_UNION_LIMITS: SetUnionLimits =
        SetUnionLimits::new(200_000, u128::MAX, usize::MAX);

    fn evidence_order_hash<'a>(payloads: impl IntoIterator<Item = &'a [u8]>) -> u64 {
        let mut hash = 0xcbf2_9ce4_8422_2325u64;
        for payload in payloads {
            for byte in (payload.len() as u64).to_le_bytes().iter().chain(payload) {
                hash ^= u64::from(*byte);
                hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
            }
        }
        hash
    }

    fn journal_shape(journal: &ExtensionJournal) -> (usize, usize) {
        fn visit(node: &JournalNode, node_count: &mut usize, leaf_count: &mut usize) {
            *node_count += 1;
            match node {
                JournalNode::Branch { children } => {
                    for child in children {
                        visit(child, node_count, leaf_count);
                    }
                }
                JournalNode::Leaf { .. } => *leaf_count += 1,
            }
        }

        let mut node_count = 0;
        let mut leaf_count = 0;
        if let Some(root) = journal.root.as_deref() {
            visit(root, &mut node_count, &mut leaf_count);
        }
        (node_count, leaf_count)
    }

    fn checkpoint_evidence_id(checkpoint: &ExtensionCheckpoint) -> String {
        let order_hash =
            evidence_order_hash(checkpoint.entries().map(|entry| entry.payload.as_ref()));
        let mode = match checkpoint.mode() {
            CheckpointSemantics::JournalSuffix => "suffix",
            CheckpointSemantics::FullJournal => "full",
        };
        format!(
            "v{}-{mode}-{}-{order_hash:016x}",
            checkpoint.schema_version(),
            checkpoint.captured_entries()
        )
    }

    #[test]
    fn descriptor_identity_tags_are_explicit_and_exhaustive() {
        assert_eq!(merge_semantics_tag(MergeSemantics::AppendOrdered), 0);
        assert_eq!(merge_semantics_tag(MergeSemantics::SetUnion), 1);
        assert_eq!(
            merge_semantics_tag(MergeSemantics::ConflictsRequireReview),
            2
        );
        assert_eq!(
            checkpoint_semantics_tag(CheckpointSemantics::JournalSuffix),
            0
        );
        assert_eq!(
            checkpoint_semantics_tag(CheckpointSemantics::FullJournal),
            1
        );
        assert_eq!(payload_provenance_tag(PayloadProvenance::Understood), 0);
        assert_eq!(payload_provenance_tag(PayloadProvenance::Opaque), 1);
    }

    /// The coverage half of the `fln-amv.2` guard, and the same discipline
    /// `fln-amv.12` uses for declaration tags rather than a second scheme.
    ///
    /// The tag matches force a new descriptor variant to be *tagged*; the successor
    /// chains force it to be *covered*, and this proves the chains actually generate
    /// the 3x2x2 matrix that the classification, the named mutants and the E2E
    /// producer all iterate.
    #[test]
    fn descriptor_identity_matrix_is_generated_by_exhaustive_succ_chains() {
        // Walk each dimension independently of the generated matrix, so it is checked
        // against the chains rather than against itself.
        let mut merge_chain: Vec<MergeSemantics> = Vec::new();
        let mut merge = Some(FIRST_MERGE_SEMANTICS);
        while let Some(current) = merge {
            assert!(
                !merge_chain.contains(&current),
                "the MergeSemantics successor chain revisits {current:?}, which would \
                 silently drop every variant after the cycle"
            );
            merge_chain.push(current);
            merge = succ_merge_semantics(current);
        }
        let mut checkpoint_chain: Vec<CheckpointSemantics> = Vec::new();
        let mut checkpoint = Some(FIRST_CHECKPOINT_SEMANTICS);
        while let Some(current) = checkpoint {
            assert!(
                !checkpoint_chain.contains(&current),
                "the CheckpointSemantics successor chain revisits {current:?}"
            );
            checkpoint_chain.push(current);
            checkpoint = succ_checkpoint_semantics(current);
        }
        let mut provenance_chain: Vec<PayloadProvenance> = Vec::new();
        let mut provenance = Some(FIRST_PAYLOAD_PROVENANCE);
        while let Some(current) = provenance {
            assert!(
                !provenance_chain.contains(&current),
                "the PayloadProvenance successor chain revisits {current:?}"
            );
            provenance_chain.push(current);
            provenance = succ_payload_provenance(current);
        }
        assert_eq!(
            merge_chain.as_slice(),
            [
                MergeSemantics::AppendOrdered,
                MergeSemantics::SetUnion,
                MergeSemantics::ConflictsRequireReview,
            ]
            .as_slice(),
            "the MergeSemantics chain no longer enumerates every variant"
        );
        assert_eq!(
            checkpoint_chain.as_slice(),
            [
                CheckpointSemantics::JournalSuffix,
                CheckpointSemantics::FullJournal,
            ]
            .as_slice(),
            "the CheckpointSemantics chain no longer enumerates every variant"
        );
        assert_eq!(
            provenance_chain.as_slice(),
            [PayloadProvenance::Understood, PayloadProvenance::Opaque].as_slice(),
            "the PayloadProvenance chain no longer enumerates every variant"
        );
        assert_eq!(merge_chain.len(), MERGE_SEMANTICS_VARIANTS);
        assert_eq!(checkpoint_chain.len(), CHECKPOINT_SEMANTICS_VARIANTS);
        assert_eq!(provenance_chain.len(), PAYLOAD_PROVENANCE_VARIANTS);

        // Exact equality against the independently built product, which is the
        // both-directions assertion: every combination of chain members reaches the
        // matrix, and the matrix holds nothing that is not such a combination. Either
        // direction alone would accept a matrix that quietly dropped or invented one.
        let mut expected = Vec::with_capacity(DESCRIPTOR_COMBINATION_COUNT);
        for merge in merge_chain.iter().copied() {
            for checkpoint in checkpoint_chain.iter().copied() {
                for provenance in provenance_chain.iter().copied() {
                    expected.push((merge, checkpoint, provenance));
                }
            }
        }
        let observed: Vec<_> = descriptor_identity_cases()
            .into_iter()
            .map(|case| (case.merge, case.checkpoint, case.provenance))
            .collect();
        assert_eq!(
            observed.as_slice(),
            expected.as_slice(),
            "the generated descriptor matrix diverged from the successor chains"
        );
        assert_eq!(observed.len(), DESCRIPTOR_COMBINATION_COUNT);
        assert_eq!(DESCRIPTOR_COMBINATION_COUNT, 12);

        // Tags must be pairwise distinct within a dimension, and deliberately *not*
        // dense: retiring a variant should retire its tag forever rather than force a
        // renumbering, and silent renumbering is exactly what this bead forbids.
        let merge_tags: Vec<u8> = merge_chain
            .iter()
            .copied()
            .map(merge_semantics_tag)
            .collect();
        let checkpoint_tags: Vec<u8> = checkpoint_chain
            .iter()
            .copied()
            .map(checkpoint_semantics_tag)
            .collect();
        let provenance_tags: Vec<u8> = provenance_chain
            .iter()
            .copied()
            .map(payload_provenance_tag)
            .collect();
        for (dimension, tags) in [
            ("merge", &merge_tags),
            ("checkpoint", &checkpoint_tags),
            ("provenance", &provenance_tags),
        ] {
            let distinct: HashSet<u8> = tags.iter().copied().collect();
            assert_eq!(
                distinct.len(),
                tags.len(),
                "two {dimension} variants share a tag, so descriptors that differ \
                 collide on one identity"
            );
        }

        // The frozen mutant counts are pinned to the matrix size, so growing a
        // dimension cannot leave a stale expectation passing on a subset.
        assert_eq!(
            DESCRIPTOR_COMBINATION_COUNT * 5,
            60,
            "the frozen 60 universal mutant discriminations no longer match the matrix"
        );

        eprintln!(
            "{{\"schema\":\"fln.unit.extension-descriptor-coverage\",\"version\":1,\
             \"bead\":\"fln-amv.2\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"generated-descriptor-combination-matrix\",\
             \"claim_scope\":\"descriptor_combination_coverage_only\",\
             \"matrix_source\":\"generated_from_exhaustive_succ_chains\",\
             \"convention\":\"shared-with-fln-amv.12\",\
             \"guard_kind\":\"compile_time_and_const_eval\",\
             \"added_variant_outcome\":\"compile_error\",\
             \"source_reorder_outcome\":\"no_root_change\",\
             \"retagged_variant_outcome\":\"root_relation_failure\",\
             \"shortened_chain_outcome\":\"const_eval_assert\",\
             \"merge_chain_length\":{},\"checkpoint_chain_length\":{},\
             \"provenance_chain_length\":{},\
             \"generated_combination_count\":{},\"frozen_combination_count\":{},\
             \"tag_density_asserted\":false,\
             \"tag_pairwise_distinct_within_dimension\":true,\
             \"status\":\"pass\"}}",
            merge_chain.len(),
            checkpoint_chain.len(),
            provenance_chain.len(),
            observed.len(),
            DESCRIPTOR_COMBINATION_COUNT
        );
    }

    #[test]
    fn descriptor_identity_matrix_matches_model_and_logical_roots() {
        let cases = descriptor_identity_cases();
        assert_eq!(cases.len(), 12, "the complete 3×2×2 matrix is required");
        let options = KVMap::new();
        let mut digests = HashSet::with_capacity(cases.len());
        let mut roots = HashSet::with_capacity(cases.len());

        for case in cases {
            let state = identity_state(case, false);
            let actual_digest = state.content_digest();
            let modeled_digest =
                modeled_extension_content_digest(&state, DescriptorDigestModel::Canonical);
            assert_eq!(
                actual_digest, modeled_digest,
                "descriptor identity diverged from the independent layout model"
            );
            assert_eq!(
                actual_digest,
                identity_state(case, false).content_digest(),
                "identical descriptor and journal must have stable identity"
            );

            let descriptor = state.descriptor.clone();
            let name = descriptor.name.clone();
            let environment = Environment::new()
                .register_extension(descriptor)
                .and_then(|next| next.push_extension_entry(&name, bytes(b"alpha")))
                .and_then(|next| next.push_extension_entry(&name, bytes(b"beta")))
                .expect("single descriptor fixture builds");
            let actual_root = environment.logical_root(&options);
            let repeated_root = Environment::new()
                .register_extension(state.descriptor.clone())
                .and_then(|next| next.push_extension_entry(&name, bytes(b"alpha")))
                .and_then(|next| next.push_extension_entry(&name, bytes(b"beta")))
                .expect("repeated descriptor fixture builds")
                .logical_root(&options);
            assert_eq!(
                actual_root, repeated_root,
                "identical descriptor and journal must have stable logical identity"
            );

            let mut expected_root = fln_hash::root::LogicalRootBuilder::new();
            expected_root.add_extension_delta(&name, actual_digest);
            expected_root.set_options(&options);
            assert_eq!(
                actual_root,
                expected_root.finalize(),
                "descriptor digest must propagate exactly into the logical root"
            );
            assert!(
                digests.insert(actual_digest),
                "all 12 descriptor combinations must have distinct delta identity"
            );
            assert!(
                roots.insert(actual_root),
                "all 12 descriptor combinations must have distinct logical roots"
            );

            eprintln!(
                "{{\"schema\":\"fln.unit.extension-descriptor-identity\",\"version\":1,\
                 \"bead\":\"fln-amv.2\",\"claim_type\":\"bounded_model\",\
                 \"merge\":\"{}\",\"merge_tag\":{},\
                 \"checkpoint\":\"{}\",\"checkpoint_tag\":{},\
                 \"provenance\":\"{}\",\"provenance_tag\":{},\
                 \"journal_entries\":2,\"descriptor_position\":\"before_journal\",\
                 \"delta_digest\":\"{actual_digest}\",\"logical_root\":\"{actual_root}\",\
                 \"repeatability\":\"pass\",\"status\":\"pass\"}}",
                merge_label(case.merge),
                modeled_merge_tag(case.merge),
                checkpoint_label(case.checkpoint),
                modeled_checkpoint_tag(case.checkpoint),
                provenance_label(case.provenance),
                modeled_provenance_tag(case.provenance)
            );
        }

        assert_eq!(digests.len(), 12);
        assert_eq!(roots.len(), 12);
    }

    /// The `fln-amv.2` child matrix, as lane-consumable evidence.
    ///
    /// Third of the three producers `fln-amv.14` needs, and the same division as the
    /// declaration matrices in `environment.rs`: the unit tests keep their
    /// `fln.unit.*` summaries on stderr, this emits
    /// `fln.e2e.extension-descriptor-matrix/1` on stdout so the authoritative bundle
    /// can carry a separately identifiable fln-amv.2 child.
    ///
    /// Twelve combination rows, one defect row per combination, one summary.
    #[test]
    fn extension_descriptor_matrix_e2e_emits_detailed_real_path_evidence() {
        let run_id = std::env::var("FLN_ENV_E2E_RUN_ID")
            .unwrap_or_else(|_| "standalone-cargo-test".to_owned());
        assert!(
            run_id
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')),
            "E2E run id must be JSON-safe ASCII"
        );
        let cases = descriptor_identity_cases();
        assert_eq!(cases.len(), 12, "the complete 3x2x2 matrix is required");
        let options = KVMap::new();
        let started = Instant::now();
        let mut digests = HashSet::with_capacity(cases.len());
        let mut roots = HashSet::with_capacity(cases.len());
        let mut rows = 0usize;

        for case in cases {
            let case_started = Instant::now();
            let state = identity_state(case, false);
            let actual_digest = state.content_digest();
            let expected_digest =
                modeled_extension_content_digest(&state, DescriptorDigestModel::Canonical);
            let repeated_digest = identity_state(case, false).content_digest();
            assert_eq!(actual_digest, expected_digest);
            assert_eq!(actual_digest, repeated_digest);

            // Real registration and real appends, then root propagation proved against
            // an independently built root over the same delta digest.
            let name = state.descriptor.name.clone();
            let environment = Environment::new()
                .register_extension(state.descriptor.clone())
                .and_then(|next| next.push_extension_entry(&name, bytes(b"alpha")))
                .and_then(|next| next.push_extension_entry(&name, bytes(b"beta")))
                .expect("descriptor fixture builds");
            let actual_root = environment.logical_root(&options);
            let mut expected_root_builder = fln_hash::root::LogicalRootBuilder::new();
            expected_root_builder.add_extension_delta(&name, actual_digest);
            expected_root_builder.set_options(&options);
            let expected_root = expected_root_builder.finalize();
            assert_eq!(actual_root, expected_root);
            assert!(digests.insert(actual_digest), "descriptor delta aliased");
            assert!(roots.insert(actual_root), "descriptor root aliased");
            rows += 1;

            println!(
                "{{\"schema\":\"fln.e2e.extension-descriptor-matrix\",\"version\":1,\
                 \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.2\",\"fln-amv.14\"],\
                 \"scenario\":\"extension-descriptor-matrix\",\
                 \"merge\":\"{}\",\"merge_tag\":{},\"checkpoint\":\"{}\",\
                 \"checkpoint_tag\":{},\"provenance\":\"{}\",\"provenance_tag\":{},\
                 \"descriptor_position\":\"before_journal\",\"journal_entries\":2,\
                 \"expected_digest\":\"{expected_digest}\",\
                 \"actual_digest\":\"{actual_digest}\",\
                 \"repeated_digest\":\"{repeated_digest}\",\
                 \"digest_relation\":\"equal\",\"repeat_relation\":\"equal\",\
                 \"expected_root\":\"{expected_root}\",\"actual_root\":\"{actual_root}\",\
                 \"root_relation\":\"equal\",\"root_propagation\":\"exact\",\
                 \"model\":\"independent-descriptor-layout-v1\",\"status\":\"pass\",\
                 \"elapsed_us\":{},\"final_state\":\"verified\"}}",
                merge_label(case.merge),
                modeled_merge_tag(case.merge),
                checkpoint_label(case.checkpoint),
                modeled_checkpoint_tag(case.checkpoint),
                provenance_label(case.provenance),
                modeled_provenance_tag(case.provenance),
                case_started.elapsed().as_micros()
            );

            // The named defects, each on this same combination. Every one must move the
            // delta digest: a dimension that can be omitted, a tag that can be swapped,
            // a debug rendering, or a descriptor written after the journal would each
            // let two semantically different extensions share an identity, which is
            // exactly what fln-amv.2 was filed about.
            let omit_merge =
                modeled_extension_content_digest(&state, DescriptorDigestModel::OmitMerge);
            let omit_checkpoint =
                modeled_extension_content_digest(&state, DescriptorDigestModel::OmitCheckpoint);
            let omit_provenance =
                modeled_extension_content_digest(&state, DescriptorDigestModel::OmitProvenance);
            let swapped_tags =
                modeled_extension_content_digest(&state, DescriptorDigestModel::SwapMergeTagValues);
            let swapped_fields = modeled_extension_content_digest(
                &state,
                DescriptorDigestModel::SwapMergeAndCheckpointFields,
            );
            let debug_text =
                modeled_extension_content_digest(&state, DescriptorDigestModel::DebugText);
            let after_journal = modeled_extension_content_digest(
                &state,
                DescriptorDigestModel::DescriptorAfterJournal,
            );
            for (label, modeled) in [
                ("omit_merge", omit_merge),
                ("omit_checkpoint", omit_checkpoint),
                ("omit_provenance", omit_provenance),
                ("debug_text", debug_text),
                ("descriptor_after_journal", after_journal),
            ] {
                assert_ne!(
                    actual_digest,
                    modeled,
                    "{label} did not move the delta digest for {}/{}/{}",
                    merge_label(case.merge),
                    checkpoint_label(case.checkpoint),
                    provenance_label(case.provenance)
                );
            }

            // The two swap models are CONDITIONALLY discriminating, and saying so is
            // the point: swapping a tag value is a no-op when the swapped value equals
            // the original, and swapping two adjacent fields is a no-op when they
            // already hold the same tag. A validator that demanded "differs" here
            // would fail on the legitimate cases; one that ignored these rows would
            // miss a real regression. So the record carries the expected relation,
            // derived from the same predicate the assertion uses.
            let merge_tag_swap_must_change = case.merge != MergeSemantics::ConflictsRequireReview;
            let field_swap_must_change =
                modeled_merge_tag(case.merge) != modeled_checkpoint_tag(case.checkpoint);
            assert_eq!(
                swapped_tags != actual_digest,
                merge_tag_swap_must_change,
                "merge-tag swap had the wrong effect for {}/{}/{}",
                merge_label(case.merge),
                checkpoint_label(case.checkpoint),
                provenance_label(case.provenance)
            );
            assert_eq!(
                swapped_fields != actual_digest,
                field_swap_must_change,
                "adjacent field swap had the wrong effect for {}/{}/{}",
                merge_label(case.merge),
                checkpoint_label(case.checkpoint),
                provenance_label(case.provenance)
            );
            rows += 1;

            println!(
                "{{\"schema\":\"fln.e2e.extension-descriptor-matrix\",\"version\":1,\
                 \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.2\",\"fln-amv.14\"],\
                 \"scenario\":\"extension-descriptor-defects\",\
                 \"merge\":\"{}\",\"checkpoint\":\"{}\",\"provenance\":\"{}\",\
                 \"canonical_digest\":\"{actual_digest}\",\
                 \"omit_merge_digest\":\"{omit_merge}\",\"omit_merge_relation\":\"differs\",\
                 \"omit_checkpoint_digest\":\"{omit_checkpoint}\",\
                 \"omit_checkpoint_relation\":\"differs\",\
                 \"omit_provenance_digest\":\"{omit_provenance}\",\
                 \"omit_provenance_relation\":\"differs\",\
                 \"swapped_tag_digest\":\"{swapped_tags}\",\
                 \"swapped_tag_relation\":\"{}\",\
                 \"swapped_tag_discriminating\":{merge_tag_swap_must_change},\
                 \"swapped_field_digest\":\"{swapped_fields}\",\
                 \"swapped_field_relation\":\"{}\",\
                 \"swapped_field_discriminating\":{field_swap_must_change},\
                 \"debug_text_digest\":\"{debug_text}\",\"debug_text_relation\":\"differs\",\
                 \"after_journal_digest\":\"{after_journal}\",\
                 \"after_journal_relation\":\"differs\",\
                 \"named_defects_discriminated\":[\"omitted_dimension\",\"swapped_tag\",\
                 \"debug_text\",\"after_journal\"],\"status\":\"pass\",\
                 \"final_state\":\"verified\"}}",
                merge_label(case.merge),
                checkpoint_label(case.checkpoint),
                provenance_label(case.provenance),
                if merge_tag_swap_must_change {
                    "differs"
                } else {
                    "equal_by_construction"
                },
                if field_swap_must_change {
                    "differs"
                } else {
                    "equal_by_construction"
                }
            );
        }

        assert_eq!(digests.len(), 12);
        assert_eq!(roots.len(), 12);
        println!(
            "{{\"schema\":\"fln.e2e.extension-descriptor-matrix\",\"version\":1,\
             \"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.2\",\"fln-amv.14\"],\
             \"scenario\":\"extension-descriptor-summary\",\"combination_count\":12,\
             \"merge_variants\":3,\"checkpoint_variants\":2,\"provenance_variants\":2,\
             \"distinct_delta_digests\":{},\"distinct_logical_roots\":{},\
             \"descriptor_position\":\"before_journal\",\"matrix_rows\":{rows},\
             \"root_propagation\":\"exact\",\"claim_type\":\"bounded_model\",\
             \"status\":\"pass\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
            digests.len(),
            roots.len(),
            started.elapsed().as_micros()
        );
        assert_eq!(rows, 24);
    }

    #[test]
    fn descriptor_identity_named_mutants_are_discriminated() {
        let mut always_killed = 0usize;
        let mut swapped_merge_tag_values_killed = 0usize;
        let mut swapped_merge_and_checkpoint_fields_killed = 0usize;
        for case in descriptor_identity_cases() {
            let state = identity_state(case, false);
            let canonical = state.content_digest();
            for (mutation, model) in [
                ("omit_merge", DescriptorDigestModel::OmitMerge),
                ("omit_checkpoint", DescriptorDigestModel::OmitCheckpoint),
                ("omit_provenance", DescriptorDigestModel::OmitProvenance),
                ("debug_text", DescriptorDigestModel::DebugText),
                (
                    "descriptor_after_journal",
                    DescriptorDigestModel::DescriptorAfterJournal,
                ),
            ] {
                let mutated = modeled_extension_content_digest(&state, model);
                assert_ne!(
                    canonical,
                    mutated,
                    "{mutation} mutant survived for {}/{}/{}",
                    merge_label(case.merge),
                    checkpoint_label(case.checkpoint),
                    provenance_label(case.provenance)
                );
                always_killed += 1;
            }

            let swapped_merge_tag_values =
                modeled_extension_content_digest(&state, DescriptorDigestModel::SwapMergeTagValues);
            let merge_tag_swap_must_change = case.merge != MergeSemantics::ConflictsRequireReview;
            assert_eq!(
                swapped_merge_tag_values != canonical,
                merge_tag_swap_must_change,
                "single merge-tag value swap had the wrong effect for {}/{}/{}",
                merge_label(case.merge),
                checkpoint_label(case.checkpoint),
                provenance_label(case.provenance)
            );
            swapped_merge_tag_values_killed += usize::from(merge_tag_swap_must_change);

            let swapped_fields = modeled_extension_content_digest(
                &state,
                DescriptorDigestModel::SwapMergeAndCheckpointFields,
            );
            let field_swap_must_change =
                modeled_merge_tag(case.merge) != modeled_checkpoint_tag(case.checkpoint);
            assert_eq!(
                swapped_fields != canonical,
                field_swap_must_change,
                "adjacent descriptor-field swap had the wrong effect for {}/{}/{}",
                merge_label(case.merge),
                checkpoint_label(case.checkpoint),
                provenance_label(case.provenance)
            );
            swapped_merge_and_checkpoint_fields_killed += usize::from(field_swap_must_change);

            eprintln!(
                "{{\"schema\":\"fln.unit.extension-descriptor-mutants\",\"version\":1,\
                 \"bead\":\"fln-amv.2\",\"claim_type\":\"bounded_model\",\
                 \"merge\":\"{}\",\"checkpoint\":\"{}\",\"provenance\":\"{}\",\
                 \"canonical_digest\":\"{canonical}\",\
                 \"always_killed\":[\"omit_merge\",\"omit_checkpoint\",\"omit_provenance\",\
                 \"debug_text\",\"descriptor_after_journal\"],\
                 \"swap_merge_tag_values_changed\":{},\
                 \"swap_merge_and_checkpoint_fields_changed\":{},\
                 \"status\":\"pass\"}}",
                merge_label(case.merge),
                checkpoint_label(case.checkpoint),
                provenance_label(case.provenance),
                merge_tag_swap_must_change,
                field_swap_must_change
            );
        }
        assert_eq!(
            always_killed, 60,
            "five universally observable defects must be killed in all 12 cases"
        );
        assert_eq!(
            swapped_merge_tag_values_killed, 8,
            "swapping only the two affected merge-tag values changes 8 of 12 cases"
        );
        assert_eq!(
            swapped_merge_and_checkpoint_fields_killed, 8,
            "swapping adjacent equal tags is a no-op in 4 cases and changes the other 8"
        );
        eprintln!(
            "{{\"schema\":\"fln.unit.extension-descriptor-mutants-summary\",\"version\":1,\
             \"bead\":\"fln-amv.2\",\"claim_type\":\"bounded_model\",\
             \"descriptor_cases\":12,\"universal_mutation_classes\":5,\
             \"universal_discriminations\":{always_killed},\
             \"swap_merge_tag_values_discriminations\":{swapped_merge_tag_values_killed},\
             \"swap_adjacent_fields_discriminations\":\
             {swapped_merge_and_checkpoint_fields_killed},\
             \"total_discriminations\":{},\"status\":\"pass\"}}",
            always_killed
                + swapped_merge_tag_values_killed
                + swapped_merge_and_checkpoint_fields_killed
        );
    }

    #[test]
    fn descriptor_identity_is_stable_across_1_8_32_concurrent_complete_builds() {
        let cases = descriptor_identity_cases();
        let options = KVMap::new();
        let canonical_environment = identity_environment(cases.iter().copied());
        let canonical_root = canonical_environment.logical_root(&options);

        let mut expected_builder = fln_hash::root::LogicalRootBuilder::new();
        for case in cases.iter().copied() {
            let state = identity_state(case, true);
            expected_builder.add_extension_delta(
                &state.descriptor.name,
                modeled_extension_content_digest(&state, DescriptorDigestModel::Canonical),
            );
        }
        expected_builder.set_options(&options);
        let expected_root = expected_builder.finalize();
        assert_eq!(
            canonical_root, expected_root,
            "the full environment root must equal the explicit 12-descriptor model"
        );

        let omitted_root =
            identity_environment(cases.iter().copied().skip(1)).logical_root(&options);
        assert_ne!(
            omitted_root, expected_root,
            "omitting one descriptor must change the aggregate root"
        );
        let reversed_journal_root = identity_environment_with_journal(
            cases.iter().copied(),
            IdentityJournalOrder::BetaThenAlpha,
        )
        .logical_root(&options);
        assert_ne!(
            reversed_journal_root, expected_root,
            "reversing every journal must change the aggregate root"
        );

        for worker_count in [1usize, 8, 32] {
            let results = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..worker_count)
                    .map(|worker_index| {
                        let permutation = permuted_descriptor_cases(&cases, worker_index);
                        scope.spawn(move || {
                            let order_id = descriptor_order_id(&permutation);
                            let environment = identity_environment(permutation.iter().copied());
                            let root = environment.logical_root(&KVMap::new());
                            (order_id, environment, root)
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|handle| handle.join().expect("descriptor worker joins"))
                    .collect::<Vec<_>>()
            });

            assert_eq!(
                results.len(),
                worker_count,
                "every requested worker must build and hash a complete environment"
            );
            let order_ids: HashSet<_> = results.iter().map(|(order_id, _, _)| *order_id).collect();
            assert_eq!(
                order_ids.len(),
                worker_count,
                "every worker must receive a distinct full descriptor permutation"
            );
            for (worker_index, (order_id, environment, actual_root)) in results.iter().enumerate() {
                assert_eq!(
                    environment, &canonical_environment,
                    "{worker_count}-worker environment diverged for order {order_id}"
                );
                assert_eq!(
                    *actual_root, expected_root,
                    "{worker_count}-worker root diverged for order {order_id}"
                );
                for case in cases.iter().copied() {
                    let name = identity_descriptor(case, true).name;
                    let state = environment
                        .extension(&name)
                        .expect("every worker retains every descriptor state");
                    assert_eq!(
                        state.len(),
                        2,
                        "every worker must retain the complete journal for {}",
                        name.to_display_string()
                    );
                }
                eprintln!(
                    "{{\"schema\":\"fln.unit.extension-descriptor-concurrent-build\",\
                     \"version\":1,\"bead\":\"fln-amv.2\",\
                     \"claim_type\":\"bounded_model\",\
                     \"execution_model\":\"independent_complete_build_per_worker\",\
                     \"concurrent_worker_count\":{worker_count},\
                     \"worker_index\":{worker_index},\
                     \"input_order_id\":\"{order_id}\",\
                     \"descriptor_cases\":12,\"journal_entries_per_descriptor\":2,\
                     \"actual_logical_root\":\"{actual_root}\",\
                     \"expected_logical_root\":\"{expected_root}\",\
                     \"environment_relation\":\"equal\",\
                     \"logical_root_relation\":\"equal\",\"status\":\"pass\"}}"
                );
            }

            let mut sorted_order_ids: Vec<_> = order_ids.into_iter().collect();
            sorted_order_ids.sort_unstable();
            let mut order_set_writer = CanonWriter::new();
            order_set_writer.str("fln.test.extension-descriptor-order-set");
            order_set_writer.u16(1);
            order_set_writer.u64(sorted_order_ids.len() as u64);
            for order_id in sorted_order_ids {
                order_set_writer.bytes(&order_id.0);
            }
            let order_set_hash = hash(Domain::Fixture, &order_set_writer.into_bytes());
            eprintln!(
                "{{\"schema\":\"fln.unit.extension-descriptor-concurrent-build-summary\",\
                 \"version\":1,\
                 \"bead\":\"fln-amv.2\",\"claim_type\":\"bounded_model\",\
                 \"execution_model\":\"independent_complete_build_per_worker\",\
                 \"concurrent_worker_count\":{worker_count},\"productive_workers\":{},\
                 \"distinct_full_permutations\":{},\"descriptor_cases_per_worker\":12,\
                 \"order_set_hash\":\"{order_set_hash}\",\
                 \"expected_logical_root\":\"{expected_root}\",\
                 \"omitted_descriptor_root\":\"{omitted_root}\",\
                 \"reversed_journal_root\":\"{reversed_journal_root}\",\
                 \"environment_relation\":\"equal\",\
                 \"logical_root_relation\":\"equal\",\
                 \"omission_negative_control\":\"pass\",\
                 \"journal_order_negative_control\":\"pass\",\
                 \"status\":\"pass\"}}",
                results.len(),
                worker_count
            );
        }
    }

    #[test]
    fn persistent_journal_boundaries_share_and_replay_exactly() {
        for count in [0usize, 1, 31, 32, 33, 1_023, 1_024, 1_025] {
            let state = numbered_state(count);
            assert_eq!(state.len(), count);
            assert_eq!(state.is_empty(), count == 0);
            for (index, entry) in state.entries().enumerate() {
                let encoded: [u8; 8] = entry.payload.as_ref().try_into().expect("u64 payload");
                assert_eq!(u64::from_le_bytes(encoded), index as u64);
            }
        }

        let base = numbered_state(1_024);
        let root = base.journal.root.as_ref().expect("non-empty journal root");
        let before = Arc::strong_count(root);
        let snapshot = base.clone();
        assert_eq!(
            Arc::strong_count(root),
            before + 1,
            "snapshot is one Arc bump"
        );

        let old_ptrs: HashSet<*const ()> = snapshot.journal.node_ptrs().into_iter().collect();
        let extended = snapshot.push_entry(bytes(&1_024u64.to_le_bytes()));
        let new_ptrs = extended.journal.node_ptrs();
        let fresh = new_ptrs
            .iter()
            .filter(|ptr| !old_ptrs.contains(ptr))
            .count();
        let shared = new_ptrs.len() - fresh;
        assert!(
            fresh <= extended.journal.depth as usize + 1,
            "append created {fresh} nodes at depth {}",
            extended.journal.depth
        );
        assert_eq!(shared, old_ptrs.len(), "full prior tree remains shared");
        assert_eq!(base.len(), 1_024, "source snapshot is unchanged");
        assert_eq!(extended.len(), 1_025);
        drop(extended);
        assert_eq!(
            Arc::strong_count(root),
            before + 1,
            "dropping the appended branch releases only its shared root reference"
        );
        drop(snapshot);
        assert_eq!(
            Arc::strong_count(root),
            before,
            "dropping a snapshot releases exactly its one root reference"
        );
    }

    #[test]
    fn persistent_journal_storage_and_replay_scale_linearly() {
        let mut state = numbered_state(0);
        let mut cumulative = JournalAppendWork::default();
        for index in 0..100_000u64 {
            let work = state.journal.next_append_work();
            cumulative.node_allocations += work.node_allocations;
            cumulative.copied_child_slots += work.copied_child_slots;
            cumulative.copied_entry_slots += work.copied_entry_slots;
            state = state.push_entry(bytes(&index.to_le_bytes()));

            if state.len() == 10_000 || state.len() == 100_000 {
                let node_count = state.journal.node_ptrs().len();
                let chunk_count = state.len().div_ceil(JOURNAL_CHUNK_CAPACITY);
                let max_path_nodes = state.journal.depth as usize + 2;
                assert!(
                    node_count <= chunk_count * 2,
                    "{node_count} nodes exceeds linear bound for {chunk_count} chunks"
                );
                assert_eq!(state.entries().count(), state.len());
                assert!(
                    cumulative.node_allocations <= state.len() * max_path_nodes,
                    "append node allocation exceeds the bounded path-copy model"
                );
                assert!(
                    cumulative.copied_child_slots + cumulative.copied_entry_slots
                        <= state.len() * max_path_nodes * JOURNAL_CHUNK_CAPACITY,
                    "copied slots exceed the bounded 32-way path-copy model"
                );
                println!(
                    "{{\"schema\":\"fln.test.extension-journal-scaling\",\"version\":1,\"entries\":{},\"chunk_count\":{chunk_count},\"node_count\":{node_count},\"depth\":{},\"replay_operations\":{},\"node_allocations\":{},\"copied_child_slots\":{},\"copied_entry_slots\":{},\"timing_used_as_gate\":false,\"status\":\"pass\"}}",
                    state.len(),
                    state.journal.depth,
                    state.entries().count(),
                    cumulative.node_allocations,
                    cumulative.copied_child_slots,
                    cumulative.copied_entry_slots
                );
            }
        }
        let last = state.entries().last().expect("non-empty replay");
        let encoded: [u8; 8] = last.payload.as_ref().try_into().expect("u64 payload");
        assert_eq!(u64::from_le_bytes(encoded), 99_999);
    }

    #[test]
    fn persistent_journal_generated_append_fork_merge_matches_vec_model() {
        fn next(seed: &mut u64) -> u64 {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            *seed
        }

        let mut seed = 0x8D26_7A4B_E19C_350Fu64;
        for round in 0..512usize {
            let mode = match round % 3 {
                0 => MergeSemantics::AppendOrdered,
                1 => MergeSemantics::SetUnion,
                _ => MergeSemantics::ConflictsRequireReview,
            };
            let descriptor = descriptor(mode, PayloadProvenance::Understood);
            let base_len = next(&mut seed) as usize % 65;
            let ours_len = next(&mut seed) as usize % 9;
            let theirs_len = next(&mut seed) as usize % 9;
            let mut base = ExtensionState::new(descriptor);
            let mut base_model = Vec::<Vec<u8>>::new();
            for index in 0..base_len {
                let payload = if mode == MergeSemantics::SetUnion && index > 0 && index % 7 == 0 {
                    base_model[0].clone()
                } else {
                    (round as u64)
                        .rotate_left(19)
                        .wrapping_add(index as u64)
                        .to_le_bytes()
                        .to_vec()
                };
                base = base.push_entry(bytes(&payload));
                base_model.push(payload);
            }

            let base_snapshot = base.clone();
            let mut ours = base.clone();
            let mut ours_model = base_model.clone();
            for offset in 0..ours_len {
                let payload = if mode == MergeSemantics::SetUnion && offset > 0 && offset % 4 == 1 {
                    ours_model[base_len].clone()
                } else {
                    next(&mut seed)
                        .wrapping_add((offset as u64).rotate_left(11))
                        .to_le_bytes()
                        .to_vec()
                };
                ours = ours.push_entry(bytes(&payload));
                ours_model.push(payload);
            }
            let mut theirs = base.clone();
            let mut theirs_model = base_model.clone();
            for offset in 0..theirs_len {
                let payload = if mode == MergeSemantics::SetUnion && offset % 3 == 0 {
                    ours_model
                        .get(base_len + (offset % ours_len.max(1)))
                        .cloned()
                        .unwrap_or_else(|| next(&mut seed).to_le_bytes().to_vec())
                } else {
                    next(&mut seed)
                        .wrapping_add((offset as u64).rotate_left(23))
                        .to_le_bytes()
                        .to_vec()
                };
                theirs = theirs.push_entry(bytes(&payload));
                theirs_model.push(payload);
            }

            assert_eq!(
                base.entries()
                    .map(|entry| entry.payload.to_vec())
                    .collect::<Vec<_>>(),
                base_model,
                "round={round}: append history matches Vec"
            );
            assert_eq!(base, base_snapshot, "round={round}: forks isolate base");

            match mode {
                MergeSemantics::AppendOrdered => {
                    let mut expected = ours_model;
                    expected.extend_from_slice(&theirs_model[base_len..]);
                    let merged = merge_with_test_limits(&base, &ours, &theirs)
                        .expect("append-ordered generated merge succeeds");
                    assert_eq!(
                        merged
                            .entries()
                            .map(|entry| entry.payload.to_vec())
                            .collect::<Vec<_>>(),
                        expected,
                        "round={round}: append merge matches Vec"
                    );
                }
                MergeSemantics::SetUnion => {
                    let expected = canonical_set_union_raw_model(
                        &base_model,
                        &ours_model[base_len..],
                        &theirs_model[base_len..],
                    );
                    let merged = merge_with_test_limits(&base, &ours, &theirs)
                        .expect("set-union generated merge succeeds");
                    let reversed = merge_with_test_limits(&base, &theirs, &ours)
                        .expect("reversed set-union generated merge succeeds");
                    assert_eq!(
                        raw_payloads(&merged),
                        expected,
                        "round={round}: raw set-union merge matches canonical lossless model"
                    );
                    assert_eq!(
                        semantic_payloads(&merged),
                        stable_unique_model(&expected),
                        "round={round}: semantic set matches the first-occurrence model"
                    );
                    assert_eq!(
                        raw_payloads(&reversed),
                        expected,
                        "round={round}: branch permutation preserves raw merge product"
                    );
                    assert_eq!(
                        reversed.content_digest(),
                        merged.content_digest(),
                        "round={round}: branch permutation preserves the logical root"
                    );
                }
                MergeSemantics::ConflictsRequireReview if ours_len > 0 && theirs_len > 0 => {
                    assert!(matches!(
                        merge_with_test_limits(&base, &ours, &theirs),
                        Err(MergeConflict::ConcurrentChanges { .. })
                    ));
                }
                MergeSemantics::ConflictsRequireReview => {
                    let expected = if theirs_len > 0 {
                        theirs_model
                    } else {
                        ours_model
                    };
                    let merged = merge_with_test_limits(&base, &ours, &theirs)
                        .expect("one-sided generated review merge succeeds");
                    assert_eq!(
                        merged
                            .entries()
                            .map(|entry| entry.payload.to_vec())
                            .collect::<Vec<_>>(),
                        expected,
                        "round={round}: one-sided review merge matches Vec"
                    );
                }
            }
        }
    }

    #[test]
    fn replay_preserves_exact_recorded_order() {
        let state = ExtensionState::new(descriptor(
            MergeSemantics::AppendOrdered,
            PayloadProvenance::Understood,
        ))
        .push_entry(bytes(b"a"))
        .push_entry(bytes(b"b"))
        .push_entry(bytes(b"c"));
        let replayed: Vec<&[u8]> = state.entries().map(|e| &*e.payload).collect();
        assert_eq!(replayed, vec![b"a".as_slice(), b"b", b"c"]);
    }

    #[test]
    fn opaque_payloads_are_lossless_flagged_and_block_invalidation() {
        let opaque = ExtensionState::new(descriptor(
            MergeSemantics::AppendOrdered,
            PayloadProvenance::Opaque,
        ))
        .push_entry(bytes(&[0xde, 0xad, 0xbe, 0xef]));
        assert_eq!(
            &*opaque.entries().next().expect("one opaque entry").payload,
            &[0xde, 0xad, 0xbe, 0xef]
        );
        assert_eq!(opaque.provenance(), PayloadProvenance::Opaque);
        assert!(!opaque.supports_fine_invalidation(), "never guessed safe");
        let understood = ExtensionState::new(descriptor(
            MergeSemantics::AppendOrdered,
            PayloadProvenance::Understood,
        ));
        assert!(understood.supports_fine_invalidation());
    }

    #[test]
    fn merge_follows_the_declared_contract() {
        let base = ExtensionState::new(descriptor(
            MergeSemantics::AppendOrdered,
            PayloadProvenance::Understood,
        ))
        .push_entry(bytes(b"base"));
        let ours = base.push_entry(bytes(b"ours"));
        let theirs = base.push_entry(bytes(b"theirs"));
        let merged = merge_with_test_limits(&base, &ours, &theirs).expect("append-ordered merges");
        let seen: Vec<&[u8]> = merged.entries().map(|e| &*e.payload).collect();
        assert_eq!(seen, vec![b"base".as_slice(), b"ours", b"theirs"]);
    }

    #[test]
    fn set_union_keeps_raw_replay_lossless_and_projects_exact_semantics() {
        struct Case {
            name: &'static str,
            base: Vec<&'static [u8]>,
            ours: Vec<&'static [u8]>,
            theirs: Vec<&'static [u8]>,
            expected_raw: Vec<&'static [u8]>,
            expected_semantic: Vec<&'static [u8]>,
        }

        fn append_all(mut state: ExtensionState, payloads: &[&[u8]]) -> ExtensionState {
            for payload in payloads {
                state = state.push_entry(bytes(payload));
            }
            state
        }

        let cases = [
            Case {
                name: "base and cross-branch duplicates",
                base: vec![b"base", b"base"],
                ours: vec![b"x"],
                theirs: vec![b"x", b"y"],
                expected_raw: vec![b"base", b"base", b"x", b"x", b"y"],
                expected_semantic: vec![b"base", b"x", b"y"],
            },
            Case {
                name: "duplicates within the lexicographically first suffix",
                base: vec![b"base"],
                ours: vec![b"a", b"a"],
                theirs: vec![b"z"],
                expected_raw: vec![b"base", b"a", b"a", b"z"],
                expected_semantic: vec![b"base", b"a", b"z"],
            },
            Case {
                name: "duplicates within the branch supplied as theirs",
                base: vec![b"base"],
                ours: vec![b"z"],
                theirs: vec![b"a", b"a"],
                expected_raw: vec![b"base", b"a", b"a", b"z"],
                expected_semantic: vec![b"base", b"a", b"z"],
            },
            Case {
                name: "empty payload is an ordinary exact byte key",
                base: vec![b"root"],
                ours: vec![b"", b"z"],
                theirs: vec![b"", b"a"],
                expected_raw: vec![b"root", b"", b"a", b"", b"z"],
                expected_semantic: vec![b"root", b"", b"a", b"z"],
            },
            Case {
                name: "byte-prefix keys remain distinct",
                base: vec![],
                ours: vec![b"\0"],
                theirs: vec![b"\0\0"],
                expected_raw: vec![b"\0", b"\0\0"],
                expected_semantic: vec![b"\0", b"\0\0"],
            },
        ];

        for case in cases {
            let base = append_all(
                ExtensionState::new(descriptor(
                    MergeSemantics::SetUnion,
                    PayloadProvenance::Understood,
                )),
                &case.base,
            );
            let ours = append_all(base.clone(), &case.ours);
            let theirs = append_all(base.clone(), &case.theirs);
            let base_before = raw_payloads(&base);

            let merged = merge_with_test_limits(&base, &ours, &theirs).expect(case.name);
            let reversed = merge_with_test_limits(&base, &theirs, &ours).expect(case.name);
            let expected_raw = case
                .expected_raw
                .iter()
                .map(|payload| payload.to_vec())
                .collect::<Vec<_>>();
            let expected_semantic = case
                .expected_semantic
                .iter()
                .map(|payload| payload.to_vec())
                .collect::<Vec<_>>();

            assert_eq!(raw_payloads(&merged), expected_raw, "{}", case.name);
            assert_eq!(raw_payloads(&reversed), expected_raw, "{}", case.name);
            assert_eq!(
                semantic_payloads(&merged),
                expected_semantic,
                "{}",
                case.name
            );
            assert_eq!(
                semantic_len(&merged),
                expected_semantic.len(),
                "{}",
                case.name
            );
            assert_eq!(
                merged.content_digest(),
                reversed.content_digest(),
                "{}",
                case.name
            );
            assert_eq!(
                merged.len(),
                case.base.len() + case.ours.len() + case.theirs.len(),
                "{}: raw replay evidence must never disappear",
                case.name
            );
            assert_eq!(raw_payloads(&base), base_before, "{}", case.name);
        }

        fn deliberately_colliding_test_hash(_: &[u8]) -> u8 {
            0
        }
        let collision_base = ExtensionState::new(descriptor(
            MergeSemantics::SetUnion,
            PayloadProvenance::Understood,
        ));
        let collision = collision_base
            .push_entry(bytes(b"left"))
            .push_entry(bytes(b"right"));
        assert_eq!(
            deliberately_colliding_test_hash(b"left"),
            deliberately_colliding_test_hash(b"right")
        );
        assert_eq!(
            semantic_payloads(&collision),
            vec![b"left".to_vec(), b"right".to_vec()],
            "semantic equality is exact bytes, not a fallible hash identity"
        );

        let base = ExtensionState::new(descriptor(
            MergeSemantics::SetUnion,
            PayloadProvenance::Understood,
        ))
        .push_entry(bytes(b"base"));
        let ours = base.push_entry(bytes(b"x"));
        let theirs = base.push_entry(bytes(b"x")).push_entry(bytes(b"y"));
        let actual = merge_with_test_limits(&base, &ours, &theirs).expect("set union merges");
        let mut legacy_one_sided = raw_payloads(&ours);
        for payload in raw_payloads(&theirs).into_iter().skip(base.len()) {
            if !legacy_one_sided.contains(&payload) {
                legacy_one_sided.push(payload);
            }
        }
        assert_ne!(
            raw_payloads(&actual),
            legacy_one_sided,
            "the historical one-sided dedup mutant must lose the proof"
        );
    }

    #[test]
    fn set_union_limits_are_independent_atomic_and_recoverable() {
        fn set_state(payloads: &[&[u8]]) -> ExtensionState {
            let mut state = ExtensionState::new(descriptor(
                MergeSemantics::SetUnion,
                PayloadProvenance::Understood,
            ));
            for payload in payloads {
                state = state.push_entry(bytes(payload));
            }
            state
        }

        fn complete(
            base: &ExtensionState,
            ours: &ExtensionState,
            theirs: &ExtensionState,
            limits: SetUnionLimits,
        ) -> (ExtensionState, SetUnionFacts) {
            match ExtensionState::merge(base, ours, theirs, limits)
                .expect("valid SetUnion histories do not conflict")
            {
                ExtensionMergeOutcome::Complete {
                    state,
                    set_union_facts: Some(facts),
                } => Some((state, facts)),
                _ => None,
            }
            .expect("SetUnion merge must complete")
        }

        fn inconclusive(
            base: &ExtensionState,
            ours: &ExtensionState,
            theirs: &ExtensionState,
            limits: SetUnionLimits,
        ) -> (SetUnionInconclusive, SetUnionFacts) {
            match ExtensionState::merge(base, ours, theirs, limits)
                .expect("valid SetUnion histories do not conflict")
            {
                ExtensionMergeOutcome::Inconclusive { reason, facts } => Some((reason, facts)),
                ExtensionMergeOutcome::Complete { .. } => None,
            }
            .expect("SetUnion merge must be inconclusive")
        }

        let empty = set_state(&[]);
        let (empty_product, empty_facts) =
            complete(&empty, &empty, &empty, SetUnionLimits::new(0, 0, 0));
        assert!(empty_product.is_empty());
        assert_eq!(empty_facts.raw_entries, 0);
        assert_eq!(empty_facts.raw_payload_bytes, 0);
        assert_eq!(empty_facts.examined_entries, 0);

        let one_empty = empty.push_entry(bytes(b""));
        let (one_empty_product, one_empty_facts) =
            complete(&empty, &one_empty, &empty, SetUnionLimits::new(1, 0, 0));
        assert_eq!(raw_payloads(&one_empty_product), vec![Vec::<u8>::new()]);
        assert_eq!(one_empty_facts.semantic_entries, 1);
        assert_eq!(one_empty_facts.maximum_entry_bytes, 0);

        let (entry_reason, entry_facts) =
            inconclusive(&empty, &one_empty, &empty, SetUnionLimits::new(0, 0, 0));
        assert_eq!(entry_reason.resource, SetUnionResource::Entries);
        assert_eq!((entry_reason.limit, entry_reason.actual), (0, 1));
        assert_eq!(entry_facts.examined_entries, 0);
        assert_eq!(entry_facts.examined_payload_bytes, 0);

        let two_bytes = empty.push_entry(bytes(b"ab"));
        let (_, exact_payload_facts) =
            complete(&empty, &two_bytes, &empty, SetUnionLimits::new(1, 2, 2));
        assert_eq!(exact_payload_facts.raw_payload_bytes, 2);
        let (payload_reason, payload_facts) =
            inconclusive(&empty, &two_bytes, &empty, SetUnionLimits::new(1, 1, 2));
        assert_eq!(payload_reason.resource, SetUnionResource::PayloadBytes);
        assert_eq!((payload_reason.limit, payload_reason.actual), (1, 2));
        assert_eq!(payload_facts.examined_entries, 0);

        let input_digests = (
            empty.content_digest(),
            two_bytes.content_digest(),
            empty.content_digest(),
        );
        let (entry_bytes_reason, entry_bytes_facts) =
            inconclusive(&empty, &two_bytes, &empty, SetUnionLimits::new(1, 2, 1));
        assert_eq!(entry_bytes_reason.resource, SetUnionResource::EntryBytes);
        assert_eq!(
            (entry_bytes_reason.limit, entry_bytes_reason.actual),
            (1, 2)
        );
        assert_eq!(entry_bytes_facts.examined_entries, 1);
        assert_eq!(entry_bytes_facts.examined_payload_bytes, 2);
        assert_eq!(entry_bytes_facts.maximum_entry_bytes, 2);
        assert_eq!(
            (
                empty.content_digest(),
                two_bytes.content_digest(),
                empty.content_digest(),
            ),
            input_digests,
            "inconclusive merge publishes no mutation or partial root"
        );
        let (recovered, recovered_facts) =
            complete(&empty, &two_bytes, &empty, SetUnionLimits::new(1, 2, 2));
        assert_eq!(raw_payloads(&recovered), vec![b"ab".to_vec()]);
        assert_eq!(recovered_facts.examined_entries, 1);

        let unequal_oversize_ours = empty.push_entry(bytes(b"xx"));
        let unequal_oversize_theirs = empty.push_entry(bytes(b"yyyy"));
        let unequal_oversize_limits = SetUnionLimits::new(2, 6, 1);
        let unequal_oversize_forward = inconclusive(
            &empty,
            &unequal_oversize_ours,
            &unequal_oversize_theirs,
            unequal_oversize_limits,
        );
        let unequal_oversize_reverse = inconclusive(
            &empty,
            &unequal_oversize_theirs,
            &unequal_oversize_ours,
            unequal_oversize_limits,
        );
        assert_eq!(unequal_oversize_forward, unequal_oversize_reverse);
        assert_eq!(unequal_oversize_forward.0.actual, 4);
        assert_eq!(unequal_oversize_forward.1.examined_entries, 2);
        assert_eq!(unequal_oversize_forward.1.examined_payload_bytes, 6);
        assert_eq!(unequal_oversize_forward.1.maximum_entry_bytes, 4);

        let duplicate_base = set_state(&[b"d", b"d"]);
        let duplicate_ours = duplicate_base.push_entry(bytes(b"d"));
        let duplicate_theirs = duplicate_base.push_entry(bytes(b"d"));
        let duplicate_limits = SetUnionLimits::new(4, 4, 1);
        let (duplicate_forward, duplicate_forward_facts) = complete(
            &duplicate_base,
            &duplicate_ours,
            &duplicate_theirs,
            duplicate_limits,
        );
        let (duplicate_reverse, duplicate_reverse_facts) = complete(
            &duplicate_base,
            &duplicate_theirs,
            &duplicate_ours,
            duplicate_limits,
        );
        assert_eq!(duplicate_forward, duplicate_reverse);
        assert_eq!(duplicate_forward_facts, duplicate_reverse_facts);
        assert_eq!(duplicate_forward_facts.semantic_entries, 1);
        assert_eq!(duplicate_forward_facts.duplicate_entries, 3);

        let unique_base = set_state(&[b"a"]);
        let unique_ours = unique_base.push_entry(bytes(b"b"));
        let unique_theirs = unique_base.push_entry(bytes(b"c"));
        let unique_limits = SetUnionLimits::new(3, 3, 1);
        let (unique_forward, unique_forward_facts) =
            complete(&unique_base, &unique_ours, &unique_theirs, unique_limits);
        let (unique_reverse, unique_reverse_facts) =
            complete(&unique_base, &unique_theirs, &unique_ours, unique_limits);
        assert_eq!(unique_forward, unique_reverse);
        assert_eq!(unique_forward_facts, unique_reverse_facts);
        assert_eq!(unique_forward_facts.semantic_entries, 3);
        assert_eq!(unique_forward_facts.duplicate_entries, 0);

        match two_bytes.semantic_projection(SetUnionLimits::new(1, 1, 2)) {
            SetUnionProjection::Inconclusive { reason, facts } => {
                assert_eq!(reason.resource, SetUnionResource::PayloadBytes);
                assert_eq!(facts.examined_entries, 0);
            }
            other => assert!(
                matches!(other, SetUnionProjection::Inconclusive { .. }),
                "over-budget projection must be inconclusive"
            ),
        }
        match two_bytes.semantic_projection(SetUnionLimits::new(1, 2, 2)) {
            SetUnionProjection::Complete { entries, facts } => {
                assert_eq!(entries.len(), 1);
                assert_eq!(facts.examined_payload_bytes, 2);
            }
            other => assert!(
                matches!(other, SetUnionProjection::Complete { .. }),
                "exact-limit projection must complete"
            ),
        }
    }

    #[test]
    fn set_union_exact_byte_cost_model_matches_declared_large_fixtures() {
        const LARGE_FIXTURE_ENTRIES: usize = 16_384;
        const DUPLICATE_KEYS: usize = 257;
        const PAYLOAD_BYTES: usize = 8;

        for (fixture, key_count) in [
            ("duplicate-heavy", DUPLICATE_KEYS),
            ("unique-heavy", LARGE_FIXTURE_ENTRIES),
        ] {
            let mut state = ExtensionState::new(descriptor(
                MergeSemantics::SetUnion,
                PayloadProvenance::Understood,
            ));
            for index in 0..LARGE_FIXTURE_ENTRIES {
                let key = (index % key_count) as u64;
                state = state.push_entry(bytes(&key.to_le_bytes()));
            }
            let limits = SetUnionLimits::new(
                LARGE_FIXTURE_ENTRIES,
                (LARGE_FIXTURE_ENTRIES * PAYLOAD_BYTES) as u128,
                PAYLOAD_BYTES,
            );
            let (entries, facts) = match state.semantic_projection(limits) {
                SetUnionProjection::Complete { entries, facts } => Some((entries, facts)),
                SetUnionProjection::Inconclusive { .. } => None,
            }
            .expect("declared large fixture must fit its exact limits");
            assert_eq!(facts.raw_entries, LARGE_FIXTURE_ENTRIES);
            assert_eq!(facts.examined_entries, LARGE_FIXTURE_ENTRIES);
            assert_eq!(
                facts.raw_payload_bytes,
                (LARGE_FIXTURE_ENTRIES * PAYLOAD_BYTES) as u128
            );
            assert_eq!(facts.examined_payload_bytes, facts.raw_payload_bytes);
            assert_eq!(facts.maximum_entry_bytes, PAYLOAD_BYTES);
            assert_eq!(facts.semantic_entries, key_count);
            assert_eq!(facts.duplicate_entries, LARGE_FIXTURE_ENTRIES - key_count);
            assert_eq!(entries.len(), key_count);
            println!(
                "{{\"schema\":\"fln.test.set-union-cost-model\",\"version\":1,\"fixture\":\"{fixture}\",\"raw_entries\":{},\"payload_bytes\":{},\"semantic_entries\":{},\"duplicate_entries\":{},\"equality\":\"exact_bytes_btree\",\"time_complexity\":\"O(n_log_u_exact_byte_comparisons)\",\"space_complexity\":\"O(u_borrowed_keys)\",\"timing_used_as_gate\":false,\"status\":\"pass\"}}",
                facts.raw_entries,
                facts.raw_payload_bytes,
                facts.semantic_entries,
                facts.duplicate_entries,
            );
        }
    }

    #[test]
    fn set_union_e2e_emits_detailed_real_path_evidence() {
        fn append_environment(
            mut environment: Environment,
            extension: &Name,
            payloads: &[&[u8]],
        ) -> Environment {
            for payload in payloads {
                environment = environment
                    .push_extension_entry(extension, *payload)
                    .expect("append through the real environment registry");
            }
            environment
        }

        fn replay_environment(
            descriptor: &ExtensionDescriptor,
            payloads: &[Vec<u8>],
        ) -> Environment {
            let mut environment = Environment::new()
                .register_extension(descriptor.clone())
                .expect("register independent replay extension");
            for payload in payloads {
                environment = environment
                    .push_extension_entry(&descriptor.name, payload.as_slice())
                    .expect("replay exact raw payload");
            }
            environment
        }

        fn hex_payload(payload: &[u8]) -> String {
            use std::fmt::Write as _;

            let mut encoded = String::with_capacity(payload.len() * 2);
            for byte in payload {
                write!(&mut encoded, "{byte:02x}").expect("write to String cannot fail");
            }
            encoded
        }

        fn json_payloads(payloads: &[Vec<u8>]) -> String {
            let encoded = payloads
                .iter()
                .map(|payload| format!("\"{}\"", hex_payload(payload)))
                .collect::<Vec<_>>()
                .join(",");
            format!("[{encoded}]")
        }

        let run_id = std::env::var("FLN_ENV_E2E_RUN_ID")
            .unwrap_or_else(|_| "standalone-cargo-test".to_owned());
        assert!(
            run_id
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')),
            "E2E run id must be JSON-safe ASCII"
        );

        let extension_name = Name::str(Name::anonymous(), "e2eSetUnionExt");
        let descriptor = ExtensionDescriptor {
            name: extension_name.clone(),
            merge: MergeSemantics::SetUnion,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Understood,
        };
        let registered = Environment::new()
            .register_extension(descriptor.clone())
            .expect("register real SetUnion extension");
        let base_payloads: &[&[u8]] = &[b"base", b"base", b""];
        let ours_suffix: &[&[u8]] = &[b"x", b"x", b""];
        let theirs_suffix: &[&[u8]] = &[b"x", b"y", b"\0"];
        let base = append_environment(registered, &extension_name, base_payloads);
        let ours = append_environment(base.clone(), &extension_name, ours_suffix);
        let theirs = append_environment(base.clone(), &extension_name, theirs_suffix);
        let base_state = base.extension(&extension_name).expect("base state exists");
        let ours_state = ours.extension(&extension_name).expect("ours state exists");
        let theirs_state = theirs
            .extension(&extension_name)
            .expect("theirs state exists");

        let e2e_limits = SetUnionLimits::new(9, 13, 4);
        let (merged, merge_facts) =
            match ExtensionState::merge(base_state, ours_state, theirs_state, e2e_limits)
                .expect("real SetUnion histories do not conflict")
            {
                ExtensionMergeOutcome::Complete {
                    state,
                    set_union_facts: Some(facts),
                } => Some((state, facts)),
                _ => None,
            }
            .expect("real SetUnion merge must complete");
        let (reversed, reversed_facts) =
            match ExtensionState::merge(base_state, theirs_state, ours_state, e2e_limits)
                .expect("branch-permuted SetUnion histories do not conflict")
            {
                ExtensionMergeOutcome::Complete {
                    state,
                    set_union_facts: Some(facts),
                } => Some((state, facts)),
                _ => None,
            }
            .expect("branch-permuted SetUnion merge must complete");
        assert_eq!(merge_facts, reversed_facts);
        assert!(
            ours_suffix < theirs_suffix,
            "the independent expected model fixes this case as ours then theirs"
        );
        let expected_raw = [base_payloads, ours_suffix, theirs_suffix]
            .into_iter()
            .flatten()
            .map(|payload| payload.to_vec())
            .collect::<Vec<_>>();
        let expected_semantic = vec![
            b"base".to_vec(),
            b"".to_vec(),
            b"x".to_vec(),
            b"y".to_vec(),
            b"\0".to_vec(),
        ];
        let actual_raw = raw_payloads(&merged);
        let reversed_raw = raw_payloads(&reversed);
        let actual_semantic = semantic_payloads(&merged);
        assert_eq!(actual_raw, expected_raw, "raw replay must be byte-lossless");
        assert_eq!(actual_semantic, expected_semantic);
        assert_eq!(reversed_raw, expected_raw);
        assert_eq!(merged.content_digest(), reversed.content_digest());

        let expected_environment = replay_environment(&descriptor, &expected_raw);
        let actual_environment = replay_environment(&descriptor, &actual_raw);
        let reversed_environment = replay_environment(&descriptor, &reversed_raw);
        let expected_root = expected_environment.logical_root(&KVMap::new());
        let actual_root = actual_environment.logical_root(&KVMap::new());
        let reversed_root = reversed_environment.logical_root(&KVMap::new());
        assert_eq!(actual_root, expected_root);
        assert_eq!(reversed_root, expected_root);

        let duplicate_entries = actual_raw.len() - actual_semantic.len();
        let configured_max_entries = merge_facts.limits.max_entries;
        let configured_max_payload_bytes = merge_facts.limits.max_payload_bytes;
        let configured_max_entry_bytes = merge_facts.limits.max_entry_bytes;
        let consumed_entries = merge_facts.examined_entries;
        let consumed_payload_bytes = merge_facts.examined_payload_bytes;
        let consumed_maximum_entry_bytes = merge_facts.maximum_entry_bytes;
        println!(
            "{{\"schema\":\"fln.e2e.set-union\",\"version\":1,\"run_id\":\"{run_id}\",\"bead\":\"fln-amv.6\",\"scenario\":\"raw-semantic-split\",\"status\":\"pass\",\"reference_pin\":\"leanprover/lean4@8c9756b28d64dab099da31a4c09229a9e6a2ef35\",\"reference_sources\":[\"vendor/lean4-src/src/Lean/Environment.lean:1519-1620\",\"vendor/lean4-src/src/Lean/EnvExtension.lean:17-59\"],\"fixture_sources\":[\"tribunal/fixtures/c3/FINDINGS.md\",\"tribunal/fixtures/c3/MANIFEST.txt\"],\"fixture_census\":{{\"modules\":2433,\"extension_entries\":832903,\"integrity_faults\":0}},\"equality_key\":\"exact_payload_bytes\",\"semantic_selection\":\"stable_first_occurrence\",\"raw_branch_order\":\"canonical_lexicographic_suffix\",\"case_branch_order\":\"ours_then_theirs\",\"configured_resources\":{{\"max_entries\":{configured_max_entries},\"max_payload_bytes\":{configured_max_payload_bytes},\"max_entry_bytes\":{configured_max_entry_bytes}}},\"consumed_resources\":{{\"entries\":{consumed_entries},\"payload_bytes\":{consumed_payload_bytes},\"maximum_entry_bytes\":{consumed_maximum_entry_bytes}}},\"base_raw\":{},\"ours_suffix\":{},\"theirs_suffix\":{},\"expected_raw\":{},\"actual_raw\":{},\"expected_semantic\":{},\"actual_semantic\":{},\"raw_entry_count\":{},\"semantic_entry_count\":{},\"duplicate_entries_replayed\":{duplicate_entries},\"expected_digest\":\"{}\",\"actual_digest\":\"{}\",\"expected_root\":\"{expected_root}\",\"actual_root\":\"{actual_root}\",\"terminal_outcome\":\"complete\",\"final_state\":\"verified\"}}",
            json_payloads(
                &base_payloads
                    .iter()
                    .map(|payload| payload.to_vec())
                    .collect::<Vec<_>>()
            ),
            json_payloads(
                &ours_suffix
                    .iter()
                    .map(|payload| payload.to_vec())
                    .collect::<Vec<_>>()
            ),
            json_payloads(
                &theirs_suffix
                    .iter()
                    .map(|payload| payload.to_vec())
                    .collect::<Vec<_>>()
            ),
            json_payloads(&expected_raw),
            json_payloads(&actual_raw),
            json_payloads(&expected_semantic),
            json_payloads(&actual_semantic),
            actual_raw.len(),
            actual_semantic.len(),
            expected_environment
                .extension(&extension_name)
                .expect("expected extension exists")
                .content_digest(),
            merged.content_digest(),
        );

        let forward_order_hash = evidence_order_hash(actual_raw.iter().map(Vec::as_slice));
        let reversed_order_hash = evidence_order_hash(reversed_raw.iter().map(Vec::as_slice));
        println!(
            "{{\"schema\":\"fln.e2e.set-union\",\"version\":1,\"run_id\":\"{run_id}\",\"bead\":\"fln-amv.6\",\"scenario\":\"branch-permutation\",\"status\":\"pass\",\"forward_raw\":{},\"reversed_raw\":{},\"forward_order_hash\":\"{forward_order_hash:016x}\",\"reversed_order_hash\":\"{reversed_order_hash:016x}\",\"forward_root\":\"{actual_root}\",\"reversed_root\":\"{reversed_root}\",\"product_equal\":true,\"root_equal\":true,\"final_state\":\"verified\"}}",
            json_payloads(&actual_raw),
            json_payloads(&reversed_raw),
        );

        let options = KVMap::new();
        let base_root_before_exhaustion = base.logical_root(&options);
        let ours_root_before_exhaustion = ours.logical_root(&options);
        let theirs_root_before_exhaustion = theirs.logical_root(&options);
        let exhaustion_limits = SetUnionLimits::new(9, 13, 3);
        let (exhaustion_reason, exhaustion_facts) =
            match ExtensionState::merge(base_state, ours_state, theirs_state, exhaustion_limits)
                .expect("resource exhaustion is not a semantic conflict")
            {
                ExtensionMergeOutcome::Inconclusive { reason, facts } => Some((reason, facts)),
                ExtensionMergeOutcome::Complete { .. } => None,
            }
            .expect("over-limit SetUnion merge must be inconclusive");
        assert_eq!(exhaustion_reason.resource, SetUnionResource::EntryBytes);
        assert_eq!((exhaustion_reason.limit, exhaustion_reason.actual), (3, 4));
        assert_eq!(base.logical_root(&options), base_root_before_exhaustion);
        assert_eq!(ours.logical_root(&options), ours_root_before_exhaustion);
        assert_eq!(theirs.logical_root(&options), theirs_root_before_exhaustion);
        let recovered_after_exhaustion =
            match ExtensionState::merge(base_state, ours_state, theirs_state, e2e_limits)
                .expect("within-budget recovery is not a semantic conflict")
            {
                ExtensionMergeOutcome::Complete { state, .. } => Some(state),
                ExtensionMergeOutcome::Inconclusive { .. } => None,
            }
            .expect("within-budget retry must recover");
        assert_eq!(recovered_after_exhaustion, merged);
        let exhausted_max_entries = exhaustion_facts.limits.max_entries;
        let exhausted_max_payload_bytes = exhaustion_facts.limits.max_payload_bytes;
        let exhausted_max_entry_bytes = exhaustion_facts.limits.max_entry_bytes;
        let exhausted_entries = exhaustion_facts.examined_entries;
        let exhausted_payload_bytes = exhaustion_facts.examined_payload_bytes;
        let exhausted_maximum_entry_bytes = exhaustion_facts.maximum_entry_bytes;
        println!(
            "{{\"schema\":\"fln.e2e.set-union\",\"version\":1,\"run_id\":\"{run_id}\",\"bead\":\"fln-amv.6\",\"scenario\":\"resource-exhaustion-clean-recovery\",\"status\":\"pass\",\"configured_resources\":{{\"max_entries\":{exhausted_max_entries},\"max_payload_bytes\":{exhausted_max_payload_bytes},\"max_entry_bytes\":{exhausted_max_entry_bytes}}},\"consumed_resources\":{{\"entries\":{exhausted_entries},\"payload_bytes\":{exhausted_payload_bytes},\"maximum_entry_bytes\":{exhausted_maximum_entry_bytes}}},\"raw_entry_count\":{},\"raw_payload_bytes\":{},\"partial_semantic_count\":{},\"partial_duplicate_decisions\":{},\"expected_outcome\":\"inconclusive\",\"actual_outcome\":\"inconclusive\",\"resource\":\"entry_bytes\",\"limit\":{},\"actual\":{},\"partial_product_published\":false,\"base_root_before\":\"{base_root_before_exhaustion}\",\"base_root_after\":\"{}\",\"ours_root_before\":\"{ours_root_before_exhaustion}\",\"ours_root_after\":\"{}\",\"theirs_root_before\":\"{theirs_root_before_exhaustion}\",\"theirs_root_after\":\"{}\",\"recovered_raw\":{},\"recovered_semantic\":{},\"recovered_root\":\"{actual_root}\",\"recovered_duplicate_decisions\":{},\"cleanup\":\"inputs_unchanged\",\"recovery_state\":\"within_budget_retry_complete\",\"terminal_outcome\":\"clean_recovery\",\"final_state\":\"clean_recovery\"}}",
            exhaustion_facts.raw_entries,
            exhaustion_facts.raw_payload_bytes,
            exhaustion_facts.semantic_entries,
            exhaustion_facts.duplicate_entries,
            exhaustion_reason.limit,
            exhaustion_reason.actual,
            base.logical_root(&options),
            ours.logical_root(&options),
            theirs.logical_root(&options),
            json_payloads(&actual_raw),
            json_payloads(&actual_semantic),
            merge_facts.duplicate_entries,
        );

        let mut one_sided_dedup_mutant = raw_payloads(ours_state);
        for payload in raw_payloads(theirs_state)
            .into_iter()
            .skip(base_state.len())
        {
            if !one_sided_dedup_mutant.contains(&payload) {
                one_sided_dedup_mutant.push(payload);
            }
        }
        let mutant_environment = replay_environment(&descriptor, &one_sided_dedup_mutant);
        let mutant_root = mutant_environment.logical_root(&KVMap::new());
        assert_ne!(one_sided_dedup_mutant, expected_raw);
        assert_ne!(mutant_root, expected_root);
        println!(
            "{{\"schema\":\"fln.e2e.set-union\",\"version\":1,\"run_id\":\"{run_id}\",\"bead\":\"fln-amv.6\",\"scenario\":\"one-sided-dedup-negative-recovery\",\"status\":\"pass\",\"mutant\":\"deduplicate_only_second_suffix\",\"expected_outcome\":\"mutant_diverges\",\"actual_outcome\":\"mutant_diverges\",\"mutant_raw\":{},\"recovered_raw\":{},\"mutant_root\":\"{mutant_root}\",\"recovered_root\":\"{actual_root}\",\"mutant_detected\":true,\"recovery_outcome\":\"lossless_merge_restored\",\"final_state\":\"clean_recovery\"}}",
            json_payloads(&one_sided_dedup_mutant),
            json_payloads(&actual_raw),
        );
    }

    #[test]
    fn extension_merge_refusals_e2e_emit_detailed_real_path_evidence() {
        fn replay_environment(descriptor: &ExtensionDescriptor, payloads: &[&[u8]]) -> Environment {
            let mut environment = Environment::new()
                .register_extension(descriptor.clone())
                .expect("register real extension contract");
            for payload in payloads {
                environment = environment
                    .push_extension_entry(&descriptor.name, *payload)
                    .expect("append through the real environment registry");
            }
            environment
        }

        let run_id = std::env::var("FLN_ENV_E2E_RUN_ID")
            .unwrap_or_else(|_| "standalone-cargo-test".to_owned());
        assert!(
            run_id
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')),
            "E2E run id must be JSON-safe ASCII"
        );
        let options = KVMap::new();
        let extension_name = Name::str(Name::anonymous(), "e2eMergeRefusalExt");
        let descriptor = ExtensionDescriptor {
            name: extension_name.clone(),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Understood,
        };

        let base = replay_environment(&descriptor, &[b"base"]);
        let ours = replay_environment(&descriptor, &[b"base", b"ours"]);
        let theirs = replay_environment(&descriptor, &[b"base", b"theirs"]);
        let mismatched_descriptor = ExtensionDescriptor {
            merge: MergeSemantics::SetUnion,
            ..descriptor.clone()
        };
        let mismatched = replay_environment(&mismatched_descriptor, &[b"base", b"ours"]);
        let base_root_before = base.logical_root(&options);
        let ours_root_before = ours.logical_root(&options);
        let mismatched_root_before = mismatched.logical_root(&options);
        let descriptor_error = merge_with_test_limits(
            base.extension(&extension_name)
                .expect("base extension exists"),
            mismatched
                .extension(&extension_name)
                .expect("mismatched extension exists"),
            theirs
                .extension(&extension_name)
                .expect("theirs extension exists"),
        )
        .expect_err("contract mismatch must be a typed refusal");
        assert!(matches!(
            descriptor_error,
            MergeConflict::DescriptorMismatch { .. }
        ));
        assert_eq!(base.logical_root(&options), base_root_before);
        assert_eq!(ours.logical_root(&options), ours_root_before);
        assert_eq!(mismatched.logical_root(&options), mismatched_root_before);

        let descriptor_recovered = merge_with_test_limits(
            base.extension(&extension_name)
                .expect("base extension exists"),
            ours.extension(&extension_name)
                .expect("ours extension exists"),
            base.extension(&extension_name)
                .expect("base extension exists"),
        )
        .expect("matching contracts recover cleanly");
        assert_eq!(
            raw_payloads(&descriptor_recovered),
            raw_payloads(
                ours.extension(&extension_name)
                    .expect("ours extension exists")
            )
        );
        println!(
            "{{\"schema\":\"fln.e2e.extension-merge-refusal\",\"version\":1,\"run_id\":\"{run_id}\",\"bead\":\"fln-amv.3\",\"scenario\":\"descriptor-mismatch-negative-recovery\",\"status\":\"pass\",\"mismatch_field\":\"merge_semantics\",\"base_contract\":{{\"name\":\"e2eMergeRefusalExt\",\"merge\":\"append_ordered\",\"checkpoint\":\"journal_suffix\",\"provenance\":\"understood\"}},\"ours_contract\":{{\"name\":\"e2eMergeRefusalExt\",\"merge\":\"set_union\",\"checkpoint\":\"journal_suffix\",\"provenance\":\"understood\"}},\"theirs_contract\":{{\"name\":\"e2eMergeRefusalExt\",\"merge\":\"append_ordered\",\"checkpoint\":\"journal_suffix\",\"provenance\":\"understood\"}},\"expected_outcome\":\"descriptor_mismatch\",\"actual_outcome\":\"descriptor_mismatch\",\"base_root_before\":\"{base_root_before}\",\"base_root_after\":\"{}\",\"ours_root_before\":\"{ours_root_before}\",\"ours_root_after\":\"{}\",\"invalid_root_before\":\"{mismatched_root_before}\",\"invalid_root_after\":\"{}\",\"input_mutation\":false,\"recovery_outcome\":\"matching_contract_merged\",\"recovered_digest\":\"{}\",\"final_state\":\"clean_recovery\"}}",
            base.logical_root(&options),
            ours.logical_root(&options),
            mismatched.logical_root(&options),
            descriptor_recovered.content_digest(),
        );

        let history_base = replay_environment(&descriptor, &[b"base-0", b"base-1"]);
        let history_ours = replay_environment(&descriptor, &[b"base-0", b"base-1", b"ours"]);
        let invalid_theirs = replay_environment(&descriptor, &[b"corrupt", b"base-1", b"theirs"]);
        let valid_theirs = replay_environment(&descriptor, &[b"base-0", b"base-1", b"theirs"]);
        let history_base_state = history_base
            .extension(&extension_name)
            .expect("history base extension exists");
        let history_ours_state = history_ours
            .extension(&extension_name)
            .expect("history ours extension exists");
        let invalid_theirs_state = invalid_theirs
            .extension(&extension_name)
            .expect("invalid theirs extension exists");
        let history_base_root_before = history_base.logical_root(&options);
        let history_ours_root_before = history_ours.logical_root(&options);
        let invalid_theirs_root_before = invalid_theirs.logical_root(&options);
        let history_error =
            merge_with_test_limits(history_base_state, history_ours_state, invalid_theirs_state)
                .expect_err("unrelated history must be a typed refusal");
        assert!(
            matches!(&history_error, MergeConflict::HistoryMismatch { .. }),
            "unexpected merge refusal: {history_error:?}"
        );
        let MergeConflict::HistoryMismatch {
            base_len: reported_base_len,
            ours_len: reported_ours_len,
            theirs_len: reported_theirs_len,
            ours_common_prefix: reported_ours_common_prefix,
            theirs_common_prefix: reported_theirs_common_prefix,
            ..
        } = history_error
        else {
            return;
        };
        assert_eq!(reported_base_len, 2);
        assert_eq!(reported_ours_len, 3);
        assert_eq!(reported_theirs_len, 3);
        assert_eq!(reported_ours_common_prefix, 2);
        assert_eq!(reported_theirs_common_prefix, 0);
        assert_eq!(
            history_base.logical_root(&options),
            history_base_root_before
        );
        assert_eq!(
            history_ours.logical_root(&options),
            history_ours_root_before
        );
        assert_eq!(
            invalid_theirs.logical_root(&options),
            invalid_theirs_root_before
        );

        let history_recovered = merge_with_test_limits(
            history_base_state,
            history_ours_state,
            valid_theirs
                .extension(&extension_name)
                .expect("valid theirs extension exists"),
        )
        .expect("valid descendant histories recover cleanly");
        let recovered_raw = raw_payloads(&history_recovered);
        assert_eq!(
            recovered_raw,
            vec![
                b"base-0".to_vec(),
                b"base-1".to_vec(),
                b"ours".to_vec(),
                b"theirs".to_vec(),
            ]
        );
        println!(
            "{{\"schema\":\"fln.e2e.extension-merge-refusal\",\"version\":1,\"run_id\":\"{run_id}\",\"bead\":\"fln-amv.4\",\"scenario\":\"history-mismatch-negative-recovery\",\"status\":\"pass\",\"invalid_branch\":\"theirs\",\"expected_outcome\":\"history_mismatch\",\"actual_outcome\":\"history_mismatch\",\"base_len\":{reported_base_len},\"ours_len\":{reported_ours_len},\"theirs_len\":{reported_theirs_len},\"ours_common_prefix\":{reported_ours_common_prefix},\"theirs_common_prefix\":{reported_theirs_common_prefix},\"base_root_before\":\"{history_base_root_before}\",\"base_root_after\":\"{}\",\"ours_root_before\":\"{history_ours_root_before}\",\"ours_root_after\":\"{}\",\"invalid_root_before\":\"{invalid_theirs_root_before}\",\"invalid_root_after\":\"{}\",\"input_mutation\":false,\"recovery_outcome\":\"valid_descendants_merged\",\"recovered_order_hash\":\"{:016x}\",\"recovered_digest\":\"{}\",\"final_state\":\"clean_recovery\"}}",
            history_base.logical_root(&options),
            history_ours.logical_root(&options),
            invalid_theirs.logical_root(&options),
            evidence_order_hash(recovered_raw.iter().map(Vec::as_slice)),
            history_recovered.content_digest(),
        );
    }

    #[test]
    fn review_required_merges_are_typed_conflicts_never_silent() {
        let base = ExtensionState::new(descriptor(
            MergeSemantics::ConflictsRequireReview,
            PayloadProvenance::Understood,
        ));
        let ours = base.push_entry(bytes(b"o"));
        let theirs = base.push_entry(bytes(b"t"));
        let conflict = merge_with_test_limits(&base, &ours, &theirs).expect_err("both changed");
        assert_eq!(
            conflict,
            MergeConflict::ConcurrentChanges {
                extension: Name::str(Name::anonymous(), "simpExt"),
            }
        );
        // One-sided changes pass through unchanged.
        let one_sided =
            merge_with_test_limits(&base, &ours, &base).expect("one-sided change is safe");
        assert_eq!(one_sided.len(), 1);
    }

    #[test]
    fn mismatched_descriptors_are_typed_conflicts_on_either_branch() {
        let expected = descriptor(MergeSemantics::AppendOrdered, PayloadProvenance::Understood);
        let base = ExtensionState::new(expected.clone()).push_entry(bytes(b"base"));
        let matching = base.push_entry(bytes(b"matching"));
        let variants = [
            ExtensionDescriptor {
                name: Name::str(Name::anonymous(), "otherExt"),
                ..expected.clone()
            },
            ExtensionDescriptor {
                merge: MergeSemantics::SetUnion,
                ..expected.clone()
            },
            ExtensionDescriptor {
                checkpoint: CheckpointSemantics::FullJournal,
                ..expected.clone()
            },
            ExtensionDescriptor {
                provenance: PayloadProvenance::Opaque,
                ..expected.clone()
            },
        ];

        for variant in variants {
            let mismatched = ExtensionState::new(variant.clone()).push_entry(bytes(b"mismatched"));
            let before = (base.clone(), matching.clone(), mismatched.clone());

            let ours_error = merge_with_test_limits(&base, &mismatched, &matching)
                .expect_err("ours contract mismatch is refused");
            assert_eq!(
                ours_error,
                MergeConflict::DescriptorMismatch {
                    base: expected.clone(),
                    ours: variant.clone(),
                    theirs: expected.clone(),
                }
            );

            let theirs_error = merge_with_test_limits(&base, &matching, &mismatched)
                .expect_err("theirs contract mismatch is refused");
            assert_eq!(
                theirs_error,
                MergeConflict::DescriptorMismatch {
                    base: expected.clone(),
                    ours: expected.clone(),
                    theirs: variant,
                }
            );

            assert_eq!(
                (base.clone(), matching.clone(), mismatched),
                before,
                "a refused merge leaves every input unchanged"
            );
        }
    }

    #[test]
    fn invalid_branch_history_is_a_typed_conflict() {
        let expected = descriptor(MergeSemantics::AppendOrdered, PayloadProvenance::Understood);
        let base = ExtensionState::new(expected.clone())
            .push_entry(bytes(b"a"))
            .push_entry(bytes(b"b"));
        let matching = base.push_entry(bytes(b"c"));
        let invalid_histories = [
            (
                "shorter branch",
                ExtensionState::new(expected.clone()).push_entry(bytes(b"a")),
                1,
            ),
            (
                "first entry differs",
                ExtensionState::new(expected.clone())
                    .push_entry(bytes(b"x"))
                    .push_entry(bytes(b"b")),
                0,
            ),
            (
                "same-length later entry differs",
                ExtensionState::new(expected.clone())
                    .push_entry(bytes(b"a"))
                    .push_entry(bytes(b"x")),
                1,
            ),
            (
                "longer history diverges before the base ends",
                ExtensionState::new(expected.clone())
                    .push_entry(bytes(b"a"))
                    .push_entry(bytes(b"x"))
                    .push_entry(bytes(b"c")),
                1,
            ),
        ];

        for (case, invalid, common_prefix) in invalid_histories {
            let before = (base.clone(), matching.clone(), invalid.clone());
            assert_eq!(
                merge_with_test_limits(&base, &invalid, &matching)
                    .expect_err("invalid ours history is refused"),
                MergeConflict::HistoryMismatch {
                    extension: expected.name.clone(),
                    base_len: 2,
                    ours_len: invalid.len(),
                    theirs_len: 3,
                    ours_common_prefix: common_prefix,
                    theirs_common_prefix: 2,
                },
                "{case}"
            );
            assert_eq!(
                merge_with_test_limits(&base, &matching, &invalid)
                    .expect_err("invalid theirs history is refused"),
                MergeConflict::HistoryMismatch {
                    extension: expected.name.clone(),
                    base_len: 2,
                    ours_len: 3,
                    theirs_len: invalid.len(),
                    ours_common_prefix: 2,
                    theirs_common_prefix: common_prefix,
                },
                "{case}"
            );
            assert_eq!(
                (base.clone(), matching.clone(), invalid),
                before,
                "{case} leaves every input unchanged"
            );
        }

        let invalid_ours = ExtensionState::new(expected.clone());
        let invalid_theirs = ExtensionState::new(expected.clone()).push_entry(bytes(b"x"));
        assert_eq!(
            merge_with_test_limits(&base, &invalid_ours, &invalid_theirs)
                .expect_err("both invalid histories are refused together"),
            MergeConflict::HistoryMismatch {
                extension: expected.name,
                base_len: 2,
                ours_len: 0,
                theirs_len: 1,
                ours_common_prefix: 0,
                theirs_common_prefix: 0,
            }
        );
    }

    #[test]
    fn suffix_checkpoints_round_trip_empty_nested_and_repeated_restores() {
        let base = state_with_checkpoint(37, CheckpointSemantics::JournalSuffix);
        let unchanged = base
            .checkpoint(Some(&base), TEST_LIMITS)
            .expect("empty suffix captures");
        assert_eq!(unchanged.schema_version(), 1);
        assert_eq!(unchanged.mode(), CheckpointSemantics::JournalSuffix);
        assert_eq!(unchanged.base_len(), Some(37));
        assert_eq!(unchanged.captured_entries(), 0);
        assert_eq!(unchanged.captured_payload_bytes(), 0);
        assert_eq!(unchanged.entries().count(), 0);
        assert_eq!(
            ExtensionState::restore(Some(&base), &unchanged, TEST_LIMITS)
                .expect("empty suffix restores"),
            base
        );

        let middle = base
            .push_entry(bytes(b"middle-a"))
            .push_entry(bytes(b"middle-b"));
        let final_state = middle
            .push_entry(bytes(b"final-a"))
            .push_entry(bytes(b"final-b"))
            .push_entry(bytes(b"final-c"));
        let first = middle
            .checkpoint(Some(&base), TEST_LIMITS)
            .expect("first nested checkpoint captures");
        let second = final_state
            .checkpoint(Some(&middle), TEST_LIMITS)
            .expect("second nested checkpoint captures");

        let restored_middle =
            ExtensionState::restore(Some(&base), &first, TEST_LIMITS).expect("middle restores");
        let restored_final = ExtensionState::restore(Some(&restored_middle), &second, TEST_LIMITS)
            .expect("nested final restores");
        let restored_again = ExtensionState::restore(Some(&restored_middle), &second, TEST_LIMITS)
            .expect("repeated restore is deterministic");
        assert_eq!(restored_middle, middle);
        assert_eq!(restored_final, final_state);
        assert_eq!(restored_again, final_state);
        assert_eq!(
            restored_final.content_digest(),
            final_state.content_digest()
        );
        assert_eq!(restored_final.descriptor, final_state.descriptor);
    }

    #[test]
    fn full_checkpoints_are_self_contained_and_refuse_ambient_bases() {
        let state = state_with_checkpoint(73, CheckpointSemantics::FullJournal);
        let checkpoint = state
            .checkpoint(None, TEST_LIMITS)
            .expect("full journal captures without base");
        assert_eq!(checkpoint.mode(), CheckpointSemantics::FullJournal);
        assert_eq!(checkpoint.base_len(), None);
        assert_eq!(checkpoint.base_state_digest(), None);
        assert_eq!(checkpoint.captured_entries(), state.len());
        assert_eq!(checkpoint.entries().count(), state.len());
        assert_eq!(
            checkpoint.captured_payload_bytes(),
            state.journal.payload_bytes
        );
        let restored = ExtensionState::restore(None, &checkpoint, TEST_LIMITS)
            .expect("full journal restores without base");
        assert_eq!(restored, state);
        assert_eq!(restored.content_digest(), state.content_digest());

        assert_eq!(
            state
                .checkpoint(Some(&state), TEST_LIMITS)
                .expect_err("full capture refuses a base"),
            CheckpointError::UnexpectedBase {
                extension: state.descriptor.name.clone(),
            }
        );
        assert_eq!(
            ExtensionState::restore(Some(&state), &checkpoint, TEST_LIMITS)
                .expect_err("full restore refuses a base"),
            CheckpointError::UnexpectedBase {
                extension: state.descriptor.name.clone(),
            }
        );
    }

    #[test]
    fn suffix_capture_refuses_every_invalid_base_atomically() {
        let target = state_with_checkpoint(3, CheckpointSemantics::JournalSuffix);
        assert_eq!(
            target
                .checkpoint(None, TEST_LIMITS)
                .expect_err("suffix capture requires a base"),
            CheckpointError::MissingBase {
                extension: target.descriptor.name.clone(),
            }
        );

        let wrong_name = ExtensionState::new(ExtensionDescriptor {
            name: Name::str(Name::anonymous(), "otherExt"),
            ..target.descriptor.clone()
        });
        assert_eq!(
            target
                .checkpoint(Some(&wrong_name), TEST_LIMITS)
                .expect_err("wrong extension is refused"),
            CheckpointError::ExtensionNameMismatch {
                expected: target.descriptor.name.clone(),
                actual: wrong_name.descriptor.name.clone(),
            }
        );

        for mismatched in [
            ExtensionDescriptor {
                merge: MergeSemantics::SetUnion,
                ..target.descriptor.clone()
            },
            ExtensionDescriptor {
                checkpoint: CheckpointSemantics::FullJournal,
                ..target.descriptor.clone()
            },
            ExtensionDescriptor {
                provenance: PayloadProvenance::Opaque,
                ..target.descriptor.clone()
            },
        ] {
            let base = ExtensionState::new(mismatched.clone());
            assert_eq!(
                target
                    .checkpoint(Some(&base), TEST_LIMITS)
                    .expect_err("contract mismatch is refused"),
                CheckpointError::ContractMismatch {
                    expected: target.descriptor.clone(),
                    actual: mismatched,
                }
            );
        }

        let divergent = ExtensionState::new(target.descriptor.clone())
            .push_entry(bytes(&0u64.to_le_bytes()))
            .push_entry(bytes(b"different"));
        let before = (target.clone(), divergent.clone());
        assert_eq!(
            target
                .checkpoint(Some(&divergent), TEST_LIMITS)
                .expect_err("divergent branch is refused"),
            CheckpointError::HistoryMismatch {
                extension: target.descriptor.name.clone(),
                base_len: 2,
                target_len: 3,
                common_prefix: 1,
            }
        );
        assert_eq!((target, divergent), before, "refusal mutates no snapshot");
    }

    /// An independently rebuilt, content-identical base SUCCEEDS.
    ///
    /// This is the first of the two discriminating tests. Allocation lineage is not
    /// semantic identity: a base rebuilt from scratch shares no journal node with the
    /// one the checkpoint was captured against, so the O(1) structural proof fails and
    /// the exact comparison has to carry it. If restore only accepted the original
    /// handle it would be enforcing allocation identity, which is the defect in the
    /// other direction.
    #[test]
    fn a_content_identical_independently_rebuilt_base_restores() {
        let captured_base = state_with_checkpoint(3, CheckpointSemantics::JournalSuffix);
        let target = captured_base.push_entry(bytes(b"suffix"));
        let checkpoint = target
            .checkpoint(Some(&captured_base), TEST_LIMITS)
            .expect("checkpoint captures");

        // Rebuilt from scratch: same descriptor, same entries, no shared nodes.
        let rebuilt = state_with_checkpoint(3, CheckpointSemantics::JournalSuffix);
        assert_eq!(rebuilt.content_digest(), captured_base.content_digest());
        assert!(
            !rebuilt.journal.is_same_structure(&captured_base.journal),
            "the rebuilt base must not share structure, or this proves nothing"
        );

        let restored = ExtensionState::restore(Some(&rebuilt), &checkpoint, TEST_LIMITS)
            .expect("a content-identical rebuilt base must restore");
        let expected = ExtensionState::restore(Some(&captured_base), &checkpoint, TEST_LIMITS)
            .expect("the original base restores");
        assert_eq!(restored.content_digest(), expected.content_digest());
        assert_eq!(restored, expected);

        // A sibling base — reached by a different path but content-identical — is the
        // same requirement stated the way a caller meets it in practice.
        let sibling = state_with_checkpoint(2, CheckpointSemantics::JournalSuffix)
            .push_entry(bytes(&2u64.to_le_bytes()));
        assert_eq!(sibling.content_digest(), captured_base.content_digest());
        assert!(
            !sibling.journal.is_same_structure(&captured_base.journal),
            "a sibling reached by a different path must not share structure"
        );
        assert_eq!(
            ExtensionState::restore(Some(&sibling), &checkpoint, TEST_LIMITS)
                .expect("a sibling base must restore")
                .content_digest(),
            expected.content_digest()
        );

        // Boundaries, because one length proves one length. Empty and singleton bases
        // are where an off-by-one in the comparison or a wrong empty-journal identity
        // would hide: an empty base has no root node at all, so structural identity
        // there is a different code path from the shared-node one.
        for base_len in 0..5usize {
            let original = state_with_checkpoint(base_len, CheckpointSemantics::JournalSuffix);
            let grown = original.push_entry(bytes(b"boundary-suffix"));
            let captured = grown.checkpoint(Some(&original), TEST_LIMITS);
            assert!(
                captured.is_ok(),
                "capture must succeed at base_len {base_len}: {captured:?}"
            );
            let point = captured.expect("asserted just above");
            let independent = state_with_checkpoint(base_len, CheckpointSemantics::JournalSuffix);
            assert_eq!(
                independent.content_digest(),
                original.content_digest(),
                "the rebuilt base must be content-identical at base_len {base_len}"
            );
            let outcome = ExtensionState::restore(Some(&independent), &point, TEST_LIMITS);
            assert!(
                outcome.is_ok(),
                "a rebuilt base must restore at base_len {base_len}: {outcome:?}"
            );
            let restored = outcome.expect("asserted just above");
            assert_eq!(
                restored.content_digest(),
                grown.content_digest(),
                "restoring a rebuilt base must reproduce the captured target at base_len \
                 {base_len}"
            );
            assert_eq!(
                point.retained_base_facts().map(|facts| facts.entries),
                Some(base_len),
                "the retained footprint must report the real base length"
            );
        }
    }

    /// Equal-length and equal-digest UNEQUAL histories FAIL.
    ///
    /// The second discriminating test, and the one that makes the whole bead's claim
    /// load-bearing: a recorded digest can only reject, so a base that satisfies every
    /// recorded digest must still be refused when its history differs.
    #[test]
    fn equal_length_and_equal_digest_unequal_histories_are_refused() {
        let captured_base = state_with_checkpoint(3, CheckpointSemantics::JournalSuffix);
        let target = captured_base.push_entry(bytes(b"suffix"));
        let checkpoint = target
            .checkpoint(Some(&captured_base), TEST_LIMITS)
            .expect("checkpoint captures");

        // Same length, different contents: the digest fast path is enough here, and the
        // point of asserting it is that the cheap rejection still happens.
        let mut equal_length = ExtensionState::new(descriptor_with_checkpoint(
            CheckpointSemantics::JournalSuffix,
        ));
        for index in 0..3u64 {
            equal_length = equal_length.push_entry(bytes(&(index + 100).to_le_bytes()));
        }
        assert_eq!(equal_length.len(), captured_base.len());
        assert_ne!(
            equal_length.content_digest(),
            captured_base.content_digest()
        );
        let refused = ExtensionState::restore(Some(&equal_length), &checkpoint, TEST_LIMITS)
            .expect_err("an equal-length different history must be refused");
        assert!(
            matches!(
                refused,
                CheckpointError::BaseHistoryMismatch { .. }
                    | CheckpointError::BaseDigestMismatch { .. }
            ),
            "expected a digest-level rejection, got {refused:?}"
        );

        // Now the case the digests CANNOT catch, simulated through the bounded seam:
        // the recorded digests are forged to match this wrong base exactly, so every
        // fast path accepts and only the exact comparison can refuse.
        let colliding = checkpoint.clone().forge_recorded_base_digests(
            equal_length.journal.digest,
            equal_length.content_digest(),
        );
        let caught = ExtensionState::restore(Some(&equal_length), &colliding, TEST_LIMITS)
            .expect_err("an equal-digest different history must still be refused");
        let CheckpointError::BaseNotExact {
            base_len,
            first_divergence,
            ..
        } = &caught
        else {
            unreachable!("expected the exact comparison to refuse, got {caught:?}")
        };
        assert_eq!(*base_len, 3);
        assert_eq!(
            *first_divergence, 0,
            "the divergence index must name where the histories actually parted"
        );

        // And the same forged checkpoint against the RIGHT base still succeeds, so the
        // refusal above is discriminating rather than the seam breaking everything.
        assert!(
            ExtensionState::restore(Some(&captured_base), &colliding, TEST_LIMITS).is_err(),
            "forged digests do not match the real base, so its fast path rejects"
        );
        let honest = ExtensionState::restore(Some(&captured_base), &checkpoint, TEST_LIMITS);
        assert!(honest.is_ok(), "the unforged checkpoint restores normally");

        // A collision that diverges LATE, which is the case that actually exercises the
        // comparison loop rather than its first iteration. Two bases sharing a two-entry
        // prefix and differing only at the last entry, with the digests forged to agree:
        // the refusal must name entry 2, not entry 0, or the divergence index is
        // decoration rather than a fact a caller can act on.
        let mut shared_prefix = ExtensionState::new(descriptor_with_checkpoint(
            CheckpointSemantics::JournalSuffix,
        ));
        for index in 0..2u64 {
            shared_prefix = shared_prefix.push_entry(bytes(&index.to_le_bytes()));
        }
        let late_divergent = shared_prefix.push_entry(bytes(b"diverges-here"));
        assert_eq!(late_divergent.len(), captured_base.len());
        assert_eq!(
            first_entry_divergence(&captured_base, &late_divergent),
            Some(2),
            "the two bases must share exactly a two-entry prefix"
        );
        let late_collision = checkpoint.clone().forge_recorded_base_digests(
            late_divergent.journal.digest,
            late_divergent.content_digest(),
        );
        let late_caught =
            ExtensionState::restore(Some(&late_divergent), &late_collision, TEST_LIMITS)
                .expect_err("a late-diverging equal-digest history must still be refused");
        let CheckpointError::BaseNotExact {
            first_divergence: late_index,
            ..
        } = &late_caught
        else {
            unreachable!("expected the exact comparison to refuse, got {late_caught:?}")
        };
        assert_eq!(
            *late_index, 2,
            "the reported divergence must be where the histories actually parted"
        );

        eprintln!(
            "{{\"schema\":\"fln.unit.checkpoint-base-identity\",\"version\":1,\
             \"bead\":\"fln-extension-history-checkpoint-identity-41s\",\
             \"claim_type\":\"bounded_model\",\
             \"scenario\":\"digest-is-accelerator-not-proof\",\
             \"equal_length_unequal_history\":\"refused_by_digest_accelerator\",\
             \"equal_digest_unequal_history_divergence_0\":\"refused_by_exact_comparison\",\
             \"equal_digest_unequal_history_divergence_2\":\"refused_by_exact_comparison\",\
             \"reported_divergence_indices\":[0,2],\
             \"collision_source\":\"bounded_test_seam_forging_recorded_digests_only\",\
             \"unforged_checkpoint_still_restores\":true,\"status\":\"pass\"}}"
        );
    }

    /// Epoch and ordered entry ids are bound at CAPTURE time, and the binding
    /// discriminates.
    ///
    /// The decision this implements, recorded on the bead before the code was written:
    /// capture-time binding, rejecting restore-time derivation from a caller-supplied
    /// epoch. The reason for rejecting it is that a checkpoint which cannot state its own
    /// epoch is not self-contained, and a wrong-epoch restore would then surface as a
    /// wrong-VALUE mismatch rather than a wrong-EPOCH one — a worse diagnostic for the same
    /// defect, and the diagnostic collapse this bead keeps objecting to.
    ///
    /// The binding is by DERIVATION, not comparison: epoch is an input to every
    /// [`ExtensionEntryId`], so the same payloads under a different epoch produce different
    /// ids. That makes reading a checkpoint from one epoch as one from another impossible
    /// rather than merely inadvisable.
    #[test]
    fn capture_binds_the_epoch_and_ordered_entry_ids() {
        let state = state_with_checkpoint(4, CheckpointSemantics::FullJournal);
        let here = fixture_epoch();
        let elsewhere = ModuleEpoch::new("v4.33.0", "1111111111111111111111111111111111111111");
        assert_ne!(here, elsewhere);

        let capture = |epoch: &ModuleEpoch, from: &ExtensionState| {
            from.try_checkpoint(None, TEST_LIMITS, ProofBudget::UNBOUNDED, epoch, None)
                .into_complete()
                .expect("capture completes")
                .expect("capture succeeds")
        };
        let mine = capture(&here, &state);
        let theirs = capture(&elsewhere, &state);

        // The checkpoint states its own epoch — the point of capture-time binding.
        assert_eq!(mine.epoch(), &here);
        assert_eq!(theirs.epoch(), &elsewhere);
        assert_eq!(mine.entry_ids().len(), state.len());

        // SAME payloads, DIFFERENT epoch, DIFFERENT ids — pairwise, so a reordering could
        // not pass either.
        for (ours, others) in mine.entry_ids().iter().zip(theirs.entry_ids()) {
            assert_ne!(
                ours, others,
                "an entry id must depend on the epoch, or the epoch is not bound"
            );
        }
        assert_ne!(mine, theirs, "the checkpoints must differ by epoch alone");

        // Order is bound: reversing the entries changes the id SEQUENCE while leaving the
        // id SET identical, so only order distinguishes them.
        let payloads: Vec<Arc<[u8]>> = state
            .entries()
            .map(|entry| Arc::clone(&entry.payload))
            .collect();
        let mut reversed = ExtensionState::new(state.descriptor.clone());
        for payload in payloads.iter().rev() {
            reversed = reversed.push_entry(Arc::clone(payload));
        }
        let reversed_point = capture(&here, &reversed);
        assert_ne!(
            mine.entry_ids(),
            reversed_point.entry_ids(),
            "the id sequence must be order-sensitive"
        );
        let ours: HashSet<&ExtensionEntryId> = mine.entry_ids().iter().collect();
        let permuted: HashSet<&ExtensionEntryId> = reversed_point.entry_ids().iter().collect();
        assert_eq!(
            ours, permuted,
            "the same entries must yield the same id set"
        );

        // Each restores under its own epoch, because restore re-derives with the
        // checkpoint's own epoch rather than an ambient one.
        for point in [&mine, &theirs, &reversed_point] {
            assert!(
                ExtensionState::restore(None, point, TEST_LIMITS).is_ok(),
                "a checkpoint must restore under the epoch it was captured with"
            );
        }

        // A changed payload changes its id, which is what makes the recorded ids a check
        // rather than a decoration.
        let mut tampered = ExtensionState::new(state.descriptor.clone());
        for (index, payload) in payloads.iter().enumerate() {
            tampered = if index == 2 {
                tampered.push_entry(bytes(b"tampered"))
            } else {
                tampered.push_entry(Arc::clone(payload))
            };
        }
        let tampered_point = capture(&here, &tampered);
        assert_ne!(
            mine.entry_ids()[2],
            tampered_point.entry_ids()[2],
            "a changed payload must change its id"
        );

        // THE CHECK FIRES. Capture always derives consistently, so the restore-side
        // comparison can only be exercised through a seam — and a check nothing can make
        // fire is unfalsifiable, which is the standard this bead applies everywhere else.
        let forged = mine
            .clone()
            .forge_entry_ids(theirs.entry_ids().to_vec().into());
        let caught = ExtensionState::restore(None, &forged, TEST_LIMITS)
            .expect_err("ids that do not re-derive must be refused");
        let CheckpointError::EntryIdentityMismatch {
            epoch_tag, entries, ..
        } = &caught
        else {
            unreachable!("expected an entry-identity mismatch, got {caught:?}")
        };
        assert_eq!(
            epoch_tag,
            here.tag(),
            "the refusal names the epoch it derived under"
        );
        assert_eq!(*entries, state.len());
        // And the unforged checkpoint still restores, so the seam is discriminating rather
        // than breaking everything.
        assert!(ExtensionState::restore(None, &mine, TEST_LIMITS).is_ok());

        eprintln!(
            "{{\"schema\":\"fln.unit.checkpoint-epoch-entry-binding\",\"version\":1,\
             \"bead\":\"fln-extension-history-checkpoint-identity-41s\",\
             \"claim_type\":\"bounded_model\",\
             \"scenario\":\"capture-time-epoch-and-ordered-entry-ids\",\
             \"decision\":\"capture_time_binding\",\
             \"option_rejected\":\"restore_time_derivation_from_caller_supplied_epoch\",\
             \"binding_mechanism\":\"derivation_not_comparison\",\
             \"entry_ids\":{},\"epoch_changes_every_id\":true,\
             \"order_sensitive\":true,\"same_id_set_under_permutation\":true,\
             \"tampered_payload_changes_its_id\":true,\
             \"forged_ids_refused\":\"entry_identity_mismatch\",\
             \"unforged_still_restores\":true,\
             \"payload_retained\":false,\"status\":\"pass\"}}",
            mine.entry_ids().len()
        );
    }

    /// A probe that trips at a chosen sample, so a test can pin the exact checkpoint
    /// rather than only prove that cancellation happens.
    struct TripAt {
        trip_on: std::cell::Cell<u32>,
    }

    impl TripAt {
        fn new(sample: u32) -> TripAt {
            TripAt {
                trip_on: std::cell::Cell::new(sample),
            }
        }
    }

    impl CancellationProbe for TripAt {
        fn is_cancelled(&self) -> bool {
            let remaining = self.trip_on.get();
            if remaining == 0 {
                return true;
            }
            self.trip_on.set(remaining - 1);
            false
        }
    }

    /// The widened signature has real inhabitants on the non-answer arm.
    ///
    /// This is the point of widening the type BEFORE bounding the proofs: a budget stop
    /// has somewhere truthful to go. Cancellation is that inhabitant today; comparison
    /// exhaustion joins it in the next slice. Until the type could express a non-answer,
    /// a stop would have had to arrive as a `CheckpointError` — a rejection wearing a
    /// resource-exhaustion hat, and the exact FL-INV-07 collapse this bead is about.
    #[test]
    fn cancellation_is_a_typed_non_answer_at_a_frozen_checkpoint() {
        let base = state_with_checkpoint(3, CheckpointSemantics::JournalSuffix);
        let target = base.push_entry(bytes(b"suffix"));
        let checkpoint = target
            .checkpoint(Some(&base), TEST_LIMITS)
            .expect("checkpoint captures");

        for (sample, expected) in [
            (0u32, CheckpointProofCheckpoint::BeforeBaseProof),
            (1, CheckpointProofCheckpoint::BeforePublication),
        ] {
            let probe = TripAt::new(sample);
            let cancelled = ExtensionState::try_restore(
                Some(&base),
                &checkpoint,
                TEST_LIMITS,
                ProofBudget::UNBOUNDED,
                Some(&probe),
            );
            let Outcome::Inconclusive(inconclusive) = &cancelled else {
                unreachable!("a tripped probe must stop restore, got {cancelled:?}")
            };
            let InconclusiveCause::Cancelled { at } = &inconclusive.cause else {
                unreachable!("cancellation must not be reported as exhaustion")
            };
            assert_eq!(
                at.text(),
                expected.to_string(),
                "the probe must stop at the checkpoint it was set for"
            );
            // Not a refusal, and not cacheable: no verdict was reached about this
            // checkpoint, so a cache that stored it would replay "we gave up" as "this
            // checkpoint is bad".
            assert_eq!(cancelled.authority(), Authority::NonAuthoritative);
            assert_eq!(
                cancelled.cache_admission(),
                CacheAdmission::Refused {
                    authority: Authority::NonAuthoritative
                }
            );
        }

        // Capture side, same contract.
        let capture_probe = TripAt::new(0);
        let cancelled_capture = target.try_checkpoint(
            Some(&base),
            TEST_LIMITS,
            ProofBudget::UNBOUNDED,
            &fixture_epoch(),
            Some(&capture_probe),
        );
        assert_eq!(
            cancelled_capture.authority(),
            Authority::NonAuthoritative,
            "a cancelled capture reached no verdict either"
        );

        // An untripped probe must not change the answer, on either side.
        let quiet = TripAt::new(u32::MAX);
        let restored = ExtensionState::try_restore(
            Some(&base),
            &checkpoint,
            TEST_LIMITS,
            ProofBudget::UNBOUNDED,
            Some(&quiet),
        )
        .into_complete()
        .expect("an untripped probe restores")
        .expect("and the restore itself succeeds");
        assert_eq!(
            restored.content_digest(),
            ExtensionState::restore(Some(&base), &checkpoint, TEST_LIMITS)
                .expect("fixture path agrees")
                .content_digest()
        );
        let quiet_capture = TripAt::new(u32::MAX);
        assert_eq!(
            target
                .try_checkpoint(
                    Some(&base),
                    TEST_LIMITS,
                    ProofBudget::UNBOUNDED,
                    &fixture_epoch(),
                    Some(&quiet_capture)
                )
                .into_complete()
                .expect("an untripped probe captures")
                .expect("and the capture itself succeeds"),
            checkpoint
        );

        // A completed refusal stays a refusal: widening the type must not have turned a
        // verdict into a non-answer.
        let wrong = state_with_checkpoint(2, CheckpointSemantics::JournalSuffix);
        let refused = ExtensionState::try_restore(
            Some(&wrong),
            &checkpoint,
            TEST_LIMITS,
            ProofBudget::UNBOUNDED,
            None,
        );
        assert_eq!(
            refused.authority(),
            Authority::Authoritative,
            "a wrong base is a completed determination, not a non-answer"
        );
        assert!(
            refused.into_complete().expect("completed").is_err(),
            "and that determination is a refusal"
        );
    }

    fn planned(
        base: Option<&ExtensionState>,
        checkpoint: &ExtensionCheckpoint,
    ) -> PreparedExtensionHistory {
        ExtensionState::plan_history_restore(base, checkpoint, TEST_LIMITS, ProofBudget::UNBOUNDED)
            .expect("an unbounded proof budget cannot bind")
            .expect("planning succeeds")
    }

    /// One preflighted transaction, and a failed one leaves the original untouched —
    /// proved by comparing roots before and after, not by reading the code path.
    #[test]
    fn the_history_plan_is_preflighted_and_a_failure_leaves_the_original_untouched() {
        let captured_base = state_with_checkpoint(4, CheckpointSemantics::JournalSuffix);
        let target = captured_base.push_entry(bytes(b"suffix"));
        let checkpoint = target
            .checkpoint(Some(&captured_base), TEST_LIMITS)
            .expect("checkpoint captures");

        let plan = planned(Some(&captured_base), &checkpoint);
        // Material is not authority.
        assert!(!plan.is_cacheable());
        assert_eq!(plan.descriptor(), checkpoint.descriptor());
        assert!(plan.is_valid_for(Some(&captured_base)));
        // The proof happened at plan time, in O(1) here because the base was kept.
        assert_eq!(plan.proof_usage().kind, HistoryProofKind::SharedStructure);
        assert_eq!(plan.proof_usage().compared_entries, 0);

        // Roots before: the target ExtensionState's own digest, and an enclosing
        // Environment's logical root, because both must be untouched by a failure.
        let digest_before = captured_base.content_digest();
        let env = Environment::new()
            .register_extension(captured_base.descriptor.clone())
            .expect("register");
        let env_root_before = env.logical_root(&KVMap::new());
        let snapshot = captured_base.clone();

        // Forced failure 1: the plan committed against a DIFFERENT base. Content-identical
        // but independently built, so this is refused on the plan's own binding rather
        // than on content — a plan's recorded proof describes the base it was given.
        let rebuilt = state_with_checkpoint(4, CheckpointSemantics::JournalSuffix);
        assert_eq!(rebuilt.content_digest(), captured_base.content_digest());
        assert!(!plan.is_valid_for(Some(&rebuilt)));
        let superseded = plan
            .commit(Some(&rebuilt), None)
            .expect_err("a cross-base plan must be refused");
        assert!(matches!(superseded, CheckpointError::PlanSuperseded { .. }));

        // Forced failure 2: committed with no base at all.
        assert!(plan.commit(None, None).is_err());

        // Forced failure 3: a full-journal plan committed against a base.
        let full = state_with_checkpoint(3, CheckpointSemantics::FullJournal)
            .checkpoint(None, TEST_LIMITS)
            .expect("full captures");
        let full_plan = planned(None, &full);
        assert_eq!(
            full_plan.proof_usage().kind,
            HistoryProofKind::SelfContained
        );
        assert!(full_plan.commit(Some(&captured_base), None).is_err());

        // Untouched after all three: same value, same digest, same enclosing root, and
        // still sharing with the pre-failure snapshot.
        assert_eq!(digest_before, captured_base.content_digest());
        assert_eq!(digest_before, snapshot.content_digest());
        assert_eq!(env_root_before, env.logical_root(&KVMap::new()));
        assert_eq!(captured_base, snapshot);
        assert!(captured_base.journal.is_same_structure(&snapshot.journal));

        // And the honest commit still applies, reproducing exactly what the direct path
        // produces — so plan-then-commit is not a second semantics.
        let restored = plan
            .commit(Some(&captured_base), None)
            .expect("the honest commit applies");
        assert_eq!(restored.state, target);
        assert_eq!(
            restored.state.content_digest(),
            ExtensionState::restore(Some(&captured_base), &checkpoint, TEST_LIMITS)
                .expect("direct path agrees")
                .content_digest()
        );
        // Committing twice from one plan yields the same state: applying is a pure
        // function of the plan, so "consumed once" is about the PROOF, not about the plan
        // becoming unusable.
        assert_eq!(
            plan.commit(Some(&captured_base), None)
                .expect("re-commit applies")
                .state,
            restored.state
        );
    }

    /// DOUBLE-CHARGE EXACT COMPARISON: the named mutant, killed on recorded usage.
    ///
    /// Previously unwritable rather than merely unwritten — there was no charge to double.
    /// Now the plan records what the proof cost and commit records what committing cost,
    /// so charging the comparison a second time is a visible arithmetic fact rather than
    /// an invisible performance loss.
    #[test]
    fn the_double_charge_exact_comparison_mutant_is_killed_on_recorded_usage() {
        let captured_base = state_with_checkpoint(5, CheckpointSemantics::JournalSuffix);
        let target = captured_base.push_entry(bytes(b"suffix"));
        let checkpoint = target
            .checkpoint(Some(&captured_base), TEST_LIMITS)
            .expect("checkpoint captures");

        // An independently rebuilt base, so the proof is a real exact comparison and
        // therefore has a non-zero charge to be double-counted.
        let rebuilt = state_with_checkpoint(5, CheckpointSemantics::JournalSuffix);
        assert!(!rebuilt.journal.is_same_structure(&captured_base.journal));
        let plan = planned(Some(&rebuilt), &checkpoint);
        assert_eq!(plan.proof_usage().kind, HistoryProofKind::ExactComparison);
        let charged_once = *plan.proof_usage();
        assert_eq!(charged_once.compared_entries, 5);
        assert!(charged_once.compared_payload_bytes > 0);

        // CANONICAL: committing charges NOTHING, because the proof was consumed at plan
        // time. Applying a suffix examines the suffix, never the base.
        let restored = plan
            .commit(Some(&rebuilt), None)
            .expect("the commit applies");
        assert_eq!(
            restored.commit_usage.compared_entries, 0,
            "commit must not recharge the base comparison"
        );
        assert_eq!(restored.commit_usage.compared_payload_bytes, 0);
        let canonical_total = charged_once
            .compared_entries
            .checked_add(restored.commit_usage.compared_entries)
            .expect("no overflow");
        assert_eq!(
            canonical_total, charged_once.compared_entries,
            "the total charge must equal the single proof"
        );

        // MUTANT: a commit that re-proves the base. Modelled by charging the comparison
        // again — which is exactly what re-running it would cost.
        let recharged = bounded_entry_divergence(&rebuilt, &rebuilt, ProofBudget::UNBOUNDED);
        assert_eq!(recharged, Ok(None), "the model re-proof does succeed");
        let mutant_total = charged_once
            .compared_entries
            .checked_add(charged_once.compared_entries)
            .expect("no overflow");
        assert_ne!(
            mutant_total, canonical_total,
            "the double-charge model must be distinguishable from the canonical total"
        );
        assert_eq!(
            mutant_total,
            charged_once.compared_entries * 2,
            "and it must be exactly twice, or it is not modelling a double charge"
        );

        // The typed kill: the discriminating signal is commit_usage being zero, not the
        // totals merely differing. A commit that recharged would report non-zero here,
        // and that field is the only place the difference is observable.
        assert_eq!(
            restored.commit_usage.compared_entries, 0,
            "recorded_commit_usage is the typed kill signal for double_charge"
        );
        // And it is zero in the O(1) mode too, so the contract does not depend on which
        // proof discharged it.
        let shared_plan = planned(Some(&captured_base), &checkpoint);
        assert_eq!(
            shared_plan.proof_usage().kind,
            HistoryProofKind::SharedStructure
        );
        assert_eq!(
            shared_plan
                .commit(Some(&captured_base), None)
                .expect("applies")
                .commit_usage
                .compared_entries,
            0
        );

        eprintln!(
            "{{\"schema\":\"fln.unit.checkpoint-history-plan\",\"version\":1,\
             \"bead\":\"fln-extension-history-checkpoint-identity-41s\",\
             \"claim_type\":\"bounded_model\",\
             \"scenario\":\"plan-consumed-once-not-double-charged\",\
             \"plan_cacheable\":false,\
             \"proof_charged_at_plan_entries\":{},\
             \"commit_charged_entries\":0,\
             \"canonical_total_entries\":{},\
             \"double_charge_model_total_entries\":{},\
             \"mutant\":\"double_charge_exact_comparison\",\
             \"kill_signal\":\"recorded_commit_usage\",\
             \"cross_base_plan\":\"refused_plan_superseded\",\
             \"usage_accounting\":\"logical_attributed_phase_local\",\
             \"allocator_or_rss_claimed\":false,\"status\":\"pass\"}}",
            charged_once.compared_entries, canonical_total, mutant_total
        );
    }

    /// FullJournal binds every fact it names that EXISTS, and each omission dies for its
    /// own typed reason.
    ///
    /// # Two named bindings refer to surface this crate does not have
    ///
    /// The bead requires FullJournal to bind "epoch/profile" and "exact ordered
    /// EntryIds". Neither exists: `ExtensionEntry` carries a payload and nothing else, so
    /// there are no entry *ids* (order is bound — the journal and its digest are
    /// order-sensitive — but there is no identifier to bind), and there is no epoch or
    /// profile concept on `ExtensionCheckpoint` or `ExtensionDescriptor` at all. Adding
    /// either is new design surface, not a binding fix, so it is recorded on the bead as
    /// a decision rather than invented here. What follows covers every named binding that
    /// does exist.
    #[test]
    fn full_journal_binding_omissions_each_die_for_their_own_typed_reason() {
        let full_state = state_with_checkpoint(4, CheckpointSemantics::FullJournal);
        let checkpoint = full_state
            .checkpoint(None, TEST_LIMITS)
            .expect("full journal captures");
        let host = Environment::new()
            .register_extension(full_state.descriptor.clone())
            .expect("register the target extension");

        // Baseline: it applies, and to exactly the captured state.
        let applied = completed(host.apply_extension_checkpoint(
            &checkpoint,
            TEST_LIMITS,
            ProofBudget::UNBOUNDED,
            None,
        ))
        .expect("the honest full-journal checkpoint applies");
        assert_eq!(
            applied
                .extension(&full_state.descriptor.name)
                .expect("registered")
                .content_digest(),
            full_state.content_digest()
        );

        // ---- omit the DESCRIPTOR binding -> ContractMismatch / NameMismatch ----------
        let other_descriptor = ExtensionDescriptor {
            name: full_state.descriptor.name.clone(),
            provenance: PayloadProvenance::Opaque,
            ..full_state.descriptor.clone()
        };
        assert_ne!(other_descriptor, full_state.descriptor);
        let wrong_host = Environment::new()
            .register_extension(other_descriptor)
            .expect("register a differently-contracted extension");
        let refused = completed(wrong_host.apply_extension_checkpoint(
            &checkpoint,
            TEST_LIMITS,
            ProofBudget::UNBOUNDED,
            None,
        ))
        .expect_err("a descriptor mismatch must be refused");
        assert!(
            matches!(
                refused,
                crate::environment::EnvError::Checkpoint(CheckpointError::ContractMismatch { .. })
            ),
            "expected a contract mismatch, got {refused:?}"
        );

        // ---- omit the TARGET NAME binding -> UnknownExtension -----------------------
        let empty_host = Environment::new();
        assert!(
            completed(empty_host.apply_extension_checkpoint(
                &checkpoint,
                TEST_LIMITS,
                ProofBudget::UNBOUNDED,
                None,
            ))
            .is_err(),
            "a checkpoint must not apply to an environment lacking its target"
        );

        // ---- omit the SCHEMA binding -> UnsupportedVersion --------------------------
        let wrong_schema = checkpoint
            .clone()
            .forge_schema_version(EXTENSION_CHECKPOINT_SCHEMA_VERSION + 7);
        let schema_refused = ExtensionState::restore(None, &wrong_schema, TEST_LIMITS)
            .expect_err("an unknown schema must be refused, never guessed compatible");
        assert!(matches!(
            schema_refused,
            CheckpointError::UnsupportedVersion { .. }
        ));

        // ---- omit the CUMULATIVE FACTS binding -> MalformedCheckpoint ---------------
        let wrong_facts = checkpoint.clone().forge_cumulative_facts(99);
        let facts_refused = ExtensionState::restore(None, &wrong_facts, TEST_LIMITS)
            .expect_err("declared facts that disagree with the journal must be refused");
        assert!(matches!(
            facts_refused,
            CheckpointError::MalformedCheckpoint { .. }
        ));

        // ---- omit the VALUE binding -> different restored identity ------------------
        let mut altered = ExtensionState::new(full_state.descriptor.clone());
        for index in 0..4u64 {
            let payload = if index == 2 {
                u64::MAX.to_le_bytes()
            } else {
                index.to_le_bytes()
            };
            altered = altered.push_entry(bytes(payload.as_slice()));
        }
        let altered_checkpoint = altered
            .checkpoint(None, TEST_LIMITS)
            .expect("altered full journal captures");
        assert_eq!(
            altered_checkpoint.captured_entries(),
            checkpoint.captured_entries()
        );
        assert_ne!(
            ExtensionState::restore(None, &altered_checkpoint, TEST_LIMITS)
                .expect("applies")
                .content_digest(),
            ExtensionState::restore(None, &checkpoint, TEST_LIMITS)
                .expect("applies")
                .content_digest(),
            "one changed entry value must change the restored identity"
        );

        // ---- omit the AMBIENT-BASE refusal -> UnexpectedBase ------------------------
        let base_refused = ExtensionState::restore(Some(&full_state), &checkpoint, TEST_LIMITS)
            .expect_err("full-journal mode is self-contained and must refuse an ambient base");
        assert!(matches!(
            base_refused,
            CheckpointError::UnexpectedBase { .. }
        ));

        eprintln!(
            "{{\"schema\":\"fln.unit.checkpoint-full-journal-bindings\",\"version\":1,\
             \"bead\":\"fln-extension-history-checkpoint-identity-41s\",\
             \"claim_type\":\"bounded_model\",\
             \"scenario\":\"full-journal-binding-omissions\",\
             \"descriptor_omission\":\"contract_mismatch\",\
             \"target_name_omission\":\"unknown_extension\",\
             \"schema_omission\":\"unsupported_version\",\
             \"cumulative_facts_omission\":\"malformed_checkpoint\",\
             \"value_omission\":\"restored_identity_differs\",\
             \"ambient_base_omission\":\"unexpected_base\",\
             \"bindings_named_but_absent_from_this_crate\":\
             [\"epoch_or_profile\",\"ordered_entry_ids\"],\
             \"absent_surface_is_new_design_not_a_binding_fix\":true,\"status\":\"pass\"}}"
        );
    }

    /// Usage facts are LOGICAL and reproducible, never allocator or process facts.
    ///
    /// The bead's mutants include reporting allocator/RSS bytes as canonical usage and
    /// claiming cross-process portability. The discriminating property for both is
    /// reproducibility from values alone: two independently built, content-identical
    /// states must report byte-identical facts. An allocator or RSS number would not,
    /// and a durable cross-process claim would need surface this crate does not have.
    #[test]
    fn usage_facts_are_reproducible_from_values_not_from_the_process() {
        let first = state_with_checkpoint(6, CheckpointSemantics::JournalSuffix);
        let second = state_with_checkpoint(6, CheckpointSemantics::JournalSuffix);
        assert_eq!(first.content_digest(), second.content_digest());
        assert!(
            !first.journal.is_same_structure(&second.journal),
            "the two must be independently built, or reproducibility proves nothing"
        );

        let first_point = first
            .push_entry(bytes(b"suffix"))
            .checkpoint(Some(&first), TEST_LIMITS)
            .expect("captures");
        let second_point = second
            .push_entry(bytes(b"suffix"))
            .checkpoint(Some(&second), TEST_LIMITS)
            .expect("captures");

        // Retained-base facts: identical across two separate allocations of the same value.
        assert_eq!(
            first_point.retained_base_facts(),
            second_point.retained_base_facts(),
            "retained facts must be a function of the value, not of the allocation"
        );

        // Proof usage: identical too, including the compared byte count, which is the
        // field an allocator-derived number would most obviously perturb.
        let cross = planned(Some(&second), &first_point);
        let cross_again = planned(Some(&second), &first_point);
        assert_eq!(cross.proof_usage(), cross_again.proof_usage());
        assert_eq!(cross.proof_usage().kind, HistoryProofKind::ExactComparison);
        assert_eq!(
            cross.proof_usage().compared_payload_bytes,
            second.journal.payload_bytes,
            "compared bytes must equal the canonical payload total, a logical quantity"
        );

        // Same-process semantic portability: the plan proved against an independently
        // rebuilt base commits to the same state the original does.
        assert_eq!(
            cross
                .commit(Some(&second), None)
                .expect("applies")
                .state
                .content_digest(),
            ExtensionState::restore(Some(&first), &first_point, TEST_LIMITS)
                .expect("original applies")
                .content_digest()
        );

        eprintln!(
            "{{\"schema\":\"fln.unit.checkpoint-usage-provenance\",\"version\":1,\
             \"bead\":\"fln-extension-history-checkpoint-identity-41s\",\
             \"claim_type\":\"bounded_model\",\
             \"scenario\":\"usage-facts-reproducible-from-values\",\
             \"mutants\":[\"report_allocator_or_rss_as_canonical_usage\",\
             \"claim_cross_process_portability\"],\
             \"kill_signal\":\"byte_identical_facts_across_independent_allocations\",\
             \"portability_claimed\":\"same_process_semantic_only\",\
             \"durable_encoding_claimed\":false,\"status\":\"pass\"}}"
        );
    }

    /// Fixed seed for the branch matrix. A constant, not a clock or an RNG: a schedule
    /// proof whose input cannot be reproduced is a story about one run.
    const BRANCH_SEED: u64 = 0xa5a5_5a5a_c3c3_3c3c;

    /// Distinct branches in the matrix. Chosen so the widest schedule still gives every
    /// worker real work — 64 over 32 workers is two each, and the test asserts no
    /// partition is empty.
    const BRANCH_COUNT: usize = 64;

    /// The 1/8/32 matrix over DISTINCT branches, productive by assertion.
    ///
    /// Transcribed from `franken_lean-j8h`'s declaration-admission matrix (6c0e406)
    /// rather than re-derived, and the bead's own wording is why every assertion here
    /// exists: "relabeling one sequential loop is insufficient." So the test asserts no
    /// empty partition, full coverage, AND that the number of distinct thread ids that
    /// did work equals the worker count — measured, not assumed.
    ///
    /// Each worker plans and commits real checkpoint restores on its own branches. The
    /// branches are genuinely distinct values, and the reduction is order-independent, so
    /// one digest must hold across 1, 8 and 32 workers and equal a sequential model.
    ///
    /// Honest scope: bounded component evidence for checkpoint identity under
    /// concurrency, not closure for the bead.
    #[test]
    fn checkpoint_identity_is_stable_across_1_8_32_productive_branch_schedules() {
        // Each branch is a base of seed-varied length plus a seed-varied suffix, so no
        // two branches are the same value and a matrix of identical items cannot pass by
        // accident.
        let branches: Vec<(ExtensionState, ExtensionCheckpoint)> = (0..BRANCH_COUNT)
            .map(|index| {
                let mixed = BRANCH_SEED
                    ^ (u64::try_from(index)
                        .unwrap_or(0)
                        .wrapping_mul(0x100_0000_01b3));
                let base_len = usize::try_from(mixed % 5).unwrap_or(0) + 1;
                let mut base = ExtensionState::new(descriptor_with_checkpoint(
                    CheckpointSemantics::JournalSuffix,
                ));
                for entry in 0..base_len {
                    base =
                        base.push_entry(bytes(format!("branch.{index}.base.{entry}").as_bytes()));
                }
                let target = base.push_entry(bytes(format!("branch.{index}.suffix").as_bytes()));
                let checkpoint = target
                    .checkpoint(Some(&base), TEST_LIMITS)
                    .expect("branch checkpoint captures");
                (base, checkpoint)
            })
            .collect();

        // The sequential model, built independently of any schedule.
        let sequential: Vec<Digest> = branches
            .iter()
            .map(|(base, checkpoint)| {
                ExtensionState::restore(Some(base), checkpoint, TEST_LIMITS)
                    .expect("sequential restore")
                    .content_digest()
            })
            .collect();
        let reduce = |mut digests: Vec<Digest>| {
            digests.sort_unstable();
            let mut w = CanonWriter::new();
            w.str("fln.test.checkpoint-branch-schedule");
            w.u16(1);
            w.u64(u64::try_from(digests.len()).unwrap_or(u64::MAX));
            for digest in digests {
                w.bytes(&digest.0);
            }
            hash(Domain::Fixture, &w.into_bytes())
        };
        let expected = reduce(sequential.clone());

        let mut reductions = Vec::new();
        for worker_count in [1usize, 8, 32] {
            let (digests, sizes, threads) = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..worker_count)
                    .map(|worker| {
                        let branches = &branches;
                        scope.spawn(move || {
                            let mut mine = Vec::new();
                            for (index, (base, checkpoint)) in branches.iter().enumerate() {
                                if index % worker_count != worker {
                                    continue;
                                }
                                // The full transaction: plan, then commit.
                                let plan = ExtensionState::plan_history_restore(
                                    Some(base),
                                    checkpoint,
                                    TEST_LIMITS,
                                    ProofBudget::UNBOUNDED,
                                )
                                .expect("unbounded proof cannot bind")
                                .expect("planning succeeds");
                                let restored =
                                    plan.commit(Some(base), None).expect("commit applies");
                                mine.push(restored.state.content_digest());
                            }
                            (mine, std::thread::current().id())
                        })
                    })
                    .collect();
                let mut digests = Vec::new();
                let mut sizes = Vec::new();
                let mut threads = HashSet::new();
                for handle in handles {
                    let (mine, id) = handle.join().expect("worker completes");
                    sizes.push(mine.len());
                    threads.insert(id);
                    digests.extend(mine);
                }
                (digests, sizes, threads)
            });

            assert_eq!(sizes.len(), worker_count);
            assert!(
                sizes.iter().all(|size| *size > 0),
                "an empty partition means this worker count is a label, not a schedule \
                 (sizes {sizes:?})"
            );
            assert_eq!(
                sizes.iter().sum::<usize>(),
                BRANCH_COUNT,
                "the partitions must cover every branch exactly once"
            );
            assert_eq!(
                threads.len(),
                worker_count,
                "work must be done by {worker_count} distinct threads, not relabelled \
                 serial work"
            );
            let reduction = reduce(digests);
            assert_eq!(
                reduction, expected,
                "schedule with {worker_count} workers diverged from the sequential model"
            );
            reductions.push((worker_count, reduction, sizes, threads.len()));
        }

        let distinct: HashSet<Digest> = reductions
            .iter()
            .map(|(_, reduction, _, _)| *reduction)
            .collect();
        assert_eq!(
            distinct.len(),
            1,
            "the reduction must not depend on the worker count"
        );

        for (worker_count, reduction, sizes, measured_threads) in &reductions {
            let min = sizes.iter().min().copied().unwrap_or_default();
            let max = sizes.iter().max().copied().unwrap_or_default();
            eprintln!(
                "{{\"schema\":\"fln.unit.checkpoint-branch-schedule\",\"version\":1,\
                 \"bead\":\"fln-extension-history-checkpoint-identity-41s\",\
                 \"claim_type\":\"bounded_model\",\
                 \"gate_relation\":\"partial-component-evidence\",\
                 \"scenario\":\"productive-1-8-32-branch-matrix\",\
                 \"seed\":\"{BRANCH_SEED:#018x}\",\"branches\":{BRANCH_COUNT},\
                 \"worker_count\":{worker_count},\
                 \"distinct_worker_threads\":{measured_threads},\
                 \"partition_scheme\":\"index-modulo-worker-count-v1\",\
                 \"min_partition\":{min},\"max_partition\":{max},\"empty_partitions\":0,\
                 \"execution_model\":\"plan_then_commit_per_distinct_branch\",\
                 \"reduction\":\"canonical-sorted-restored-digest-set-v1\",\
                 \"reduction_digest\":\"{reduction}\",\
                 \"matches_sequential_model\":true,\"status\":\"pass\"}}"
            );
        }
        eprintln!(
            "{{\"schema\":\"fln.unit.checkpoint-branch-schedule-summary\",\"version\":1,\
             \"bead\":\"fln-extension-history-checkpoint-identity-41s\",\
             \"claim_type\":\"bounded_model\",\
             \"gate_relation\":\"partial-component-evidence\",\
             \"scenario\":\"productive-1-8-32-branch-matrix\",\
             \"seed\":\"{BRANCH_SEED:#018x}\",\"worker_counts\":[1,8,32],\
             \"branches\":{BRANCH_COUNT},\"distinct_reductions\":{},\
             \"expected_distinct_reductions\":1,\"reduction_digest\":\"{expected}\",\
             \"status\":\"pass\"}}",
            distinct.len()
        );
    }

    /// The proof budget binds, and a stop is a non-answer — never a divergence.
    ///
    /// This is the payoff of widening the type first. The comparison can now run out,
    /// and when it does the outcome says "no verdict was reached", not "these histories
    /// differ". Manufacturing a divergence out of running short of room would be a
    /// refusal invented from a resource limit, which is this bead's defect in its purest
    /// form.
    #[test]
    fn the_proof_budget_binds_and_a_stop_is_not_a_divergence() {
        let captured_base = state_with_checkpoint(6, CheckpointSemantics::JournalSuffix);
        let target = captured_base.push_entry(bytes(b"suffix"));
        let checkpoint = target
            .checkpoint(Some(&captured_base), TEST_LIMITS)
            .expect("checkpoint captures");
        // An independently rebuilt base, so the O(1) structural proof cannot apply and
        // the comparison is genuinely reached.
        let rebuilt = state_with_checkpoint(6, CheckpointSemantics::JournalSuffix);
        assert!(!rebuilt.journal.is_same_structure(&captured_base.journal));

        // Exactly enough entries admits.
        let exact = ProofBudget::new(6, u128::MAX);
        assert!(
            ExtensionState::try_restore(Some(&rebuilt), &checkpoint, TEST_LIMITS, exact, None)
                .into_complete()
                .expect("an exact budget must not stop")
                .is_ok(),
            "an exact budget must admit"
        );

        // One short stops, and the stop is INCONCLUSIVE rather than a BaseNotExact.
        let one_short = ProofBudget::new(5, u128::MAX);
        let stopped =
            ExtensionState::try_restore(Some(&rebuilt), &checkpoint, TEST_LIMITS, one_short, None);
        let Outcome::Inconclusive(inconclusive) = &stopped else {
            unreachable!("one entry short must stop, got {stopped:?}")
        };
        let InconclusiveCause::ResourceExhausted { usage } = &inconclusive.cause else {
            unreachable!("a budget stop must be ResourceExhausted")
        };
        assert_eq!(usage.allowed, 5);
        assert!(
            usage.observed > usage.allowed,
            "a stop must report spending past its allowance"
        );
        assert!(usage.is_genuine_exhaustion());
        assert_eq!(
            inconclusive
                .progress
                .as_ref()
                .map(|progress| progress.text()),
            Some(ProofDimension::ComparedEntries.as_str())
        );
        assert_eq!(stopped.authority(), Authority::NonAuthoritative);
        assert_eq!(
            stopped.cache_admission(),
            CacheAdmission::Refused {
                authority: Authority::NonAuthoritative
            }
        );

        // The payload-byte dimension binds independently of the entry count.
        let byte_bound = ProofBudget::new(usize::MAX, 4);
        let byte_stopped =
            ExtensionState::try_restore(Some(&rebuilt), &checkpoint, TEST_LIMITS, byte_bound, None);
        let (_, byte_progress) = match &byte_stopped {
            Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
                InconclusiveCause::ResourceExhausted { usage } => (
                    usage,
                    inconclusive
                        .progress
                        .as_ref()
                        .map(|progress| progress.text()),
                ),
                _ => unreachable!("a budget stop must be ResourceExhausted"),
            },
            _ => unreachable!("a tight byte budget must stop, got {byte_stopped:?}"),
        };
        assert_eq!(
            byte_progress,
            Some(ProofDimension::ComparedPayloadBytes.as_str())
        );

        // AN ADEQUATE-BUDGET RETRY SUCCEEDS AND IS IDENTICAL. A stop must be recoverable,
        // or it is a rejection by another name.
        let retried =
            ExtensionState::try_restore(Some(&rebuilt), &checkpoint, TEST_LIMITS, exact, None)
                .into_complete()
                .expect("the retry completes")
                .expect("and restores");
        assert_eq!(
            retried.content_digest(),
            ExtensionState::restore(Some(&captured_base), &checkpoint, TEST_LIMITS)
                .expect("the fixture path agrees")
                .content_digest(),
            "an adequate-budget retry must reproduce the unlimited result exactly"
        );

        // A stop must never be reported as a divergence, at either depth. Under a
        // budget that binds, the bounded comparison returns Err rather than Ok(Some).
        assert!(
            matches!(
                bounded_entry_divergence(&captured_base, &rebuilt, one_short),
                Err((ProofDimension::ComparedEntries, 5, _))
            ),
            "a bound comparison must report a stop, not a divergence"
        );
        // And where it does finish, it agrees with the unbounded helper.
        assert_eq!(
            bounded_entry_divergence(&captured_base, &rebuilt, exact),
            Ok(None)
        );
        assert_eq!(first_entry_divergence(&captured_base, &rebuilt), None);

        // Capture side, same contract.
        let capture_stop = target.try_checkpoint(
            Some(&rebuilt),
            TEST_LIMITS,
            one_short,
            &fixture_epoch(),
            None,
        );
        assert_eq!(
            capture_stop.authority(),
            Authority::NonAuthoritative,
            "a bound capture proof reached no verdict either"
        );

        eprintln!(
            "{{\"schema\":\"fln.unit.checkpoint-proof-budget\",\"version\":1,\
             \"bead\":\"fln-extension-history-checkpoint-identity-41s\",\
             \"claim_type\":\"bounded_model\",\
             \"scenario\":\"bounded-exact-comparison\",\
             \"compared_entries_exact\":\"admits\",\
             \"compared_entries_one_short\":\"inconclusive_resource_exhausted\",\
             \"compared_payload_bytes_tight\":\"inconclusive_resource_exhausted\",\
             \"stop_reported_as_divergence\":false,\
             \"adequate_budget_retry\":\"identical_to_unlimited\",\
             \"authority_on_stop\":\"non_authoritative\",\
             \"cacheable_on_stop\":false,\
             \"charge_order\":\"before_each_compared_entry\",\"status\":\"pass\"}}"
        );
    }

    /// CAPTURE side: a base that satisfies the prefix-digest accelerator but is not
    /// actually the prefix must be refused.
    ///
    /// The symmetric half of the restore-side defect. `prefix_facts(base.len())` yields
    /// a cumulative digest stored on the target's journal; comparing it to the base's
    /// own digest can reject a base that plainly is not the prefix, but it cannot prove
    /// one that is. Simulated through a seam that forges the BASE's journal facts —
    /// necessarily a different seam from the restore-side one, because the two defects
    /// compare different pairs of values.
    #[test]
    fn capture_refuses_a_base_that_only_matches_the_prefix_digest() {
        let real_base = state_with_checkpoint(3, CheckpointSemantics::JournalSuffix);
        let target = real_base.push_entry(bytes(b"suffix"));

        // A same-length base sharing a two-entry prefix and differing at the last.
        let mut wrong = ExtensionState::new(descriptor_with_checkpoint(
            CheckpointSemantics::JournalSuffix,
        ));
        for index in 0..2u64 {
            wrong = wrong.push_entry(bytes(&index.to_le_bytes()));
        }
        let wrong = wrong.push_entry(bytes(b"not-the-real-third"));
        assert_eq!(wrong.len(), real_base.len());

        // Without forging, the accelerator already rejects it — asserted so the cheap
        // path is still proved to work.
        let refused = target
            .checkpoint(Some(&wrong), TEST_LIMITS)
            .expect_err("a different history must be refused at capture");
        assert!(
            matches!(refused, CheckpointError::HistoryMismatch { .. }),
            "expected the digest-level rejection, got {refused:?}"
        );

        // Forge the base's own journal facts to those of the real base, so the
        // accelerator accepts and only the exact prefix proof can refuse.
        let colliding = wrong
            .clone()
            .forge_journal_facts(real_base.journal.digest, real_base.journal.payload_bytes);
        let caught = target
            .checkpoint(Some(&colliding), TEST_LIMITS)
            .expect_err("an equal-digest non-prefix base must still be refused at capture");
        let CheckpointError::BaseNotExact {
            base_len,
            first_divergence,
            ..
        } = &caught
        else {
            unreachable!("expected the exact prefix proof to refuse, got {caught:?}")
        };
        assert_eq!(*base_len, 3);
        assert_eq!(
            *first_divergence, 2,
            "the divergence must name the entry where the base stopped being a prefix"
        );

        // And the honest base still captures, so the proof is discriminating rather
        // than refusing everything.
        assert!(
            target.checkpoint(Some(&real_base), TEST_LIMITS).is_ok(),
            "the real base must still capture"
        );
        // Including at the boundaries, where an off-by-one in the prefix walk would show.
        for base_len in 0..4usize {
            let base = state_with_checkpoint(base_len, CheckpointSemantics::JournalSuffix);
            let grown = base.push_entry(bytes(b"boundary"));
            assert!(
                grown.checkpoint(Some(&base), TEST_LIMITS).is_ok(),
                "capture must succeed at base_len {base_len}"
            );
            assert_eq!(prefix_divergence(&grown, &base), None);
        }

        eprintln!(
            "{{\"schema\":\"fln.unit.checkpoint-capture-ancestry\",\"version\":1,\
             \"bead\":\"fln-extension-history-checkpoint-identity-41s\",\
             \"claim_type\":\"bounded_model\",\
             \"scenario\":\"prefix-digest-is-accelerator-not-proof\",\
             \"unforged_non_prefix_base\":\"refused_by_digest_accelerator\",\
             \"equal_digest_non_prefix_base\":\"refused_by_exact_prefix_proof\",\
             \"reported_divergence\":2,\
             \"collision_source\":\"bounded_test_seam_forging_base_journal_facts_only\",\
             \"honest_base_still_captures\":true,\
             \"boundary_base_lengths\":[0,1,2,3],\"status\":\"pass\"}}"
        );
    }

    /// A digest match is an accelerator: passing it must not be the last word, and a
    /// shared-structure base takes the O(1) proof rather than the comparison.
    #[test]
    fn base_equality_is_proved_by_structure_or_by_exact_comparison() {
        let captured_base = state_with_checkpoint(4, CheckpointSemantics::JournalSuffix);
        let target = captured_base.push_entry(bytes(b"suffix"));
        let checkpoint = target
            .checkpoint(Some(&captured_base), TEST_LIMITS)
            .expect("checkpoint captures");

        // The retained handle and the presented base are the same journal by
        // construction, so the O(1) proof applies.
        let CheckpointPayload::JournalSuffix { base: retained, .. } = &checkpoint.payload else {
            unreachable!("suffix mode")
        };
        assert!(retained.journal.is_same_structure(&captured_base.journal));
        assert_eq!(first_entry_divergence(retained, &captured_base), None);

        // Exact comparison agrees with structural identity wherever both apply, and
        // reports a divergence index wherever they differ.
        let diverging = state_with_checkpoint(2, CheckpointSemantics::JournalSuffix)
            .push_entry(bytes(b"different"))
            .push_entry(bytes(b"also-different"));
        assert_eq!(diverging.len(), captured_base.len());
        assert_eq!(first_entry_divergence(retained, &diverging), Some(2));
    }

    /// An unrelated Environment edit does not invalidate a valid checkpoint.
    ///
    /// Base root means the TARGET `ExtensionState` root, not the encompassing
    /// Environment logical root. Conflating them is how a checkpoint that is still
    /// perfectly valid starts failing because some other extension or declaration
    /// changed.
    #[test]
    fn an_unrelated_environment_edit_does_not_invalidate_a_checkpoint() {
        let descriptor = descriptor_with_checkpoint(CheckpointSemantics::JournalSuffix);
        let target_name = descriptor.name.clone();
        let base_state = state_with_checkpoint(3, CheckpointSemantics::JournalSuffix);
        let target = base_state.push_entry(bytes(b"suffix"));
        let checkpoint = target
            .checkpoint(Some(&base_state), TEST_LIMITS)
            .expect("checkpoint captures");

        let expected = ExtensionState::restore(Some(&base_state), &checkpoint, TEST_LIMITS)
            .expect("restores against its own base")
            .content_digest();

        // A second, unrelated extension whose journal grows. The Environment's logical
        // root moves; the target ExtensionState's does not.
        let other = ExtensionDescriptor {
            name: Name::str(Name::anonymous(), "other.extension"),
            checkpoint: CheckpointSemantics::FullJournal,
            ..descriptor_with_checkpoint(CheckpointSemantics::FullJournal)
        };
        let unrelated_before = ExtensionState::new(other);
        let unrelated_after = unrelated_before.push_entry(bytes(b"unrelated"));
        assert_ne!(
            unrelated_before.content_digest(),
            unrelated_after.content_digest(),
            "the unrelated extension must actually change, or this proves nothing"
        );

        // The target base is untouched by that edit, so the checkpoint still restores
        // to exactly the same state.
        assert_eq!(
            ExtensionState::restore(Some(&base_state), &checkpoint, TEST_LIMITS)
                .expect("an unrelated edit must not invalidate this checkpoint")
                .content_digest(),
            expected
        );
        assert_eq!(checkpoint.descriptor().name, target_name);
    }

    /// Suffix mode reports the memory it retains; full-journal mode retains none.
    #[test]
    fn suffix_checkpoints_report_their_retained_base_footprint() {
        let base_state = state_with_checkpoint(5, CheckpointSemantics::JournalSuffix);
        let target = base_state.push_entry(bytes(b"suffix"));
        let suffix = target
            .checkpoint(Some(&base_state), TEST_LIMITS)
            .expect("suffix checkpoint captures");

        let retained = suffix
            .retained_base_facts()
            .expect("suffix mode retains its base for exact proof");
        assert_eq!(retained.entries, base_state.len());
        assert_eq!(retained.payload_bytes, base_state.journal.payload_bytes);
        // The retained footprint is the BASE's, and it is separate from what the
        // checkpoint carries — the suffix itself is one entry.
        assert_eq!(suffix.captured_entries(), 1);
        assert!(retained.entries > suffix.captured_entries());

        let full = state_with_checkpoint(5, CheckpointSemantics::FullJournal)
            .checkpoint(None, TEST_LIMITS)
            .expect("full-journal checkpoint captures");
        assert_eq!(
            full.retained_base_facts(),
            None,
            "full-journal mode is self-contained and must retain nothing"
        );

        eprintln!(
            "{{\"schema\":\"fln.unit.checkpoint-retained-footprint\",\"version\":1,\
             \"bead\":\"fln-extension-history-checkpoint-identity-41s\",\
             \"claim_type\":\"bounded_model\",\
             \"scenario\":\"retained-base-handle-accounting\",\
             \"mode\":\"journal_suffix\",\"retained_entries\":{},\
             \"retained_payload_bytes\":{},\"carried_entries\":{},\
             \"accounting\":\"logical_attributed_footprint\",\
             \"allocator_or_rss_claimed\":false,\"address_identity_used\":false,\
             \"full_journal_retains\":\"none\",\"status\":\"pass\"}}",
            retained.entries,
            retained.payload_bytes,
            suffix.captured_entries()
        );
    }

    #[test]
    fn restore_mismatch_table_is_typed_and_atomic() {
        let base = state_with_checkpoint(2, CheckpointSemantics::JournalSuffix);
        let target = base.push_entry(bytes(b"suffix"));
        let checkpoint = target
            .checkpoint(Some(&base), TEST_LIMITS)
            .expect("checkpoint captures");
        let before = (base.clone(), checkpoint.clone());

        assert_eq!(
            ExtensionState::restore(None, &checkpoint, TEST_LIMITS)
                .expect_err("missing base is refused"),
            CheckpointError::MissingBase {
                extension: base.descriptor.name.clone(),
            }
        );

        let short = state_with_checkpoint(1, CheckpointSemantics::JournalSuffix);
        assert_eq!(
            ExtensionState::restore(Some(&short), &checkpoint, TEST_LIMITS)
                .expect_err("wrong base length is refused"),
            CheckpointError::BaseLengthMismatch {
                extension: base.descriptor.name.clone(),
                expected: 2,
                actual: 1,
            }
        );

        let divergent = ExtensionState::new(base.descriptor.clone())
            .push_entry(bytes(b"wrong-a"))
            .push_entry(bytes(b"wrong-b"));
        let expected_history = match &checkpoint.payload {
            CheckpointPayload::JournalSuffix {
                base_history_digest,
                ..
            } => *base_history_digest,
            CheckpointPayload::FullJournal { .. } => unreachable!(),
        };
        assert_eq!(
            ExtensionState::restore(Some(&divergent), &checkpoint, TEST_LIMITS)
                .expect_err("cross-branch base is refused"),
            CheckpointError::BaseHistoryMismatch {
                extension: base.descriptor.name.clone(),
                expected: expected_history,
                actual: divergent.journal.digest,
            }
        );

        let mut wrong_state_digest = checkpoint.clone();
        if let CheckpointPayload::JournalSuffix {
            base_state_digest, ..
        } = &mut wrong_state_digest.payload
        {
            *base_state_digest = Digest([0xA5; 32]);
        }
        assert_eq!(
            ExtensionState::restore(Some(&base), &wrong_state_digest, TEST_LIMITS)
                .expect_err("wrong bound state digest is refused"),
            CheckpointError::BaseDigestMismatch {
                extension: base.descriptor.name.clone(),
                expected: Digest([0xA5; 32]),
                actual: base.content_digest(),
            }
        );

        let wrong_name = ExtensionState::new(ExtensionDescriptor {
            name: Name::str(Name::anonymous(), "otherExt"),
            ..base.descriptor.clone()
        })
        .push_entry(bytes(&0u64.to_le_bytes()))
        .push_entry(bytes(&1u64.to_le_bytes()));
        assert!(matches!(
            ExtensionState::restore(Some(&wrong_name), &checkpoint, TEST_LIMITS),
            Err(CheckpointError::ExtensionNameMismatch { .. })
        ));

        assert_eq!((base, checkpoint), before, "all refusals are atomic");
    }

    #[test]
    fn schema_mode_truncation_and_resource_boundaries_are_refused() {
        let base = state_with_checkpoint(2, CheckpointSemantics::JournalSuffix);
        let target = base.push_entry(bytes(b"abc")).push_entry(bytes(b"defg"));
        let checkpoint = target
            .checkpoint(Some(&base), CheckpointLimits::new(2, 7))
            .expect("exact resource boundary passes");

        for (limits, resource, limit, actual) in [
            (
                CheckpointLimits::new(1, 7),
                CheckpointResource::Entries,
                1,
                2,
            ),
            (
                CheckpointLimits::new(2, 6),
                CheckpointResource::PayloadBytes,
                6,
                7,
            ),
        ] {
            assert_eq!(
                target
                    .checkpoint(Some(&base), limits)
                    .expect_err("capture over limit is refused"),
                CheckpointError::ResourceLimitExceeded {
                    extension: base.descriptor.name.clone(),
                    resource,
                    limit,
                    actual,
                }
            );
            assert_eq!(
                ExtensionState::restore(Some(&base), &checkpoint, limits)
                    .expect_err("restore over limit is refused"),
                CheckpointError::ResourceLimitExceeded {
                    extension: base.descriptor.name.clone(),
                    resource,
                    limit,
                    actual,
                }
            );
        }

        let mut future = checkpoint.clone();
        future.schema_version += 1;
        assert_eq!(
            ExtensionState::restore(Some(&base), &future, TEST_LIMITS)
                .expect_err("unknown versions are refused"),
            CheckpointError::UnsupportedVersion {
                found: 2,
                supported: 1,
            }
        );

        let mut wrong_mode = checkpoint.clone();
        wrong_mode.descriptor.checkpoint = CheckpointSemantics::FullJournal;
        assert_eq!(
            ExtensionState::restore(Some(&base), &wrong_mode, TEST_LIMITS)
                .expect_err("mode disagreement is refused"),
            CheckpointError::ModeMismatch {
                descriptor_mode: CheckpointSemantics::FullJournal,
                payload_mode: CheckpointSemantics::JournalSuffix,
            }
        );

        let mut truncated = checkpoint.clone();
        if let CheckpointPayload::JournalSuffix { journal, .. } = &mut truncated.payload {
            journal.len -= 1;
        }
        assert!(matches!(
            ExtensionState::restore(Some(&base), &truncated, TEST_LIMITS),
            Err(CheckpointError::MalformedCheckpoint { .. })
        ));

        let mut false_measurement = checkpoint;
        false_measurement.captured_entries += 1;
        assert_eq!(
            ExtensionState::restore(Some(&base), &false_measurement, TEST_LIMITS)
                .expect_err("false measurements are refused"),
            CheckpointError::MalformedCheckpoint {
                extension: base.descriptor.name.clone(),
                reason: "declared checkpoint measurements do not match its journal",
            }
        );
    }

    #[test]
    fn checkpoint_model_chains_preserve_exact_state_and_identity() {
        let mut seed = 0x4D59_5DF4_D0F3_3173u64;
        for mode in [
            CheckpointSemantics::JournalSuffix,
            CheckpointSemantics::FullJournal,
        ] {
            let mut state = state_with_checkpoint(0, mode);
            for round in 0..64usize {
                let base = state.clone();
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                let additions = (seed as usize % 9) + usize::from(round == 0);
                for offset in 0..additions {
                    let payload = seed
                        .wrapping_add(((round * 11 + offset) as u64).rotate_left(17))
                        .to_le_bytes();
                    state = state.push_entry(bytes(&payload));
                }
                let checkpoint = match mode {
                    CheckpointSemantics::JournalSuffix => state
                        .checkpoint(Some(&base), TEST_LIMITS)
                        .expect("model suffix captures"),
                    CheckpointSemantics::FullJournal => state
                        .checkpoint(None, TEST_LIMITS)
                        .expect("model full journal captures"),
                };
                let restored = match mode {
                    CheckpointSemantics::JournalSuffix => {
                        ExtensionState::restore(Some(&base), &checkpoint, TEST_LIMITS)
                    }
                    CheckpointSemantics::FullJournal => {
                        ExtensionState::restore(None, &checkpoint, TEST_LIMITS)
                    }
                }
                .expect("model checkpoint restores");
                assert_eq!(restored, state, "mode={mode:?}, round={round}");
                assert_eq!(
                    restored.content_digest(),
                    state.content_digest(),
                    "mode={mode:?}, round={round}"
                );
            }
        }
    }

    #[test]
    fn checkpoints_preserve_every_merge_contract_and_provenance_class() {
        for checkpoint_mode in [
            CheckpointSemantics::JournalSuffix,
            CheckpointSemantics::FullJournal,
        ] {
            for merge in [
                MergeSemantics::AppendOrdered,
                MergeSemantics::SetUnion,
                MergeSemantics::ConflictsRequireReview,
            ] {
                for provenance in [PayloadProvenance::Understood, PayloadProvenance::Opaque] {
                    let descriptor = ExtensionDescriptor {
                        name: Name::str(Name::anonymous(), "checkpointMatrixExt"),
                        merge,
                        checkpoint: checkpoint_mode,
                        provenance,
                    };
                    let base = ExtensionState::new(descriptor.clone()).push_entry(bytes(b"base"));
                    let target = base.push_entry(bytes(b"target"));
                    let checkpoint = match checkpoint_mode {
                        CheckpointSemantics::JournalSuffix => target
                            .checkpoint(Some(&base), TEST_LIMITS)
                            .expect("matrix suffix captures"),
                        CheckpointSemantics::FullJournal => target
                            .checkpoint(None, TEST_LIMITS)
                            .expect("matrix full journal captures"),
                    };
                    let restored = match checkpoint_mode {
                        CheckpointSemantics::JournalSuffix => {
                            ExtensionState::restore(Some(&base), &checkpoint, TEST_LIMITS)
                        }
                        CheckpointSemantics::FullJournal => {
                            ExtensionState::restore(None, &checkpoint, TEST_LIMITS)
                        }
                    }
                    .expect("matrix checkpoint restores");

                    assert_eq!(restored, target);
                    assert_eq!(restored.descriptor, descriptor);
                    assert_eq!(restored.provenance(), provenance);
                    assert_eq!(
                        restored.supports_fine_invalidation(),
                        provenance == PayloadProvenance::Understood
                    );

                    let ours = restored.push_entry(bytes(b"same-branch-entry"));
                    let theirs = restored.push_entry(bytes(b"same-branch-entry"));
                    match merge {
                        MergeSemantics::AppendOrdered => {
                            let merged = merge_with_test_limits(&restored, &ours, &theirs)
                                .expect("restored append contract remains executable");
                            assert_eq!(merged.len(), restored.len() + 2);
                            assert_eq!(
                                merged
                                    .entries()
                                    .skip(restored.len())
                                    .map(|entry| entry.payload.as_ref())
                                    .collect::<Vec<_>>(),
                                vec![b"same-branch-entry".as_slice(); 2]
                            );
                        }
                        MergeSemantics::SetUnion => {
                            let merged = merge_with_test_limits(&restored, &ours, &theirs)
                                .expect("restored set-union contract remains executable");
                            assert_eq!(
                                merged.len(),
                                restored.len() + 2,
                                "raw replay retains both branch entries"
                            );
                            assert_eq!(
                                semantic_len(&merged),
                                semantic_len(&restored) + 1,
                                "the exact-byte semantic view collapses the duplicate"
                            );
                            assert_eq!(
                                merged
                                    .entries()
                                    .skip(restored.len())
                                    .map(|entry| entry.payload.as_ref())
                                    .collect::<Vec<_>>(),
                                vec![b"same-branch-entry".as_slice(); 2]
                            );
                        }
                        MergeSemantics::ConflictsRequireReview => assert!(matches!(
                            merge_with_test_limits(&restored, &ours, &theirs),
                            Err(MergeConflict::ConcurrentChanges { .. })
                        )),
                    }
                }
            }
        }
    }

    #[test]
    fn checkpoint_work_matches_suffix_or_full_payload_not_base_history() {
        let suffix_base = state_with_checkpoint(4_096, CheckpointSemantics::JournalSuffix);
        for suffix_len in [0usize, 1, 31, 32, 33, 257] {
            let mut target = suffix_base.clone();
            for index in 0..suffix_len {
                target = target.push_entry(bytes(&(10_000u64 + index as u64).to_le_bytes()));
            }
            let (checkpoint, work) = target
                .checkpoint_with_work(
                    Some(&suffix_base),
                    TEST_LIMITS,
                    ProofBudget::UNBOUNDED,
                    &fixture_epoch(),
                )
                .expect("an unbounded proof budget cannot bind")
                .expect("suffix capture succeeds");
            assert_eq!(checkpoint.captured_entries(), suffix_len);
            assert_eq!(checkpoint.entries().count(), suffix_len);
            assert_eq!(work.captured_entries, suffix_len);
            assert!(
                work.prefix_lookup_steps <= target.journal.depth as usize + 1,
                "prefix lookup steps={} depth={}",
                work.prefix_lookup_steps,
                target.journal.depth
            );
        }

        let full = state_with_checkpoint(4_096, CheckpointSemantics::FullJournal);
        let (checkpoint, work) = full
            .checkpoint_with_work(None, TEST_LIMITS, ProofBudget::UNBOUNDED, &fixture_epoch())
            .expect("an unbounded proof budget cannot bind")
            .expect("full capture succeeds");
        assert_eq!(work.prefix_lookup_steps, 0);
        assert_eq!(work.captured_entries, full.len());
        assert_eq!(checkpoint.entries().count(), full.len());
    }

    #[test]
    fn environment_state_e2e_emits_detailed_real_path_evidence() {
        let run_id = std::env::var("FLN_ENV_E2E_RUN_ID")
            .unwrap_or_else(|_| "standalone-cargo-test".to_owned());
        assert!(
            run_id
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')),
            "E2E run id must be JSON-safe ASCII"
        );
        let limits = CheckpointLimits::new(1_000, 64_000);
        let extension_name = Name::str(Name::anonymous(), "e2eExt");
        let suffix_descriptor = ExtensionDescriptor {
            name: extension_name.clone(),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Understood,
        };

        let journal_started = Instant::now();
        let mut base = Environment::new()
            .register_extension(suffix_descriptor.clone())
            .expect("register real suffix extension");
        let mut expected_payloads = Vec::new();
        let mut journal_work = JournalAppendWork::default();
        for index in 0..64u64 {
            let payload = index.to_le_bytes();
            expected_payloads.push(payload.to_vec());
            let work = base
                .extension(&extension_name)
                .expect("base extension exists before append")
                .journal
                .next_append_work();
            journal_work.node_allocations += work.node_allocations;
            journal_work.copied_child_slots += work.copied_child_slots;
            journal_work.copied_entry_slots += work.copied_entry_slots;
            base = base
                .push_extension_entry(&extension_name, payload.as_slice())
                .expect("append real base entry");
        }
        let snapshot = base.clone();
        let mut target = base.clone();
        for index in 64..69u64 {
            let payload = index.to_le_bytes();
            expected_payloads.push(payload.to_vec());
            let work = target
                .extension(&extension_name)
                .expect("target extension exists before append")
                .journal
                .next_append_work();
            journal_work.node_allocations += work.node_allocations;
            journal_work.copied_child_slots += work.copied_child_slots;
            journal_work.copied_entry_slots += work.copied_entry_slots;
            target = target
                .push_extension_entry(&extension_name, payload.as_slice())
                .expect("append real suffix entry");
        }

        let mut rebuilt = Environment::new()
            .register_extension(suffix_descriptor.clone())
            .expect("register independent expected extension");
        for payload in &expected_payloads {
            rebuilt = rebuilt
                .push_extension_entry(&extension_name, payload.as_slice())
                .expect("append independent expected entry");
        }

        let base_state = base
            .extension(&extension_name)
            .expect("base extension exists");
        let snapshot_state = snapshot
            .extension(&extension_name)
            .expect("snapshot extension exists");
        let target_state = target
            .extension(&extension_name)
            .expect("target extension exists");
        assert_eq!(base_state, snapshot_state, "snapshot remains unchanged");
        assert_eq!(
            target, rebuilt,
            "incremental append matches independent replay"
        );

        let expected_order_hash = evidence_order_hash(expected_payloads.iter().map(Vec::as_slice));
        let actual_order_hash =
            evidence_order_hash(target_state.entries().map(|entry| entry.payload.as_ref()));
        assert_eq!(actual_order_hash, expected_order_hash);
        let base_nodes: HashSet<*const ()> = base_state.journal.node_ptrs().into_iter().collect();
        let target_nodes: HashSet<*const ()> =
            target_state.journal.node_ptrs().into_iter().collect();
        let shared_nodes = target_nodes.intersection(&base_nodes).count();
        let fresh_nodes = target_nodes.difference(&base_nodes).count();
        let (node_count, chunk_count) = journal_shape(&target_state.journal);
        assert_eq!(node_count, target_nodes.len());
        assert!(shared_nodes > 0, "fork must preserve shared journal nodes");
        assert!(
            fresh_nodes <= target_state.journal.depth as usize + 1,
            "final append path copies only one bounded path"
        );
        let expected_root = rebuilt.logical_root(&KVMap::new());
        let actual_root = target.logical_root(&KVMap::new());
        assert_eq!(actual_root, expected_root);
        println!(
            "{{\"schema\":\"fln.e2e.environment-state\",\"version\":1,\"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.5\",\"fln-amv.7\"],\"scenario\":\"persistent-journal\",\"status\":\"pass\",\"entry_count\":{},\"chunk_capacity\":{JOURNAL_CHUNK_CAPACITY},\"chunk_count\":{chunk_count},\"node_count\":{node_count},\"shared_node_count\":{shared_nodes},\"fresh_node_count\":{fresh_nodes},\"append_operations\":{},\"replay_operations\":{},\"node_allocations\":{},\"copied_child_slots\":{},\"copied_entry_slots\":{},\"payload_bytes\":{},\"expected_order_hash\":\"{expected_order_hash:016x}\",\"actual_order_hash\":\"{actual_order_hash:016x}\",\"expected_root\":\"{expected_root}\",\"actual_root\":\"{actual_root}\",\"snapshot_root\":\"{}\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
            target_state.len(),
            target_state.len(),
            target_state.entries().count(),
            journal_work.node_allocations,
            journal_work.copied_child_slots,
            journal_work.copied_entry_slots,
            target_state.journal.payload_bytes,
            snapshot.logical_root(&KVMap::new()),
            journal_started.elapsed().as_micros()
        );

        let suffix_started = Instant::now();
        let checkpoint = completed(target.checkpoint_extension(
            &extension_name,
            Some(&base),
            limits,
            ProofBudget::UNBOUNDED,
            &fixture_epoch(),
            None,
        ))
        .expect("capture through the real environment registry");
        let (instrumented_checkpoint, suffix_work) = target_state
            .checkpoint_with_work(
                Some(base_state),
                limits,
                ProofBudget::UNBOUNDED,
                &fixture_epoch(),
            )
            .expect("an unbounded proof budget cannot bind")
            .expect("measure the same real suffix capture");
        assert_eq!(checkpoint, instrumented_checkpoint);
        let restored = completed(base.apply_extension_checkpoint(
            &checkpoint,
            limits,
            ProofBudget::UNBOUNDED,
            None,
        ))
        .expect("apply through the real environment registry");
        assert_eq!(restored, target);
        let checkpoint_id = checkpoint_evidence_id(&checkpoint);
        let restored_state = restored
            .extension(&extension_name)
            .expect("restored extension exists");
        println!(
            "{{\"schema\":\"fln.e2e.environment-state\",\"version\":1,\"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.7\"],\"scenario\":\"checkpoint-roundtrip\",\"mode\":\"journal_suffix\",\"status\":\"pass\",\"base_id\":\"{}\",\"checkpoint_id\":\"{checkpoint_id}\",\"restored_id\":\"{}\",\"base_root\":\"{}\",\"checkpoint_base_root\":\"{}\",\"expected_root\":\"{}\",\"actual_root\":\"{}\",\"base_entries\":{},\"checkpoint_entries\":{},\"restored_entries\":{},\"payload_bytes\":{},\"prefix_lookup_steps\":{},\"capture_operations\":{},\"restore_operations\":{},\"entry_limit\":{},\"payload_byte_limit\":{},\"expected_outcome\":\"restored\",\"actual_outcome\":\"restored\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
            base_state.content_digest(),
            restored_state.content_digest(),
            base.logical_root(&KVMap::new()),
            checkpoint
                .base_state_digest()
                .expect("suffix checkpoint carries base identity"),
            target.logical_root(&KVMap::new()),
            restored.logical_root(&KVMap::new()),
            base_state.len(),
            checkpoint.captured_entries(),
            restored_state.len(),
            checkpoint.captured_payload_bytes(),
            suffix_work.prefix_lookup_steps,
            suffix_work.captured_entries,
            checkpoint.captured_entries(),
            limits.max_entries,
            limits.max_payload_bytes,
            suffix_started.elapsed().as_micros()
        );

        let full_started = Instant::now();
        let full_name = Name::str(Name::anonymous(), "e2eFullExt");
        let full_descriptor = ExtensionDescriptor {
            name: full_name.clone(),
            checkpoint: CheckpointSemantics::FullJournal,
            ..suffix_descriptor
        };
        let full_base = Environment::new()
            .register_extension(full_descriptor)
            .expect("register real full extension");
        let mut full_target = full_base.clone();
        for index in 0..37u64 {
            full_target = full_target
                .push_extension_entry(&full_name, index.to_le_bytes().as_slice())
                .expect("append full-journal entry");
        }
        let full_checkpoint = completed(full_target.checkpoint_extension(
            &full_name,
            None,
            limits,
            ProofBudget::UNBOUNDED,
            &fixture_epoch(),
            None,
        ))
        .expect("capture real full journal");
        let (_, full_work) = full_target
            .extension(&full_name)
            .expect("full target extension exists")
            .checkpoint_with_work(None, limits, ProofBudget::UNBOUNDED, &fixture_epoch())
            .expect("an unbounded proof budget cannot bind")
            .expect("measure the same real full capture");
        let full_restored = full_base.apply_extension_checkpoint(
            &full_checkpoint,
            limits,
            ProofBudget::UNBOUNDED,
            None,
        );
        let full_restored = completed(full_restored).expect("apply real full journal");
        assert_eq!(full_restored, full_target);
        println!(
            "{{\"schema\":\"fln.e2e.environment-state\",\"version\":1,\"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.7\"],\"scenario\":\"checkpoint-roundtrip\",\"mode\":\"full_journal\",\"status\":\"pass\",\"base_id\":null,\"checkpoint_id\":\"{}\",\"restored_id\":\"{}\",\"base_root\":null,\"checkpoint_base_root\":null,\"expected_root\":\"{}\",\"actual_root\":\"{}\",\"base_entries\":0,\"checkpoint_entries\":{},\"restored_entries\":{},\"payload_bytes\":{},\"prefix_lookup_steps\":{},\"capture_operations\":{},\"restore_operations\":{},\"entry_limit\":{},\"payload_byte_limit\":{},\"expected_outcome\":\"restored\",\"actual_outcome\":\"restored\",\"elapsed_us\":{},\"final_state\":\"verified\"}}",
            checkpoint_evidence_id(&full_checkpoint),
            full_restored
                .extension(&full_name)
                .expect("full restored extension exists")
                .content_digest(),
            full_target.logical_root(&KVMap::new()),
            full_restored.logical_root(&KVMap::new()),
            full_checkpoint.captured_entries(),
            full_restored
                .extension(&full_name)
                .expect("full restored extension exists")
                .len(),
            full_checkpoint.captured_payload_bytes(),
            full_work.prefix_lookup_steps,
            full_work.captured_entries,
            full_checkpoint.captured_entries(),
            limits.max_entries,
            limits.max_payload_bytes,
            full_started.elapsed().as_micros()
        );

        let divergence_case_started = Instant::now();
        let mut divergent = Environment::new()
            .register_extension(target_state.descriptor.clone())
            .expect("register divergent extension");
        for index in 0..64u64 {
            let payload = if index == 63 {
                u64::MAX.to_le_bytes()
            } else {
                index.to_le_bytes()
            };
            divergent = divergent
                .push_extension_entry(&extension_name, payload.as_slice())
                .expect("append divergent base entry");
        }
        let divergent_root_before = divergent.logical_root(&KVMap::new());
        let refusal = completed(divergent.apply_extension_checkpoint(
            &checkpoint,
            limits,
            ProofBudget::UNBOUNDED,
            None,
        ))
        .expect_err("divergent base must receive a typed refusal");
        assert!(matches!(
            refusal,
            crate::environment::EnvError::Checkpoint(CheckpointError::BaseHistoryMismatch { .. })
        ));
        let actual_outcome = "base_history_mismatch";
        assert_eq!(
            divergent.logical_root(&KVMap::new()),
            divergent_root_before,
            "failed apply is atomic"
        );
        let recovered = completed(base.apply_extension_checkpoint(
            &checkpoint,
            limits,
            ProofBudget::UNBOUNDED,
            None,
        ))
        .expect("clean recovery after typed refusal");
        assert_eq!(recovered, target);
        println!(
            "{{\"schema\":\"fln.e2e.environment-state\",\"version\":1,\"run_id\":\"{run_id}\",\"beads\":[\"fln-amv.7\"],\"scenario\":\"checkpoint-negative-recovery\",\"mode\":\"journal_suffix\",\"status\":\"pass\",\"base_id\":\"{}\",\"checkpoint_id\":\"{checkpoint_id}\",\"restored_id\":\"{}\",\"base_root_before\":\"{divergent_root_before}\",\"base_root_after\":\"{}\",\"expected_root\":\"{}\",\"actual_root\":\"{}\",\"base_entries\":{},\"checkpoint_entries\":{},\"restored_entries\":{},\"entry_limit\":{},\"payload_byte_limit\":{},\"expected_outcome\":\"base_history_mismatch\",\"actual_outcome\":\"{actual_outcome}\",\"recovery_outcome\":\"restored\",\"elapsed_us\":{},\"final_state\":\"clean_recovery\"}}",
            divergent
                .extension(&extension_name)
                .expect("divergent extension exists")
                .content_digest(),
            recovered
                .extension(&extension_name)
                .expect("recovered extension exists")
                .content_digest(),
            divergent.logical_root(&KVMap::new()),
            target.logical_root(&KVMap::new()),
            recovered.logical_root(&KVMap::new()),
            divergent
                .extension(&extension_name)
                .expect("divergent extension exists")
                .len(),
            checkpoint.captured_entries(),
            recovered
                .extension(&extension_name)
                .expect("recovered extension exists")
                .len(),
            limits.max_entries,
            limits.max_payload_bytes,
            divergence_case_started.elapsed().as_micros()
        );
    }

    // ---------------------------------------------------------------------------
    // Modelled refusal work facts (bead `fln-extension-merge-validation-proof-debt-dt5`).
    //
    // Follows this file's existing `JournalAppendWork`/`next_append_work` idiom: the work
    // is *modelled* rather than counted by instrumented production code. A counter in the
    // hot path would also be the weaker artifact — it reports what one run did, where a
    // model reports what the code can do at all.
    //
    // A counting allocator was never available as an alternative: no `#[global_allocator]`
    // exists anywhere in the workspace and D3's `#![forbid(unsafe_code)]` rules one out.
    // Recorded so the next reader does not rediscover that the obvious route is closed by
    // doctrine.
    // ---------------------------------------------------------------------------

    /// What a merge-stage *input* type puts within reach.
    trait StageInput {
        const REACHES_JOURNAL: bool;
        const REACHES_PAYLOAD: bool;
        /// An `ExtensionDescriptor` carries `merge`, so narrowing a stage to descriptors
        /// does **not** exclude policy *selection*. Recorded rather than glossed: this is
        /// the one criterion of the four that the narrowing does not buy.
        const CARRIES_MERGE_POLICY: bool;
    }

    impl StageInput for ExtensionDescriptor {
        const REACHES_JOURNAL: bool = false;
        const REACHES_PAYLOAD: bool = false;
        const CARRIES_MERGE_POLICY: bool = true;
    }

    impl StageInput for ExtensionState {
        const REACHES_JOURNAL: bool = true;
        const REACHES_PAYLOAD: bool = true;
        const CARRIES_MERGE_POLICY: bool = true;
    }

    /// What a stage's success type can carry out of it.
    trait StageOutput {
        const CARRIES_PRODUCT: bool;
    }

    impl StageOutput for () {
        const CARRIES_PRODUCT: bool = false;
    }

    impl StageOutput for ExtensionMergeOutcome {
        const CARRIES_PRODUCT: bool = true;
    }

    /// Operation facts for a refusal, as bounds rather than tallies.
    ///
    /// `Some(0)` means *provably zero* — the stage's signature puts the resource out of
    /// reach. `None` means the signature does not bound it, and is deliberately not
    /// spelled `Some(n)`: it records what is **not** proven instead of quietly reading as
    /// a zero. Conflating those two is how a partial result gets quoted as a whole one.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct RefusalWorkFacts {
        journal_comparisons: Option<usize>,
        payload_clones: Option<usize>,
        policy_selections: Option<usize>,
        product_publications: Option<usize>,
    }

    /// Derives the facts **from the stage function itself**.
    ///
    /// This is the whole point of the shape. `I` and `O` are inferred from the real
    /// function item that is passed in, so the facts are a function of the actual
    /// signature and cannot be transcribed beside it and left to rot. Widen
    /// `validate_descriptor_admission` to take `&ExtensionState` and `I` infers to
    /// `ExtensionState`, the zeros become `None`, and the test asserting `Some(0)` fails —
    /// in addition to `_DESCRIPTOR_ADMISSION_STAYS_JOURNAL_FREE` failing to compile.
    ///
    /// The stage argument is unused at run time by design: nothing is executed, because
    /// the claim is about reachability, not about one observed run.
    fn refusal_work_facts<I: StageInput, O: StageOutput>(
        _stage: fn(&I, &I, &I) -> Result<O, MergeConflict>,
    ) -> RefusalWorkFacts {
        let zero_unless = |unbounded: bool| if unbounded { None } else { Some(0) };
        RefusalWorkFacts {
            journal_comparisons: zero_unless(I::REACHES_JOURNAL),
            payload_clones: zero_unless(I::REACHES_PAYLOAD),
            policy_selections: zero_unless(I::CARRIES_MERGE_POLICY),
            product_publications: zero_unless(O::CARRIES_PRODUCT),
        }
    }

    /// Stage 1's refusal work facts, derived from stage 1.
    ///
    /// Three of the criteria's four operations are provably zero. The fourth is not, and
    /// saying so is the point: `dt5` exists because closure evidence outran its own
    /// criteria, so a fact set that rounded `policy_selections` up to zero would repeat
    /// that on the correcting bead.
    #[test]
    fn descriptor_refusal_work_facts_are_zero_by_construction() {
        let facts = refusal_work_facts(validate_descriptor_admission);
        assert_eq!(
            facts.journal_comparisons,
            Some(0),
            "stage 1 takes descriptors, so no journal is in reach"
        );
        assert_eq!(
            facts.payload_clones,
            Some(0),
            "stage 1 takes descriptors, so no payload is in reach"
        );
        assert_eq!(
            facts.product_publications,
            Some(0),
            "stage 1 succeeds with (), so no product can leave it"
        );
        assert_eq!(
            facts.policy_selections, None,
            "STILL not discharged at this stage, and must not be recorded as zero: \
             ExtensionDescriptor carries `merge`, so narrowing to descriptors does not \
             put policy selection out of reach of the conflict construction. The \
             *decision* half IS now closed, by parametricity rather than by this model — \
             see descriptors_agree and \
             the_stage_one_decision_cannot_see_a_policy_because_it_cannot_see_a_field. \
             This fact stays None because it describes validate_descriptor_admission, \
             which still holds concrete descriptors"
        );
    }

    /// The model is not a constant — the negative control.
    ///
    /// Without this, every zero above would be satisfied by a function that ignored its
    /// type parameters and returned `Some(0)` four times, and the whole artifact would be
    /// decoration. A guard whose passing state is reachable without the property holding
    /// is not a guard.
    #[test]
    fn the_refusal_work_model_reads_the_signature_it_is_given() {
        fn stage_over_states(
            _: &ExtensionState,
            _: &ExtensionState,
            _: &ExtensionState,
        ) -> Result<ExtensionMergeOutcome, MergeConflict> {
            unreachable!("never executed: the model is about reachability, not a run")
        }

        let wide = refusal_work_facts(stage_over_states);
        assert_eq!(wide.journal_comparisons, None);
        assert_eq!(wide.payload_clones, None);
        assert_eq!(wide.product_publications, None);
        assert_ne!(
            wide,
            refusal_work_facts(validate_descriptor_admission),
            "the facts must differ between a narrow and a wide stage, or they are not \
             derived from the signature at all"
        );
    }

    /// The stage-1 decision is parametric, and stays that way.
    ///
    /// Instantiating `descriptors_agree` at a type that is *only* `Eq` — one with no
    /// fields a descriptor has, and in particular no `merge` — is the compile-time join.
    /// Specialising the function to `&ExtensionDescriptor`, which is the edit that would
    /// silently restore the ability to branch on a policy inside the decision, stops this
    /// from compiling. Same device as `_DESCRIPTOR_ADMISSION_STAYS_JOURNAL_FREE`, one
    /// abstraction further in: that one pins *which* type, this pins *that there is none*.
    #[test]
    fn the_stage_one_decision_cannot_see_a_policy_because_it_cannot_see_a_field() {
        #[derive(PartialEq, Eq)]
        struct OpaqueToken(u8);

        assert!(descriptors_agree(
            &OpaqueToken(7),
            &OpaqueToken(7),
            &OpaqueToken(7)
        ));
        assert!(!descriptors_agree(
            &OpaqueToken(7),
            &OpaqueToken(7),
            &OpaqueToken(9)
        ));
    }

    /// Stage 1 privileges no merge policy — checked over **every** assignment, not a
    /// sample.
    ///
    /// `MergeSemantics` has exactly three variants, so the 27 base/ours/theirs
    /// assignments are exhaustible, and an exhaustive check is a different claim class
    /// from a sampled one. The property: a refusal happens exactly when the three
    /// descriptors disagree, and never because of *which* policy is present — so
    /// `ConflictsRequireReview` gets no special early exit at stage 1, which is the
    /// shape a premature dispatch would take.
    #[test]
    fn stage_one_admission_is_invariant_under_every_policy_assignment() {
        const POLICIES: [MergeSemantics; 3] = [
            MergeSemantics::AppendOrdered,
            MergeSemantics::SetUnion,
            MergeSemantics::ConflictsRequireReview,
        ];
        let with = |merge: MergeSemantics| ExtensionDescriptor {
            merge,
            ..descriptor(MergeSemantics::AppendOrdered, PayloadProvenance::Understood)
        };

        let mut assignments = 0;
        for base in POLICIES {
            for ours in POLICIES {
                for theirs in POLICIES {
                    assignments += 1;
                    let refused =
                        validate_descriptor_admission(&with(base), &with(ours), &with(theirs))
                            .is_err();
                    assert_eq!(
                        refused,
                        !(base == ours && base == theirs),
                        "stage 1 must refuse on disagreement alone, never on which policy \
                         is present: base={base:?} ours={ours:?} theirs={theirs:?}"
                    );
                }
            }
        }
        assert_eq!(
            assignments,
            POLICIES.len().pow(3),
            "the sweep must be exhaustive over MergeSemantics, not a sample — if a \
             variant is added, this count is what notices"
        );
    }

    /// The cross-check the model cannot give: a real refusal leaves sharing and roots
    /// alone.
    ///
    /// The model bounds what stage 1 *can* reach. This drives an actual descriptor
    /// refusal and asserts the criteria's separate requirement that "inputs, roots,
    /// sharing, and cache state remain unchanged after every refusal" — observed through
    /// the one channel available without an allocator hook: `Arc::strong_count` over the
    /// payloads, which a refusal that cloned a handle would move.
    #[test]
    fn a_real_descriptor_refusal_disturbs_no_sharing_and_no_root() {
        let expected = descriptor(MergeSemantics::AppendOrdered, PayloadProvenance::Understood);
        let shared: Arc<[u8]> = Arc::from(&b"shared-payload"[..]);
        let base = ExtensionState::new(expected.clone()).push_entry(Arc::clone(&shared));
        let ours = base.push_entry(Arc::clone(&shared));
        let mismatched = ExtensionState::new(ExtensionDescriptor {
            provenance: PayloadProvenance::Opaque,
            ..expected.clone()
        })
        .push_entry(Arc::clone(&shared));

        let sharing_before = Arc::strong_count(&shared);
        let roots_before = (
            base.content_digest(),
            ours.content_digest(),
            mismatched.content_digest(),
        );
        let inputs_before = (base.clone(), ours.clone(), mismatched.clone());

        let refusal = ExtensionState::merge(&base, &ours, &mismatched, TEST_SET_UNION_LIMITS)
            .expect_err("a descriptor mismatch is refused");
        assert!(matches!(refusal, MergeConflict::DescriptorMismatch { .. }));

        assert_eq!(
            Arc::strong_count(&shared),
            sharing_before,
            "a refusal that cloned a payload handle would move the strong count"
        );
        assert_eq!(
            (
                base.content_digest(),
                ours.content_digest(),
                mismatched.content_digest(),
            ),
            roots_before,
            "a refusal must expose no root movement"
        );
        assert_eq!(
            (base, ours, mismatched),
            inputs_before,
            "a refusal must leave every input unchanged"
        );
    }

    // ---------------------------------------------------------------------------
    // Merge-validation mutation record and the two facts it exposed
    // (bead `fln-extension-merge-validation-proof-debt-dt5`).
    // ---------------------------------------------------------------------------

    /// What happened when one merge-validation defect was planted and the suite run.
    enum MutantOutcome {
        /// A named test failed for the intended divergence. The **function item** is
        /// held, not its name as a string: renaming or deleting the killer is then a
        /// compile error rather than a silently stale record.
        KilledBy(fn()),
        /// The mutation cannot change observable behaviour, so no test can kill it and
        /// none should be written. An equivalent mutant is not a coverage gap, and
        /// recording it as one manufactures permanent phantom debt.
        EquivalentBecause(&'static str),
        /// Planted, compiled, run — and **nothing failed**, while the mutation is *not*
        /// equivalent: it changes behaviour this bead's criteria name as load-bearing.
        ///
        /// The three explanations for a survivor — missing test, unreachable code,
        /// equivalent mutant — demand opposite responses, so a survivor is only
        /// classifiable once the reachability and equivalence questions are answered
        /// rather than assumed. This variant is the answer "missing test", and it
        /// carries the obligation it fails so the debt names its own discharge.
        SurvivedUncovered {
            /// What the run actually showed.
            measured: &'static str,
            /// The acceptance-criteria clause with no assertion behind it.
            obligation: &'static str,
        },
        /// The mutation can no longer be **written**: the stage it targeted was narrowed
        /// so the defect is not expressible there.
        ///
        /// Strictly stronger than a kill, and the difference is maintenance rather than
        /// strength at one instant: a killed mutant stays dead only while some test keeps
        /// failing for it, and this bead exists because nobody was watching that join. A
        /// prevented one needs nothing to keep working — the compiler refuses.
        ///
        /// It carries `still_unproven` because prevention is narrow. Making a defect
        /// inexpressible proves the code cannot do that thing; it does not discharge every
        /// obligation the defect was standing in for, and a classification that omitted the
        /// remainder would let a structural win read as a larger closure than it is.
        StructurallyPrevented {
            /// The constraint that makes the mutation inexpressible.
            by: &'static str,
            /// What that constraint does **not** establish.
            still_unproven: &'static str,
        },
    }

    /// The measured campaign, 2026-07-26: fourteen defects planted one at a time on the
    /// merge-validation plane, the `fln-env` suite run against each, source restored
    /// byte-exactly between plants. Twelve killed, one equivalent, and one survivor that
    /// was a real gap and is now **structurally prevented** rather than merely asserted
    /// against — see `validate_descriptor_admission`, and note what that repair explicitly
    /// does not establish.
    ///
    /// # The count was itself the defect
    ///
    /// The first pass planted **twelve** and this table asserted `len() == 12`. The
    /// acceptance criteria name **fourteen**, so the record certified its own
    /// completeness against a number rather than against the criteria that define it —
    /// which is the exact failure `dt5` was filed to correct, reproduced inside the
    /// correcting artifact. `policy_before_validation` and `clone_payloads_during_refusal`
    /// were the two never planted; both have now been run, and they landed on opposite
    /// sides: the first dies, the second survives uncovered.
    ///
    /// # Why this table exists at all
    ///
    /// `dt5` was filed because `fln-amv.3`/`.4` closed without demonstrating their named
    /// mutation matrix, and the measurement showed the debt was **not** what it looked
    /// like: eleven of the twelve already died, under ordinary behaviour-test names.
    /// The killing assertions existed; nothing *named* them. That is the whole exposure
    /// — a refactor that weakened `invalid_branch_history_is_a_typed_conflict` would
    /// silently take four ancestry mutants and the unordered-comparison mutant with it,
    /// and no artifact would record the loss.
    ///
    /// Holding function items binds the record to the compiler, in the same way
    /// `franken_lean-oh1j` bound its variant count rather than maintaining a number.
    const MERGE_VALIDATION_MUTANTS: &[(&str, MutantOutcome)] = &[
        (
            "descriptor_skip_name",
            MutantOutcome::KilledBy(mismatched_descriptors_are_typed_conflicts_on_either_branch),
        ),
        (
            "descriptor_skip_merge",
            MutantOutcome::KilledBy(mismatched_descriptors_are_typed_conflicts_on_either_branch),
        ),
        (
            "descriptor_skip_checkpoint",
            MutantOutcome::KilledBy(mismatched_descriptors_are_typed_conflicts_on_either_branch),
        ),
        (
            "descriptor_skip_provenance",
            MutantOutcome::KilledBy(mismatched_descriptors_are_typed_conflicts_on_either_branch),
        ),
        (
            "descriptor_validation_deferred",
            MutantOutcome::KilledBy(mismatched_descriptors_are_typed_conflicts_on_either_branch),
        ),
        (
            "ancestry_skipped",
            MutantOutcome::KilledBy(invalid_branch_history_is_a_typed_conflict),
        ),
        (
            "ancestry_only_length",
            MutantOutcome::KilledBy(invalid_branch_history_is_a_typed_conflict),
        ),
        (
            "ancestry_only_ours",
            MutantOutcome::KilledBy(invalid_branch_history_is_a_typed_conflict),
        ),
        (
            "ancestry_only_theirs",
            MutantOutcome::KilledBy(invalid_branch_history_is_a_typed_conflict),
        ),
        (
            "compare_entries_unordered",
            MutantOutcome::KilledBy(invalid_branch_history_is_a_typed_conflict),
        ),
        (
            "continue_after_refusal",
            MutantOutcome::KilledBy(set_union_limits_are_independent_atomic_and_recoverable),
        ),
        (
            "expose_partial_product",
            MutantOutcome::EquivalentBecause(
                "ExtensionState::merge pre-tests both of the projection's refusal \
                 conditions over the same multiset before calling it, and both are \
                 order-independent, so the projection's Inconclusive arm cannot fire on \
                 the merge path; replacing it changes no observable behaviour there. The \
                 arm IS live for the other caller, semantic_projection, which is covered \
                 by semantic_projection_refuses_typed_on_every_resource_and_exposes_no_view.",
            ),
        ),
        (
            "policy_before_validation",
            MutantOutcome::KilledBy(mismatched_descriptors_are_typed_conflicts_on_either_branch),
        ),
        (
            "clone_payloads_during_refusal",
            MutantOutcome::StructurallyPrevented {
                by: "validate_descriptor_admission takes three &ExtensionDescriptor and \
                     returns Result<(), MergeConflict>, so stage 1 has no journal, no \
                     payload and no product type in scope. The mutation body \
                     ours.entries().map(|e| e.payload.to_vec()) no longer compiles there. \
                     Measured first: as an inline guard it SURVIVED the full suite \
                     239/239, because the returned conflict is byte-identical and nothing \
                     observed the copying. _DESCRIPTOR_ADMISSION_STAYS_JOURNAL_FREE pins \
                     the signature so widening it back is a compile error at a named site.",
                still_unproven: "The operation/allocation FACTS the criteria separately \
                                 demand. Nothing counts or reports journal comparisons, \
                                 payload clones, policy dispatches or product \
                                 publications, and the refusal does still clone the three \
                                 descriptors — legitimately, since they are what the \
                                 conflict is made of. Prevention bounds what stage 1 CAN \
                                 do; it produces no facts about what it DID.",
            },
        ),
    ];

    /// The mutant kinds `dt5`'s acceptance criteria name, transcribed from the bead.
    ///
    /// # What this does and does not buy
    ///
    /// It upgrades the completeness check from a **count** to a **set**: the previous
    /// assertion was `len() == 12`, a number the author chose, which is satisfied by any
    /// twelve entries and cannot report *which* criterion is unmet. Binding to names
    /// makes a missing mutant say its own name.
    ///
    /// It does **not** close the join. This list is a transcription, so a criteria edit
    /// on the bead still moves nothing here — the same shape as `AGENTS.md`'s item 7,
    /// one artifact over. `mandated_mutants.rs` closes its version of this join by
    /// deriving the names from `AGENTS.md` at test time; the equivalent move here would
    /// derive from `.beads/issues.jsonl`, which is `fln-conformance`'s territory, not a
    /// unit test's. Recorded as a known limit rather than implied to be a mechanism.
    const CRITERIA_NAMED_MUTANTS: [&str; 14] = [
        "descriptor_skip_name",
        "descriptor_skip_merge",
        "descriptor_skip_checkpoint",
        "descriptor_skip_provenance",
        "descriptor_validation_deferred",
        "policy_before_validation",
        "clone_payloads_during_refusal",
        "expose_partial_product",
        "ancestry_skipped",
        "ancestry_only_length",
        "ancestry_only_ours",
        "ancestry_only_theirs",
        "compare_entries_unordered",
        "continue_after_refusal",
    ];

    /// The record covers the campaign and distinguishes a kill from an equivalence.
    ///
    /// The distinction is the point. A surviving mutant has three explanations — a
    /// missing test, unreachable code, or a mutation that cannot change behaviour — and
    /// they demand opposite responses. Filing an equivalent mutant as a gap creates debt
    /// that can never be discharged, because the test it asks for cannot exist.
    #[test]
    fn the_merge_validation_mutation_record_is_complete_and_classified() {
        let names: BTreeSet<&str> = MERGE_VALIDATION_MUTANTS
            .iter()
            .map(|(name, _)| *name)
            .collect();
        assert_eq!(
            names.len(),
            MERGE_VALIDATION_MUTANTS.len(),
            "a duplicated mutant name hides a missing one"
        );
        // Set equality in *both* directions. One direction alone lets the matrix drift:
        // subset-only would readmit the 12-of-14 state this test was measured out of,
        // and superset-only would let an entry sit here under a name no criterion names.
        let criteria: BTreeSet<&str> = CRITERIA_NAMED_MUTANTS.into_iter().collect();
        assert_eq!(
            criteria.len(),
            CRITERIA_NAMED_MUTANTS.len(),
            "the criteria transcription itself must not duplicate a name"
        );
        let missing: Vec<&&str> = criteria.difference(&names).collect();
        assert!(
            missing.is_empty(),
            "acceptance criteria name mutants absent from the record: {missing:?}"
        );
        let unnamed: Vec<&&str> = names.difference(&criteria).collect();
        assert!(
            unnamed.is_empty(),
            "record holds mutants no criterion names: {unnamed:?}"
        );
        let killed = MERGE_VALIDATION_MUTANTS
            .iter()
            .filter(|(_, outcome)| matches!(outcome, MutantOutcome::KilledBy(_)))
            .count();
        let equivalent = MERGE_VALIDATION_MUTANTS
            .iter()
            .filter(|(_, outcome)| matches!(outcome, MutantOutcome::EquivalentBecause(_)))
            .count();
        let uncovered = MERGE_VALIDATION_MUTANTS
            .iter()
            .filter(|(_, outcome)| matches!(outcome, MutantOutcome::SurvivedUncovered { .. }))
            .count();
        let prevented = MERGE_VALIDATION_MUTANTS
            .iter()
            .filter(|(_, outcome)| matches!(outcome, MutantOutcome::StructurallyPrevented { .. }))
            .count();
        // Asserted BY NAME and FIRST, and both parts are load-bearing rather than cosmetic.
        //
        // First, by name: a tally says `left: 13 right: 12` and leaves the reader to work
        // out which entry moved and why that is wrong. Naming the entry states the claim.
        //
        // Second, first: when the counts sat in tally order, every way of falsely
        // discharging this entry was caught by an earlier bare count mismatch, so the one
        // message that explains the mistake could never run. Measured, not assumed —
        // reclassifying the survivor to `KilledBy` failed with `left: 13 right: 12`. A
        // diagnostic that cannot fire is the untruthful contract `environment.rs` names.
        let survivor = MERGE_VALIDATION_MUTANTS
            .iter()
            .find(|(name, _)| *name == "clone_payloads_during_refusal")
            .map(|(_, outcome)| outcome)
            .expect("the measured survivor must stay in the record under its own name");
        assert!(
            matches!(survivor, MutantOutcome::StructurallyPrevented { .. }),
            "clone_payloads_during_refusal was MEASURED surviving the full suite and was \
             repaired by narrowing stage 1 so it cannot be written. Relabelling it killed \
             or equivalent without restoring an assertion, or dropping it, is how a \
             structural repair gets read as a larger closure than it earned"
        );
        // A wall on purpose. A survivor found by a later campaign is real debt and must
        // redden the build until it is recorded here deliberately with its obligation
        // named — an unwritten-down survivor is the exact state this bead was filed about.
        assert_eq!(
            uncovered, 0,
            "an uncovered mutant is open debt: repair it and reclassify, never drop it \
             from the matrix and never relabel it without an assertion that actually kills"
        );
        assert_eq!(prevented, 1);
        assert_eq!(killed, 12);
        assert_eq!(equivalent, 1);
        assert_eq!(
            killed + equivalent + uncovered + prevented,
            CRITERIA_NAMED_MUTANTS.len()
        );
        for (name, outcome) in MERGE_VALIDATION_MUTANTS {
            assert_classification_is_well_formed(name, outcome);
        }
    }

    /// Every classification must carry the argument that makes it a classification rather
    /// than a label. Extracted from the loop so it can be applied to *constructed*
    /// variants too — the record currently contains no `SurvivedUncovered` entry, so
    /// checking these rules only against the table would leave that arm's discipline
    /// unexercised, and an unexercised rule is how the next survivor gets recorded as a
    /// bare "it survived".
    fn assert_classification_is_well_formed(name: &str, outcome: &MutantOutcome) {
        match outcome {
            // Reading the item is what binds the record to the compiler. The reference in
            // the table above is already a use, so renaming or deleting a killer fails the
            // build rather than leaving a stale string behind — the exposure this closes.
            MutantOutcome::KilledBy(killer) => {
                let _killer: fn() = *killer;
            }
            // An equivalence must carry its argument. "It survived" is not a
            // classification, and an unargued equivalence is how a real gap gets dismissed
            // as a phantom.
            MutantOutcome::EquivalentBecause(reason) => assert!(
                reason.len() > 80,
                "{name}: an equivalence claim must state why behaviour cannot change"
            ),
            // A survivor must carry both halves. "It survived" is not a finding, and a
            // survivor without its unmet obligation is indistinguishable from an
            // equivalence nobody argued.
            MutantOutcome::SurvivedUncovered {
                measured,
                obligation,
            } => {
                assert!(
                    measured.len() > 80,
                    "{name}: a survivor must state what the run showed"
                );
                assert!(
                    obligation.len() > 40,
                    "{name}: a survivor must name the obligation it leaves unmet"
                );
            }
            // Prevention must carry BOTH halves. The constraint alone reads as a clean
            // win; the remainder is what stops it being quoted as one.
            MutantOutcome::StructurallyPrevented { by, still_unproven } => {
                assert!(
                    by.len() > 80,
                    "{name}: prevention must name the constraint that makes the mutation \
                     inexpressible, not merely assert that it is"
                );
                assert!(
                    still_unproven.len() > 80,
                    "{name}: prevention is narrow — it must state what it does NOT \
                     establish, or a structural win reads as a larger closure"
                );
            }
        }
    }

    /// The vocabulary for recording a *measured survivor* stays available and stays
    /// checked, even though the record holds none today.
    ///
    /// `clone_payloads_during_refusal` was the only `SurvivedUncovered` entry and its
    /// repair reclassified it, which would leave the variant unconstructed. Deleting it to
    /// satisfy the dead-code lint is the wrong repair and worth naming: the next campaign
    /// that finds a survivor would reach for the nearest surviving label, and the nearest
    /// one is `EquivalentBecause` — turning a real gap into a dismissed phantom, which is
    /// the precise error this bead's own criteria forbid in the other direction.
    #[test]
    fn a_measured_survivor_remains_recordable_and_must_argue_both_halves() {
        let well_formed = MutantOutcome::SurvivedUncovered {
            measured: "A planted defect compiled, ran, and no test failed, while the path \
                       it sits on is demonstrably reached by an existing passing test.",
            obligation: "The acceptance-criteria clause that has no assertion behind it.",
        };
        assert_classification_is_well_formed("exemplar", &well_formed);

        // And the discipline actually bites: a bare survivor is rejected.
        let bare = MutantOutcome::SurvivedUncovered {
            measured: "it survived",
            obligation: "",
        };
        assert!(
            std::panic::catch_unwind(|| assert_classification_is_well_formed("bare", &bare))
                .is_err(),
            "a survivor recorded without its measurement and obligation must be refused"
        );
    }

    /// The public projection refuses typed on every resource and exposes no view.
    ///
    /// # The coverage hole the campaign found
    ///
    /// [`ExtensionState::semantic_projection`] is public and calls
    /// `project_set_union_entries` with **no** pre-checks, so its refusal arm is live.
    /// A reachability probe — planting a `panic!` in that arm and running the suite —
    /// showed no test reached it by any route. The `expose_partial_product` mutant
    /// survived on the merge path because it is equivalent there, and that equivalence
    /// was masking a genuinely untested public path one caller over.
    ///
    /// FL-INV-07: a refusal is typed, carries the exact resource and both numbers, and
    /// yields no product — the semantic view must not become observable on a path that
    /// did not admit the complete projection, which is what that method's own doc
    /// promises.
    #[test]
    fn semantic_projection_refuses_typed_on_every_resource_and_exposes_no_view() {
        let mut state = ExtensionState::new(descriptor(
            MergeSemantics::SetUnion,
            PayloadProvenance::Understood,
        ));
        for payload in [b"aa".as_slice(), b"bbbb".as_slice(), b"cc".as_slice()] {
            state = state.push_entry(bytes(payload));
        }
        let raw_entries = state.len();
        let raw_payload_bytes = state.journal.payload_bytes;
        assert_eq!(raw_entries, 3);
        assert_eq!(raw_payload_bytes, 8);

        // Generous on every axis: the complete projection is observable, which is the
        // premise each refusal below is measured against.
        let generous = SetUnionLimits::new(raw_entries, raw_payload_bytes, 4);
        let SetUnionProjection::Complete { entries, facts } = state.semantic_projection(generous)
        else {
            unreachable!("an adequate budget must admit the complete projection")
        };
        assert_eq!(entries.len(), 3);
        assert_eq!(facts.examined_entries, 3);

        // One binding axis at a time, so a refusal names the resource under test rather
        // than whichever the frozen order reached first.
        for (resource, limits, allowed, observed) in [
            (
                SetUnionResource::Entries,
                SetUnionLimits::new(raw_entries - 1, raw_payload_bytes, 4),
                (raw_entries - 1) as u128,
                raw_entries as u128,
            ),
            (
                SetUnionResource::PayloadBytes,
                SetUnionLimits::new(raw_entries, raw_payload_bytes - 1, 4),
                raw_payload_bytes - 1,
                raw_payload_bytes,
            ),
            (
                SetUnionResource::EntryBytes,
                SetUnionLimits::new(raw_entries, raw_payload_bytes, 3),
                3,
                4,
            ),
        ] {
            let SetUnionProjection::Inconclusive { reason, .. } = state.semantic_projection(limits)
            else {
                unreachable!("{resource:?} must refuse rather than project")
            };
            assert_eq!(reason.resource, resource);
            assert_eq!(reason.limit, allowed);
            assert_eq!(reason.actual, observed);
            assert!(
                reason.actual > reason.limit,
                "{resource:?}: a stop must report spending past its allowance"
            );
        }

        // The state is a persistent value; refusing cannot have altered it.
        assert_eq!(state.len(), raw_entries);
        assert_eq!(state.journal.payload_bytes, raw_payload_bytes);
    }

    /// **The duplicated refusal authority, decided rather than tolerated.**
    ///
    /// `project_set_union_entries` has two callers with different preconditions:
    /// [`ExtensionState::merge`], which pre-tests the same limits, and
    /// [`ExtensionState::semantic_projection`], which does not. So the projection's own
    /// checks are *redundant* for one caller and *load-bearing* for the other. That is a
    /// legitimate shape, but nothing recorded which stage is the authority, and "a check
    /// that cannot fire is not defence in depth, it is an untruthful contract"
    /// (`environment::PreparedDeclarationAdmission::commit`) applies to whichever copy is
    /// dead.
    ///
    /// **The decision: on the merge path the EARLY stages are the authority**, and they
    /// stay. Merge refuses before computing the canonical branch order and before the
    /// projection's O(n) walk, so the cheap refusal is the point. The projection's checks
    /// stay too, because deleting them would leave `semantic_projection` unguarded.
    ///
    /// **What makes that a decision rather than a comment**: the two stages report
    /// *different facts* for the same breach, and this pins which one a caller sees. The
    /// entry-limit stage scans every entry, so it reports the true maximum and a full
    /// `examined_entries`; the projection stops at the first oversized entry, so it would
    /// report that entry's size and a partial count. Deleting merge's pre-check would
    /// therefore still refuse — silently changing the reported evidence. This test fails
    /// if that happens.
    #[test]
    fn merge_refuses_at_its_own_early_stage_not_inside_the_projection() {
        fn set_state(payloads: &[&[u8]]) -> ExtensionState {
            let mut state = ExtensionState::new(descriptor(
                MergeSemantics::SetUnion,
                PayloadProvenance::Understood,
            ));
            for payload in payloads {
                state = state.push_entry(bytes(payload));
            }
            state
        }

        // The oversized entry is LAST and is not the first to breach, so the two stages
        // are distinguishable: a first-breach reporter would name `bbb` (3 bytes), the
        // scanning reporter names the true maximum `ccccc` (5 bytes).
        let base = set_state(&[]);
        let ours = set_state(&[b"a", b"bbb"]);
        let theirs = set_state(&[b"ccccc"]);
        let limits = SetUnionLimits::new(8, 64, 2);

        let ExtensionMergeOutcome::Inconclusive { reason, facts } =
            ExtensionState::merge(&base, &ours, &theirs, limits)
                .expect("valid SetUnion histories do not conflict")
        else {
            unreachable!("an entry over the byte limit must refuse")
        };
        assert_eq!(reason.resource, SetUnionResource::EntryBytes);
        // The authority: the true maximum across every entry, not the first breach.
        assert_eq!(
            reason.actual, 5,
            "merge must report the scanned maximum; reporting 3 means the projection \
             refused instead and merge's early stage was removed"
        );
        assert_eq!(reason.limit, 2);
        // And it scanned all of them, which the projection's early return would not.
        assert_eq!(
            facts.examined_entries, 3,
            "the entry-limit stage scans every entry; a partial count means a \
             first-breach reporter answered"
        );
        assert_eq!(facts.maximum_entry_bytes, 5);
    }

    // ---------------------------------------------------------------------------
    // UNIT AND MODEL TABLES for merge validation
    // (bead `fln-extension-merge-validation-proof-debt-dt5`).
    //
    // These discharge the acceptance paragraph beginning "Unit tables and independent
    // generated models cover ...". Each table names the clause it answers, and where it
    // answers only part of one it says which part.
    //
    // # Why every dimension here is generated rather than listed
    //
    // The clause says "every invalid prefix class" and "all merge policies". A
    // hand-written table satisfies wording like that at the instant it is written and
    // stops satisfying it, silently, the moment a variant or a field is added — the
    // hand-listed-scope defect `AGENTS.md` records, and the reason this bead exists at
    // all. So every dimension below is either walked from a successor chain, so a new
    // variant fails to compile until it joins, or recovered from the fixture data by a
    // computed predicate, so a fixture that stops exhibiting its property fails.
    // ---------------------------------------------------------------------------

    /// A closed set of case values, walked from a successor chain.
    ///
    /// Factored from the `succ_merge_semantics` idiom already in this file rather than
    /// re-rolled per dimension. `succ` forces a new variant to join the chain — the
    /// exhaustive match stops compiling — and `COUNT` is checked in *both* directions by
    /// [`CaseDimension::all`], because a chain that is too long and one that orphans a
    /// variant are different mistakes and only the second is caught by an upper bound.
    trait CaseDimension: Copy + PartialEq + std::fmt::Debug + Sized {
        const FIRST: Self;
        const COUNT: usize;

        fn succ(self) -> Option<Self>;

        fn all() -> Vec<Self> {
            let mut values: Vec<Self> = Vec::with_capacity(Self::COUNT);
            let mut next = Some(Self::FIRST);
            while let Some(value) = next {
                assert!(
                    values.len() < Self::COUNT,
                    "{}: the successor chain yields more values than COUNT — a variant is \
                     double-counted or the chain cycles",
                    std::any::type_name::<Self>()
                );
                values.push(value);
                next = value.succ();
            }
            assert_eq!(
                values.len(),
                Self::COUNT,
                "{}: the successor chain yields fewer values than COUNT — a variant is \
                 orphaned, which is the one way to satisfy every exhaustive match and \
                 still fall out of the tables",
                std::any::type_name::<Self>()
            );
            values
        }

        /// A value **guaranteed different** from `self`, selected by `salt`.
        ///
        /// Named by position on the chain rather than by naming a second variant, so
        /// adding a variant does not leave this reaching for a stale one.
        ///
        /// The step is `1 + salt % (COUNT - 1)`, which is never `0 mod COUNT`. The
        /// obvious `1 + salt` is wrong and was written first: on a two-variant dimension
        /// `rotate(2)` is the identity, so a `salt = 1` perturbation of `Checkpoint` or
        /// `Provenance` changed nothing and the difference table quietly measured a
        /// no-op. `every_descriptor_field_perturbation_changes_exactly_that_field` caught
        /// it, which is the only reason that control exists.
        fn other(self, salt: usize) -> Self {
            let values = Self::all();
            assert!(
                values.len() >= 2,
                "{}: a one-value dimension has no different value to offer",
                std::any::type_name::<Self>()
            );
            let index = values
                .iter()
                .position(|value| *value == self)
                .expect("every value of a closed dimension is on its own chain");
            let step = 1 + salt % (values.len() - 1);
            values[(index + step) % values.len()]
        }
    }

    impl CaseDimension for MergeSemantics {
        const FIRST: Self = FIRST_MERGE_SEMANTICS;
        const COUNT: usize = MERGE_SEMANTICS_VARIANTS;
        fn succ(self) -> Option<Self> {
            succ_merge_semantics(self)
        }
    }

    impl CaseDimension for CheckpointSemantics {
        const FIRST: Self = FIRST_CHECKPOINT_SEMANTICS;
        const COUNT: usize = CHECKPOINT_SEMANTICS_VARIANTS;
        fn succ(self) -> Option<Self> {
            succ_checkpoint_semantics(self)
        }
    }

    impl CaseDimension for PayloadProvenance {
        const FIRST: Self = FIRST_PAYLOAD_PROVENANCE;
        const COUNT: usize = PAYLOAD_PROVENANCE_VARIANTS;
        fn succ(self) -> Option<Self> {
            succ_payload_provenance(self)
        }
    }

    /// One field of [`ExtensionDescriptor`], as a value, in declaration order.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    enum DescriptorField {
        Name,
        Merge,
        Checkpoint,
        Provenance,
    }

    const DESCRIPTOR_FIELD_COUNT: usize = 4;

    impl CaseDimension for DescriptorField {
        const FIRST: Self = DescriptorField::Name;
        const COUNT: usize = DESCRIPTOR_FIELD_COUNT;
        fn succ(self) -> Option<Self> {
            match self {
                DescriptorField::Name => Some(DescriptorField::Merge),
                DescriptorField::Merge => Some(DescriptorField::Checkpoint),
                DescriptorField::Checkpoint => Some(DescriptorField::Provenance),
                DescriptorField::Provenance => None,
            }
        }
    }

    /// Which branch or branches carry a descriptor difference.
    ///
    /// The criteria say "on either/both branches", so this dimension is the "either/both"
    /// — three assignments, not two, because a difference on *both* branches is a
    /// distinct diagnostic (it must report both) and not the union of the one-sided ones.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum DifferingBranches {
        OursOnly,
        TheirsOnly,
        Both,
    }

    impl CaseDimension for DifferingBranches {
        const FIRST: Self = DifferingBranches::OursOnly;
        const COUNT: usize = 3;
        fn succ(self) -> Option<Self> {
            match self {
                DifferingBranches::OursOnly => Some(DifferingBranches::TheirsOnly),
                DifferingBranches::TheirsOnly => Some(DifferingBranches::Both),
                DifferingBranches::Both => None,
            }
        }
    }

    /// A merge branch, in the **stable ours-then-theirs order** the criteria require
    /// diagnostics to use.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    enum MergeBranch {
        Ours,
        Theirs,
    }

    impl CaseDimension for MergeBranch {
        const FIRST: Self = MergeBranch::Ours;
        const COUNT: usize = 2;
        fn succ(self) -> Option<Self> {
            match self {
                MergeBranch::Ours => Some(MergeBranch::Theirs),
                MergeBranch::Theirs => None,
            }
        }
    }

    /// Binds [`DescriptorField`]'s cardinality to the struct it claims to enumerate.
    ///
    /// This is the join that would otherwise rot. `DescriptorField` is a *transcription*
    /// of `ExtensionDescriptor`'s fields, and nothing about an exhaustive `match
    /// DescriptorField` notices a **fifth struct field** — the field would simply never
    /// be perturbed, never be compared, and the difference table would keep passing while
    /// covering three quarters of the descriptor.
    ///
    /// The total destructuring below has no `..`, so adding a field to
    /// `ExtensionDescriptor` stops compiling **here**, at a site whose whole purpose is to
    /// say the tables must grow with it. Nothing is computed from the bindings on purpose:
    /// the pattern *is* the assertion.
    fn descriptor_fields_of(
        descriptor: &ExtensionDescriptor,
    ) -> [DescriptorField; DESCRIPTOR_FIELD_COUNT] {
        let ExtensionDescriptor {
            name: _,
            merge: _,
            checkpoint: _,
            provenance: _,
        } = descriptor;
        [
            DescriptorField::Name,
            DescriptorField::Merge,
            DescriptorField::Checkpoint,
            DescriptorField::Provenance,
        ]
    }

    /// Does `left` differ from `right` in exactly this field?
    fn field_differs(
        field: DescriptorField,
        left: &ExtensionDescriptor,
        right: &ExtensionDescriptor,
    ) -> bool {
        match field {
            DescriptorField::Name => left.name != right.name,
            DescriptorField::Merge => left.merge != right.merge,
            DescriptorField::Checkpoint => left.checkpoint != right.checkpoint,
            DescriptorField::Provenance => left.provenance != right.provenance,
        }
    }

    /// The fields in which two descriptors differ, in canonical field order.
    fn differing_fields(
        left: &ExtensionDescriptor,
        right: &ExtensionDescriptor,
    ) -> Vec<DescriptorField> {
        descriptor_fields_of(left)
            .into_iter()
            .filter(|field| field_differs(*field, left, right))
            .collect()
    }

    /// A descriptor differing from `descriptor` in exactly `field`.
    ///
    /// `salt` distinguishes the two branches so that a *both-branches* case has genuinely
    /// different descriptors on each side wherever the dimension is wide enough to allow
    /// it. `Checkpoint` and `Provenance` have two variants, so both salts land on the same
    /// value there; that is fine and deliberately not worked around, because the expected
    /// diagnostic is recomputed from the actual descriptors rather than assumed.
    ///
    /// The replacement is chosen by [`CaseDimension::other`] rather than by naming a
    /// second variant, so adding a variant does not silently leave this reaching for a
    /// stale one.
    fn perturb_field(
        descriptor: &ExtensionDescriptor,
        field: DescriptorField,
        salt: usize,
    ) -> ExtensionDescriptor {
        let mut perturbed = descriptor.clone();
        match field {
            DescriptorField::Name => {
                perturbed.name = Name::str(
                    Name::anonymous(),
                    if salt.is_multiple_of(2) {
                        "perturbedExtA"
                    } else {
                        "perturbedExtB"
                    },
                );
            }
            DescriptorField::Merge => perturbed.merge = descriptor.merge.other(salt),
            DescriptorField::Checkpoint => {
                perturbed.checkpoint = descriptor.checkpoint.other(salt);
            }
            DescriptorField::Provenance => {
                perturbed.provenance = descriptor.provenance.other(salt);
            }
        }
        perturbed
    }

    /// Apply a whole set of field perturbations at once — the "simultaneous differences"
    /// half of the clause.
    fn perturb_fields(
        descriptor: &ExtensionDescriptor,
        fields: &[DescriptorField],
        salt: usize,
    ) -> ExtensionDescriptor {
        let mut perturbed = descriptor.clone();
        for field in fields {
            perturbed = perturb_field(&perturbed, *field, salt);
        }
        perturbed
    }

    fn table_descriptor(case: DescriptorIdentityCase) -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: Name::str(Name::anonymous(), "tableExt"),
            merge: case.merge,
            checkpoint: case.checkpoint,
            provenance: case.provenance,
        }
    }

    /// Every closed dimension's chain agrees with its declared count.
    ///
    /// [`CaseDimension::all`] is where both directions are checked, so a dimension whose
    /// `all()` is never called is a chain nobody walks. This calls every one.
    #[test]
    fn every_case_dimension_chain_matches_its_declared_count() {
        assert_eq!(MergeSemantics::all().len(), MERGE_SEMANTICS_VARIANTS);
        assert_eq!(
            CheckpointSemantics::all().len(),
            CHECKPOINT_SEMANTICS_VARIANTS
        );
        assert_eq!(PayloadProvenance::all().len(), PAYLOAD_PROVENANCE_VARIANTS);
        assert_eq!(DescriptorField::all().len(), DESCRIPTOR_FIELD_COUNT);
        assert_eq!(DifferingBranches::all().len(), 3);
        assert_eq!(MergeBranch::all().len(), 2);
        assert_eq!(
            MergeBranch::all(),
            vec![MergeBranch::Ours, MergeBranch::Theirs],
            "diagnostics are required to report branch facts in stable ours-then-theirs \
             order, so the chain that generates that order is itself pinned"
        );
        assert_eq!(
            DescriptorField::all(),
            descriptor_fields_of(&descriptor(
                MergeSemantics::AppendOrdered,
                PayloadProvenance::Understood
            ))
            .to_vec(),
            "the chain order and the struct-bound order are the same canonical field \
             order, or `canonical branch-then-field order` names two different things"
        );
    }

    /// The perturbation is faithful, and the field comparison is complete.
    ///
    /// Both halves are load-bearing and neither is implied by the other:
    ///
    /// * If `perturb_field` did not actually change its field, every refusal in the
    ///   difference table below would be produced by some *other* difference and the
    ///   table would be measuring nothing. So each perturbation is asserted to change
    ///   **exactly** its own field, over every base descriptor and both salts.
    /// * If `field_differs` compared the wrong field — a copy-paste an exhaustive match
    ///   cannot catch, because the arms are all well-typed — the recovered mismatch list
    ///   would be wrong in the same direction as the expectation. So the field-wise view
    ///   is cross-checked against the struct's own `PartialEq`: two descriptors are equal
    ///   **iff** no field differs, over the full 12 x 12 matrix.
    #[test]
    fn every_descriptor_field_perturbation_changes_exactly_that_field() {
        for case in DESCRIPTOR_IDENTITY_CASES {
            let base = table_descriptor(case);
            for field in DescriptorField::all() {
                for salt in 0..2 {
                    let perturbed = perturb_field(&base, field, salt);
                    assert_eq!(
                        differing_fields(&base, &perturbed),
                        vec![field],
                        "perturbing {field:?} (salt {salt}) must change that field and \
                         nothing else, or the difference table proves nothing"
                    );
                }
            }
            // Simultaneous perturbation of an arbitrary subset changes exactly that subset.
            for mask in 0u32..(1 << DESCRIPTOR_FIELD_COUNT) {
                let subset: Vec<DescriptorField> = DescriptorField::all()
                    .into_iter()
                    .enumerate()
                    .filter_map(|(index, field)| (mask & (1 << index) != 0).then_some(field))
                    .collect();
                assert_eq!(
                    differing_fields(&base, &perturb_fields(&base, &subset, 0)),
                    subset,
                    "a simultaneous perturbation must change exactly its subset"
                );
            }
        }

        for left_case in DESCRIPTOR_IDENTITY_CASES {
            for right_case in DESCRIPTOR_IDENTITY_CASES {
                let left = table_descriptor(left_case);
                let right = table_descriptor(right_case);
                assert_eq!(
                    differing_fields(&left, &right).is_empty(),
                    left == right,
                    "the field-wise view and the struct's own equality must agree, or a \
                     field is compared against the wrong one: {left:?} vs {right:?}"
                );
            }
        }
    }

    /// **The descriptor-difference table**: single and simultaneous differences, on
    /// either and on both branches, under every merge policy.
    ///
    /// # What it discharges
    ///
    /// The clause "unit tables ... cover single and simultaneous descriptor differences
    /// on either/both branches", exhaustively rather than by sample: all 2^4 field
    /// subsets x 3 branch assignments x the full 12-descriptor combination matrix, which
    /// carries "all merge policies" for this table with it. The empty subset is the
    /// control and must **not** refuse at stage 1.
    ///
    /// # And the stage order, which the same fixture proves for free
    ///
    /// Every case here is built so that all three refusal conditions hold at once: the
    /// descriptors differ, *and* neither branch descends from the base, *and* both
    /// branches changed (which `ConflictsRequireReview` would refuse). The bead freezes
    /// the pipeline as admission, then ancestry, then policy — so the reported conflict
    /// must be `DescriptorMismatch` whenever the subset is non-empty, and
    /// `HistoryMismatch` when it is empty. A single fixture family therefore pins both
    /// stage boundaries: reading a `HistoryMismatch` where a mismatch was planted means
    /// stage 1 ran late, and reading a `ConcurrentChanges` means stage 3 ran early.
    ///
    /// # What it does not discharge
    ///
    /// Nothing here is about resource limits, and nothing here is a *generated* model:
    /// the case space is exhaustive over the descriptor, which is a different and
    /// stronger thing than sampling, but the journals are fixed. Prefix classes,
    /// journal sizes and the SetUnion shapes are separate tables.
    #[test]
    fn the_descriptor_difference_table_is_exhaustive_over_fields_and_branches() {
        let shared: Arc<[u8]> = Arc::from(&b"shared-table-payload"[..]);
        let mut refusals = 0usize;
        let mut controls = 0usize;

        for case in DESCRIPTOR_IDENTITY_CASES {
            let base_descriptor = table_descriptor(case);
            for mask in 0u32..(1 << DESCRIPTOR_FIELD_COUNT) {
                let subset: Vec<DescriptorField> = DescriptorField::all()
                    .into_iter()
                    .enumerate()
                    .filter_map(|(index, field)| (mask & (1 << index) != 0).then_some(field))
                    .collect();
                for branches in DifferingBranches::all() {
                    let ours_descriptor = match branches {
                        DifferingBranches::OursOnly | DifferingBranches::Both => {
                            perturb_fields(&base_descriptor, &subset, 0)
                        }
                        DifferingBranches::TheirsOnly => base_descriptor.clone(),
                    };
                    let theirs_descriptor = match branches {
                        DifferingBranches::TheirsOnly | DifferingBranches::Both => {
                            perturb_fields(&base_descriptor, &subset, 1)
                        }
                        DifferingBranches::OursOnly => base_descriptor.clone(),
                    };

                    // Base [shared, b]; ours [x] diverges at 0 and is shorter; theirs
                    // [shared, y, z] diverges at 1 and is longer. So ancestry is invalid on
                    // BOTH branches and both branch lengths differ from the base's, which
                    // is `ConflictsRequireReview`'s concurrent-change condition.
                    let base = ExtensionState::new(base_descriptor.clone())
                        .push_entry(Arc::clone(&shared))
                        .push_entry(bytes(b"b"));
                    let ours = ExtensionState::new(ours_descriptor.clone()).push_entry(bytes(b"x"));
                    let theirs = ExtensionState::new(theirs_descriptor.clone())
                        .push_entry(Arc::clone(&shared))
                        .push_entry(bytes(b"y"))
                        .push_entry(bytes(b"z"));

                    let sharing_before = Arc::strong_count(&shared);
                    let roots_before = (
                        base.content_digest(),
                        ours.content_digest(),
                        theirs.content_digest(),
                    );
                    let inputs_before = (base.clone(), ours.clone(), theirs.clone());

                    let label = format!("{case:?} subset={subset:?} branches={branches:?}");
                    let outcome =
                        ExtensionState::merge(&base, &ours, &theirs, TEST_SET_UNION_LIMITS);

                    if subset.is_empty() {
                        // The control. Descriptors agree, so stage 1 must let this through
                        // and stage 2 must be the one that refuses.
                        controls += 1;
                        assert_eq!(
                            outcome.as_ref().expect_err(&label),
                            &MergeConflict::HistoryMismatch {
                                extension: base_descriptor.name.clone(),
                                base_len: 2,
                                ours_len: 1,
                                theirs_len: 3,
                                ours_common_prefix: 0,
                                theirs_common_prefix: 1,
                            },
                            "{label}: with agreeing descriptors the ancestry stage is the \
                             authority, and a ConcurrentChanges here would mean policy \
                             dispatch overtook it"
                        );
                    } else {
                        refusals += 1;
                        let conflict = outcome.as_ref().expect_err(&label);
                        assert_eq!(
                            conflict,
                            &MergeConflict::DescriptorMismatch {
                                base: base_descriptor.clone(),
                                ours: ours_descriptor.clone(),
                                theirs: theirs_descriptor.clone(),
                            },
                            "{label}: stage 1 refuses first and reports all three complete \
                             descriptors"
                        );

                        // Every simultaneous mismatch is recoverable from the diagnostic,
                        // in canonical branch-then-field order, checked in both directions.
                        // The conflict carries the three *complete* descriptors, so a
                        // partial mismatch report is not expressible — but a wrong one is,
                        // and that is what this compares.
                        let MergeConflict::DescriptorMismatch {
                            base: reported_base,
                            ours: reported_ours,
                            theirs: reported_theirs,
                        } = conflict
                        else {
                            unreachable!("asserted equal to a DescriptorMismatch just above")
                        };
                        let mut reported: Vec<(MergeBranch, DescriptorField)> = Vec::new();
                        for branch in MergeBranch::all() {
                            let side = match branch {
                                MergeBranch::Ours => reported_ours,
                                MergeBranch::Theirs => reported_theirs,
                            };
                            for field in differing_fields(reported_base, side) {
                                reported.push((branch, field));
                            }
                        }
                        let mut expected: Vec<(MergeBranch, DescriptorField)> = Vec::new();
                        for branch in MergeBranch::all() {
                            let differs = !matches!(
                                (branch, branches),
                                (MergeBranch::Ours, DifferingBranches::TheirsOnly)
                                    | (MergeBranch::Theirs, DifferingBranches::OursOnly)
                            );
                            if differs {
                                for field in subset.iter().copied() {
                                    expected.push((branch, field));
                                }
                            }
                        }
                        assert_eq!(
                            reported, expected,
                            "{label}: the diagnostic must expose every simultaneous \
                             mismatch, and only those, in ours-then-theirs then canonical \
                             field order"
                        );

                        // Repeated refusal: same inputs, same answer, no drift.
                        for repeat in 0..2 {
                            assert_eq!(
                                ExtensionState::merge(&base, &ours, &theirs, TEST_SET_UNION_LIMITS)
                                    .as_ref()
                                    .expect_err(&label),
                                conflict,
                                "{label}: repeat {repeat} must reproduce the refusal exactly"
                            );
                        }
                    }

                    assert_eq!(
                        Arc::strong_count(&shared),
                        sharing_before,
                        "{label}: a refusal that cloned a payload handle would move the \
                         strong count"
                    );
                    assert_eq!(
                        (
                            base.content_digest(),
                            ours.content_digest(),
                            theirs.content_digest(),
                        ),
                        roots_before,
                        "{label}: a refusal must expose no root movement"
                    );
                    assert_eq!(
                        (base, ours, theirs),
                        inputs_before,
                        "{label}: a refusal must leave every input unchanged"
                    );
                }
            }
        }

        let expected_cases = DESCRIPTOR_IDENTITY_CASES.len()
            * (1 << DESCRIPTOR_FIELD_COUNT)
            * DifferingBranches::COUNT;
        assert_eq!(
            refusals + controls,
            expected_cases,
            "the sweep must be exhaustive over descriptor x subset x branch assignment"
        );
        assert_eq!(
            controls,
            DESCRIPTOR_IDENTITY_CASES.len() * DifferingBranches::COUNT,
            "exactly the empty subset is the control, on every branch assignment"
        );
        eprintln!(
            "{{\"schema\":\"fln.unit.extension-merge-validation-table\",\"version\":1,\
             \"bead\":\"fln-extension-merge-validation-proof-debt-dt5\",\
             \"claim_type\":\"bounded_model\",\"table\":\"descriptor_difference\",\
             \"descriptor_combinations\":{},\"field_subsets\":{},\"branch_assignments\":{},\
             \"cases\":{expected_cases},\"stage_one_refusals\":{refusals},\
             \"stage_two_controls\":{controls},\"status\":\"pass\"}}",
            DESCRIPTOR_IDENTITY_CASES.len(),
            1 << DESCRIPTOR_FIELD_COUNT,
            DifferingBranches::COUNT,
        );
    }

    /// Restoration and recovery for the descriptor stage.
    ///
    /// The clause names "repeated refusal, restoration, and recovery" together. Repeated
    /// refusal is asserted inside the table above, where every case runs three times.
    /// This is the other two: after a refusal, repairing the descriptor and then the
    /// history restores the merge, and the product is exactly what the policy declares —
    /// so a refusal is a stop, not a state change that has to be undone.
    ///
    /// Run under **every** merge policy, because the policies produce different products
    /// and a recovery test on one of them would say nothing about the others.
    #[test]
    fn a_descriptor_refusal_is_recoverable_under_every_merge_policy() {
        for policy in MergeSemantics::all() {
            let agreed = ExtensionDescriptor {
                merge: policy,
                ..descriptor(policy, PayloadProvenance::Understood)
            };
            let mismatched = perturb_field(&agreed, DescriptorField::Provenance, 0);

            let base = ExtensionState::new(agreed.clone()).push_entry(bytes(b"base"));
            let bad_descriptor = ExtensionState::new(mismatched).push_entry(bytes(b"ours"));
            let bad_history = ExtensionState::new(agreed.clone()).push_entry(bytes(b"other"));
            let good_ours = base.push_entry(bytes(b"ours"));
            let unchanged_theirs = base.clone();

            assert!(
                matches!(
                    ExtensionState::merge(
                        &base,
                        &bad_descriptor,
                        &unchanged_theirs,
                        TEST_SET_UNION_LIMITS
                    ),
                    Err(MergeConflict::DescriptorMismatch { .. })
                ),
                "{policy:?}: the descriptor stage refuses first"
            );
            assert!(
                matches!(
                    ExtensionState::merge(
                        &base,
                        &bad_history,
                        &unchanged_theirs,
                        TEST_SET_UNION_LIMITS
                    ),
                    Err(MergeConflict::HistoryMismatch { .. })
                ),
                "{policy:?}: repairing only the descriptor leaves the ancestry stage to \
                 refuse — a recovery that skipped a stage would pass here"
            );

            // Both repaired: the merge completes and the product is the declared one.
            let recovery = merge_with_test_limits(&base, &good_ours, &unchanged_theirs);
            assert!(
                recovery.is_ok(),
                "{policy:?}: recovery must complete: {recovery:?}"
            );
            let recovered = recovery.expect("asserted Ok immediately above");
            assert_eq!(
                raw_payloads(&recovered),
                raw_payloads(&good_ours),
                "{policy:?}: a one-sided change merges to that branch under every declared \
                 policy"
            );
            assert_eq!(
                base.len(),
                1,
                "{policy:?}: none of the refused attempts may have touched the base"
            );
        }
    }
}
