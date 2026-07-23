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

use fln_core::name::Name;
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::domain::{Digest, Domain, hash};

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

fn merge_semantics_tag(semantics: MergeSemantics) -> u8 {
    match semantics {
        MergeSemantics::AppendOrdered => 0,
        MergeSemantics::SetUnion => 1,
        MergeSemantics::ConflictsRequireReview => 2,
    }
}

fn checkpoint_semantics_tag(semantics: CheckpointSemantics) -> u8 {
    match semantics {
        CheckpointSemantics::JournalSuffix => 0,
        CheckpointSemantics::FullJournal => 1,
    }
}

fn payload_provenance_tag(provenance: PayloadProvenance) -> u8 {
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
    pub fn checkpoint(
        &self,
        base: Option<&ExtensionState>,
        limits: CheckpointLimits,
    ) -> Result<ExtensionCheckpoint, CheckpointError> {
        self.checkpoint_with_work(base, limits)
            .map(|(checkpoint, work)| {
                debug_assert_eq!(work.captured_entries, checkpoint.captured_entries);
                debug_assert!(work.prefix_lookup_steps <= self.journal.depth as usize + 1);
                checkpoint
            })
    }

    fn checkpoint_with_work(
        &self,
        base: Option<&ExtensionState>,
        limits: CheckpointLimits,
    ) -> Result<(ExtensionCheckpoint, CheckpointWork), CheckpointError> {
        match self.descriptor.checkpoint {
            CheckpointSemantics::JournalSuffix => {
                let base = base.ok_or_else(|| CheckpointError::MissingBase {
                    extension: self.descriptor.name.clone(),
                })?;
                validate_checkpoint_descriptor(&self.descriptor, &base.descriptor)?;
                let Some((prefix_digest, prefix_payload_bytes, lookup_steps)) =
                    self.journal.prefix_facts(base.len())
                else {
                    return Err(history_mismatch(base, self));
                };
                if prefix_digest != base.journal.digest
                    || prefix_payload_bytes != base.journal.payload_bytes
                {
                    return Err(history_mismatch(base, self));
                }

                let captured_entries = self.len() - base.len();
                let captured_payload_bytes =
                    self.journal.payload_bytes - base.journal.payload_bytes;
                enforce_checkpoint_limits(
                    &self.descriptor.name,
                    captured_entries,
                    captured_payload_bytes,
                    limits,
                )?;

                let journal = ExtensionJournal::from_entries(
                    self.journal
                        .records_from(base.len())
                        .map(|record| record.entry.clone()),
                );
                let checkpoint = ExtensionCheckpoint {
                    schema_version: EXTENSION_CHECKPOINT_SCHEMA_VERSION,
                    descriptor: self.descriptor.clone(),
                    captured_entries,
                    captured_payload_bytes,
                    payload: CheckpointPayload::JournalSuffix {
                        base_len: base.len(),
                        base_history_digest: base.journal.digest,
                        base_state_digest: base.content_digest(),
                        journal,
                    },
                };
                Ok((
                    checkpoint,
                    CheckpointWork {
                        prefix_lookup_steps: lookup_steps,
                        captured_entries,
                    },
                ))
            }
            CheckpointSemantics::FullJournal => {
                if base.is_some() {
                    return Err(CheckpointError::UnexpectedBase {
                        extension: self.descriptor.name.clone(),
                    });
                }
                enforce_checkpoint_limits(
                    &self.descriptor.name,
                    self.len(),
                    self.journal.payload_bytes,
                    limits,
                )?;
                let journal = ExtensionJournal::from_entries(
                    self.journal.records().map(|record| record.entry.clone()),
                );
                let checkpoint = ExtensionCheckpoint {
                    schema_version: EXTENSION_CHECKPOINT_SCHEMA_VERSION,
                    descriptor: self.descriptor.clone(),
                    captured_entries: self.len(),
                    captured_payload_bytes: self.journal.payload_bytes,
                    payload: CheckpointPayload::FullJournal { journal },
                };
                Ok((
                    checkpoint,
                    CheckpointWork {
                        prefix_lookup_steps: 0,
                        captured_entries: self.len(),
                    },
                ))
            }
        }
    }

    /// Restore a checkpoint atomically. Inputs are immutable and every validation
    /// completes before the returned snapshot can become observable.
    pub fn restore(
        base: Option<&ExtensionState>,
        checkpoint: &ExtensionCheckpoint,
        limits: CheckpointLimits,
    ) -> Result<ExtensionState, CheckpointError> {
        if checkpoint.schema_version != EXTENSION_CHECKPOINT_SCHEMA_VERSION {
            return Err(CheckpointError::UnsupportedVersion {
                found: checkpoint.schema_version,
                supported: EXTENSION_CHECKPOINT_SCHEMA_VERSION,
            });
        }
        let payload_mode = checkpoint.mode();
        if checkpoint.descriptor.checkpoint != payload_mode {
            return Err(CheckpointError::ModeMismatch {
                descriptor_mode: checkpoint.descriptor.checkpoint,
                payload_mode,
            });
        }
        let journal = checkpoint.journal();
        journal
            .integrity()
            .map_err(|reason| CheckpointError::MalformedCheckpoint {
                extension: checkpoint.descriptor.name.clone(),
                reason,
            })?;
        if journal.len != checkpoint.captured_entries
            || journal.payload_bytes != checkpoint.captured_payload_bytes
        {
            return Err(CheckpointError::MalformedCheckpoint {
                extension: checkpoint.descriptor.name.clone(),
                reason: "declared checkpoint measurements do not match its journal",
            });
        }
        enforce_checkpoint_limits(
            &checkpoint.descriptor.name,
            journal.len,
            journal.payload_bytes,
            limits,
        )?;

        match &checkpoint.payload {
            CheckpointPayload::JournalSuffix {
                base_len,
                base_history_digest,
                base_state_digest,
                journal,
            } => {
                let base = base.ok_or_else(|| CheckpointError::MissingBase {
                    extension: checkpoint.descriptor.name.clone(),
                })?;
                validate_checkpoint_descriptor(&checkpoint.descriptor, &base.descriptor)?;
                if base.len() != *base_len {
                    return Err(CheckpointError::BaseLengthMismatch {
                        extension: checkpoint.descriptor.name.clone(),
                        expected: *base_len,
                        actual: base.len(),
                    });
                }
                if base.journal.digest != *base_history_digest {
                    return Err(CheckpointError::BaseHistoryMismatch {
                        extension: checkpoint.descriptor.name.clone(),
                        expected: *base_history_digest,
                        actual: base.journal.digest,
                    });
                }
                let actual_state_digest = base.content_digest();
                if actual_state_digest != *base_state_digest {
                    return Err(CheckpointError::BaseDigestMismatch {
                        extension: checkpoint.descriptor.name.clone(),
                        expected: *base_state_digest,
                        actual: actual_state_digest,
                    });
                }
                let mut restored = base.clone();
                for record in journal.records() {
                    restored = restored.push_entry(Arc::clone(&record.entry.payload));
                }
                Ok(restored)
            }
            CheckpointPayload::FullJournal { journal } => {
                if base.is_some() {
                    return Err(CheckpointError::UnexpectedBase {
                        extension: checkpoint.descriptor.name.clone(),
                    });
                }
                Ok(ExtensionState {
                    descriptor: checkpoint.descriptor.clone(),
                    journal: journal.clone(),
                })
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
        if base.descriptor != ours.descriptor || base.descriptor != theirs.descriptor {
            return Err(MergeConflict::DescriptorMismatch {
                base: base.descriptor.clone(),
                ours: ours.descriptor.clone(),
                theirs: theirs.descriptor.clone(),
            });
        }
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
    use std::collections::HashSet;
    use std::time::Instant;

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

    fn descriptor_identity_cases() -> Vec<DescriptorIdentityCase> {
        let mut cases = Vec::with_capacity(12);
        for merge in [
            MergeSemantics::AppendOrdered,
            MergeSemantics::SetUnion,
            MergeSemantics::ConflictsRequireReview,
        ] {
            for checkpoint in [
                CheckpointSemantics::JournalSuffix,
                CheckpointSemantics::FullJournal,
            ] {
                for provenance in [PayloadProvenance::Understood, PayloadProvenance::Opaque] {
                    cases.push(DescriptorIdentityCase {
                        merge,
                        checkpoint,
                        provenance,
                    });
                }
            }
        }
        cases
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
                .checkpoint_with_work(Some(&suffix_base), TEST_LIMITS)
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
            .checkpoint_with_work(None, TEST_LIMITS)
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
        let checkpoint = target
            .checkpoint_extension(&extension_name, Some(&base), limits)
            .expect("capture through the real environment registry");
        let (instrumented_checkpoint, suffix_work) = target_state
            .checkpoint_with_work(Some(base_state), limits)
            .expect("measure the same real suffix capture");
        assert_eq!(checkpoint, instrumented_checkpoint);
        let restored = base
            .apply_extension_checkpoint(&checkpoint, limits)
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
        let full_checkpoint = full_target
            .checkpoint_extension(&full_name, None, limits)
            .expect("capture real full journal");
        let (_, full_work) = full_target
            .extension(&full_name)
            .expect("full target extension exists")
            .checkpoint_with_work(None, limits)
            .expect("measure the same real full capture");
        let full_restored = full_base
            .apply_extension_checkpoint(&full_checkpoint, limits)
            .expect("apply real full journal");
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
        let refusal = divergent
            .apply_extension_checkpoint(&checkpoint, limits)
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
        let recovered = base
            .apply_extension_checkpoint(&checkpoint, limits)
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
}
