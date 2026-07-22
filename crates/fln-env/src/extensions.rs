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

use std::sync::Arc;

use fln_core::name::Name;

/// Declared merge semantics for one extension — the contract branch/merge consults.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeSemantics {
    /// Entries concatenate in branch order (the common upstream replay shape).
    AppendOrdered,
    /// Entries form a set keyed by their bytes; duplicates collapse.
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

#[derive(Debug)]
enum JournalNode {
    Branch { children: Vec<Arc<JournalNode>> },
    Leaf { entries: Vec<ExtensionEntry> },
}

#[derive(Debug, Clone, Default)]
struct ExtensionJournal {
    root: Option<Arc<JournalNode>>,
    len: usize,
    depth: u32,
}

impl ExtensionJournal {
    fn push(&self, entry: ExtensionEntry) -> ExtensionJournal {
        let (root, depth) = match &self.root {
            None => (new_journal_path(0, entry), 0),
            Some(root) if self.len == journal_capacity(self.depth) => (
                Arc::new(JournalNode::Branch {
                    children: vec![Arc::clone(root), new_journal_path(self.depth, entry)],
                }),
                self.depth + 1,
            ),
            Some(root) => (
                journal_insert(root, self.depth, self.len, entry),
                self.depth,
            ),
        };
        ExtensionJournal {
            root: Some(root),
            len: self.len + 1,
            depth,
        }
    }

    fn iter(&self) -> JournalIter<'_> {
        let mut stack = Vec::with_capacity(self.depth as usize + 1);
        if let Some(root) = &self.root {
            stack.push((root.as_ref(), 0));
        }
        JournalIter { stack }
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
}

fn journal_capacity(depth: u32) -> usize {
    1usize
        .checked_shl(JOURNAL_BITS * (depth + 1))
        .unwrap_or(usize::MAX)
}

fn new_journal_path(depth: u32, entry: ExtensionEntry) -> Arc<JournalNode> {
    if depth == 0 {
        Arc::new(JournalNode::Leaf {
            entries: vec![entry],
        })
    } else {
        Arc::new(JournalNode::Branch {
            children: vec![new_journal_path(depth - 1, entry)],
        })
    }
}

fn journal_insert(
    node: &Arc<JournalNode>,
    depth: u32,
    index: usize,
    entry: ExtensionEntry,
) -> Arc<JournalNode> {
    match (depth, node.as_ref()) {
        (0, JournalNode::Leaf { entries }) => {
            let mut next = entries.clone();
            next.push(entry);
            Arc::new(JournalNode::Leaf { entries: next })
        }
        (depth, JournalNode::Branch { children }) => {
            let shift = JOURNAL_BITS * depth;
            let slot = (index >> shift) & (JOURNAL_CHUNK_CAPACITY - 1);
            let mut next = children.clone();
            if let Some(child) = next.get_mut(slot) {
                *child = journal_insert(child, depth - 1, index, entry);
            } else {
                next.push(new_journal_path(depth - 1, entry));
            }
            Arc::new(JournalNode::Branch { children: next })
        }
        _ => unreachable!("journal depth and node kind disagree"),
    }
}

impl PartialEq for ExtensionJournal {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other.iter())
    }
}

impl Eq for ExtensionJournal {}

struct JournalIter<'a> {
    stack: Vec<(&'a JournalNode, usize)>,
}

impl<'a> Iterator for JournalIter<'a> {
    type Item = &'a ExtensionEntry;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (node, index) = *self.stack.last()?;
            match node {
                JournalNode::Leaf { entries } => {
                    if let Some(entry) = entries.get(index) {
                        self.stack.last_mut()?.1 += 1;
                        return Some(entry);
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
        self.journal.iter()
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
    ) -> Result<ExtensionState, MergeConflict> {
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
                Ok(merged)
            }
            MergeSemantics::SetUnion => {
                let mut merged = ours.clone();
                for entry in theirs.entries().skip(base.len()) {
                    if !merged.entries().any(|seen| seen == entry) {
                        merged = merged.push_entry(Arc::clone(&entry.payload));
                    }
                }
                Ok(merged)
            }
            MergeSemantics::ConflictsRequireReview => {
                let ours_changed = ours.len() != base.len();
                let theirs_changed = theirs.len() != base.len();
                if ours_changed && theirs_changed {
                    Err(MergeConflict::ConcurrentChanges {
                        extension: base.descriptor.name.clone(),
                    })
                } else if theirs_changed {
                    Ok(theirs.clone())
                } else {
                    Ok(ours.clone())
                }
            }
        }
    }
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
    use std::collections::HashSet;

    fn descriptor(merge: MergeSemantics, provenance: PayloadProvenance) -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: Name::str(Name::anonymous(), "simpExt"),
            merge,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance,
        }
    }

    fn bytes(v: &[u8]) -> Arc<[u8]> {
        Arc::from(v.to_vec().into_boxed_slice())
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
    }

    #[test]
    fn persistent_journal_storage_and_replay_scale_linearly() {
        let state = numbered_state(100_000);
        let node_count = state.journal.node_ptrs().len();
        let leaf_bound = state.len().div_ceil(JOURNAL_CHUNK_CAPACITY);
        assert!(
            node_count <= leaf_bound * 2,
            "{node_count} nodes exceeds linear bound for {leaf_bound} leaves"
        );
        assert_eq!(state.entries().count(), state.len());
        let last = state.entries().last().expect("non-empty replay");
        let encoded: [u8; 8] = last.payload.as_ref().try_into().expect("u64 payload");
        assert_eq!(u64::from_le_bytes(encoded), 99_999);
        println!(
            "persistent journal evidence: entries={} nodes={node_count} leaves_bound={leaf_bound} depth={}",
            state.len(),
            state.journal.depth
        );
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
        let merged = ExtensionState::merge(&base, &ours, &theirs).expect("append-ordered merges");
        let seen: Vec<&[u8]> = merged.entries().map(|e| &*e.payload).collect();
        assert_eq!(seen, vec![b"base".as_slice(), b"ours", b"theirs"]);
    }

    #[test]
    fn set_union_collapses_duplicates() {
        let base = ExtensionState::new(descriptor(
            MergeSemantics::SetUnion,
            PayloadProvenance::Understood,
        ));
        let ours = base.push_entry(bytes(b"x"));
        let theirs = base.push_entry(bytes(b"x")).push_entry(bytes(b"y"));
        let merged = ExtensionState::merge(&base, &ours, &theirs).expect("set union merges");
        assert_eq!(merged.len(), 2, "duplicate `x` collapsed");
    }

    #[test]
    fn review_required_merges_are_typed_conflicts_never_silent() {
        let base = ExtensionState::new(descriptor(
            MergeSemantics::ConflictsRequireReview,
            PayloadProvenance::Understood,
        ));
        let ours = base.push_entry(bytes(b"o"));
        let theirs = base.push_entry(bytes(b"t"));
        let conflict = ExtensionState::merge(&base, &ours, &theirs).expect_err("both changed");
        assert_eq!(
            conflict,
            MergeConflict::ConcurrentChanges {
                extension: Name::str(Name::anonymous(), "simpExt"),
            }
        );
        // One-sided changes pass through unchanged.
        let one_sided =
            ExtensionState::merge(&base, &ours, &base).expect("one-sided change is safe");
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

            let ours_error = ExtensionState::merge(&base, &mismatched, &matching)
                .expect_err("ours contract mismatch is refused");
            assert_eq!(
                ours_error,
                MergeConflict::DescriptorMismatch {
                    base: expected.clone(),
                    ours: variant.clone(),
                    theirs: expected.clone(),
                }
            );

            let theirs_error = ExtensionState::merge(&base, &matching, &mismatched)
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
                ExtensionState::merge(&base, &invalid, &matching)
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
                ExtensionState::merge(&base, &matching, &invalid)
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
            ExtensionState::merge(&base, &invalid_ours, &invalid_theirs)
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
}
