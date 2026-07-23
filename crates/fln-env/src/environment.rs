//! The Grimoire environment (plan §7.1): semantically the Reference's name→constant
//! map plus contract-registered extensions; mechanically ours — persistent maps with
//! structural sharing, so a snapshot is an O(1) clone and mutation after a fork is
//! invisible to the fork (the primitive under Athanor's speculative parallelism,
//! Lantern's per-request views, and Envoy's search trees).
//!
//! Every commit exposes two roots: the **logical root** (declarations + extension
//! deltas + options; the cache key the Ledger, receipts, and Envoy speak) and a
//! separate **operational-metadata root** — two hosts producing the same trusted
//! environment share a logical root even when their operational manifests differ.

use std::sync::Arc;

use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::root::{LogicalRoot, LogicalRootBuilder};

use crate::constants::{ConstantInfo, DefinitionSafety, QuotKind, ReducibilityHints};
use crate::extensions::{
    CheckpointError, CheckpointLimits, CheckpointSemantics, ExtensionCheckpoint,
    ExtensionDescriptor, ExtensionState,
};
#[cfg(test)]
use crate::extensions::{MergeSemantics, PayloadProvenance};
use crate::pmap::{PKey, PMap};

/// Stable `Domain::DeclContent` tags. These are schema values, not Rust enum
/// discriminants: changing them requires an explicit identity/epoch decision.
fn definition_safety_tag(safety: DefinitionSafety) -> u8 {
    match safety {
        DefinitionSafety::Unsafe => 0,
        DefinitionSafety::Safe => 1,
        DefinitionSafety::Partial => 2,
    }
}

fn quot_kind_tag(kind: QuotKind) -> u8 {
    match kind {
        QuotKind::Type => 0,
        QuotKind::Ctor => 1,
        QuotKind::Lift => 2,
        QuotKind::Ind => 3,
    }
}

impl PKey for Name {
    fn key_hash(&self) -> u64 {
        // The stored Reference-observable hash; collisions are handled by the trie's
        // buckets, equality stays structural.
        self.hash()
    }
}

/// Typed refusals — an environment mutation never panics and never silently drops.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvError {
    /// The kernel's already-declared law: one name, one constant.
    DuplicateDeclaration {
        name: Name,
    },
    DuplicateExtension {
        name: Name,
    },
    UnknownExtension {
        name: Name,
    },
    Checkpoint(CheckpointError),
}

impl std::fmt::Display for EnvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvError::DuplicateDeclaration { name } => {
                write!(
                    f,
                    "constant `{}` is already declared",
                    name.to_display_string()
                )
            }
            EnvError::DuplicateExtension { name } => {
                write!(
                    f,
                    "extension `{}` is already registered",
                    name.to_display_string()
                )
            }
            EnvError::UnknownExtension { name } => {
                write!(
                    f,
                    "extension `{}` is not registered",
                    name.to_display_string()
                )
            }
            EnvError::Checkpoint(error) => error.fmt(f),
        }
    }
}

/// The environment. `Clone` IS `snapshot`: O(1), fully isolated.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Environment {
    constants: PMap<Name, Arc<ConstantInfo>>,
    extensions: PMap<Name, Arc<ExtensionState>>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment::default()
    }

    pub fn len(&self) -> usize {
        self.constants.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }

    /// `Environment.find`.
    pub fn find(&self, name: &Name) -> Option<&ConstantInfo> {
        self.constants.get(name).map(Arc::as_ref)
    }

    pub fn contains(&self, name: &Name) -> bool {
        self.constants.contains_key(name)
    }

    /// Add a constant. One name, one constant — a duplicate is a typed refusal
    /// (the kernel's admission law; nothing here can overwrite a declaration).
    pub fn add_decl(&self, info: ConstantInfo) -> Result<Environment, EnvError> {
        let name = info.name().clone();
        if self.constants.contains_key(&name) {
            return Err(EnvError::DuplicateDeclaration { name });
        }
        Ok(Environment {
            constants: self.constants.insert(name, Arc::new(info)),
            extensions: self.extensions.clone(),
        })
    }

    /// Register an extension with its declared contracts.
    pub fn register_extension(
        &self,
        descriptor: ExtensionDescriptor,
    ) -> Result<Environment, EnvError> {
        let name = descriptor.name.clone();
        if self.extensions.contains_key(&name) {
            return Err(EnvError::DuplicateExtension { name });
        }
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self
                .extensions
                .insert(name, Arc::new(ExtensionState::new(descriptor))),
        })
    }

    /// Append one replay entry to a registered extension.
    pub fn push_extension_entry(
        &self,
        extension: &Name,
        payload: impl Into<Arc<[u8]>>,
    ) -> Result<Environment, EnvError> {
        let Some(state) = self.extensions.get(extension) else {
            return Err(EnvError::UnknownExtension {
                name: extension.clone(),
            });
        };
        let next = state.push_entry(payload);
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self.extensions.insert(extension.clone(), Arc::new(next)),
        })
    }

    pub fn extension(&self, name: &Name) -> Option<&ExtensionState> {
        self.extensions.get(name).map(Arc::as_ref)
    }

    /// Capture one registered extension under its declared checkpoint contract.
    /// A suffix base is another immutable environment snapshot; full-journal mode
    /// requires `None` and carries no ambient extension history.
    pub fn checkpoint_extension(
        &self,
        extension: &Name,
        base: Option<&Environment>,
        limits: CheckpointLimits,
    ) -> Result<ExtensionCheckpoint, EnvError> {
        let state = self
            .extension(extension)
            .ok_or_else(|| EnvError::UnknownExtension {
                name: extension.clone(),
            })?;
        let base_state = match base {
            Some(base) => {
                Some(
                    base.extension(extension)
                        .ok_or_else(|| EnvError::UnknownExtension {
                            name: extension.clone(),
                        })?,
                )
            }
            None => None,
        };
        state
            .checkpoint(base_state, limits)
            .map_err(EnvError::Checkpoint)
    }

    /// Apply a checkpoint to the matching registry slot and return a new isolated
    /// environment snapshot. Declarations and unrelated extensions remain shared.
    pub fn apply_extension_checkpoint(
        &self,
        checkpoint: &ExtensionCheckpoint,
        limits: CheckpointLimits,
    ) -> Result<Environment, EnvError> {
        let name = &checkpoint.descriptor().name;
        let registered = self
            .extension(name)
            .ok_or_else(|| EnvError::UnknownExtension { name: name.clone() })?;
        if checkpoint.mode() == CheckpointSemantics::FullJournal
            && registered.descriptor != *checkpoint.descriptor()
        {
            let error = if registered.descriptor.name != checkpoint.descriptor().name {
                CheckpointError::ExtensionNameMismatch {
                    expected: checkpoint.descriptor().name.clone(),
                    actual: registered.descriptor.name.clone(),
                }
            } else {
                CheckpointError::ContractMismatch {
                    expected: checkpoint.descriptor().clone(),
                    actual: registered.descriptor.clone(),
                }
            };
            return Err(EnvError::Checkpoint(error));
        }
        let base = match checkpoint.mode() {
            CheckpointSemantics::JournalSuffix => Some(registered),
            CheckpointSemantics::FullJournal => None,
        };
        let restored =
            ExtensionState::restore(base, checkpoint, limits).map_err(EnvError::Checkpoint)?;
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self.extensions.insert(name.clone(), Arc::new(restored)),
        })
    }

    /// The canonical content digest of one constant (Domain::DeclContent): the
    /// deterministic projection the logical root aggregates. Byte-level olean parity
    /// is the codec's business; this digest is FrankenLean's own identity.
    pub fn decl_content_digest(info: &ConstantInfo) -> Digest {
        let mut w = CanonWriter::new();
        w.str(info.kind_name());
        info.name().write_body(&mut w);
        let base = info.constant_val();
        w.u64(base.level_params.len() as u64);
        for p in &base.level_params {
            p.write_body(&mut w);
        }
        base.type_.write_body(&mut w);
        match info {
            ConstantInfo::Axiom(v) => w.bool(v.is_unsafe),
            ConstantInfo::Defn(v) => {
                v.value.write_body(&mut w);
                match v.hints {
                    ReducibilityHints::Opaque => w.u8(0),
                    ReducibilityHints::Abbrev => w.u8(1),
                    ReducibilityHints::Regular(h) => {
                        w.u8(2);
                        w.u32(h);
                    }
                }
                w.u8(definition_safety_tag(v.safety));
                w.u64(v.all.len() as u64);
                for n in &v.all {
                    n.write_body(&mut w);
                }
            }
            ConstantInfo::Thm(v) => {
                v.value.write_body(&mut w);
                w.u64(v.all.len() as u64);
                for n in &v.all {
                    n.write_body(&mut w);
                }
            }
            ConstantInfo::Opaque(v) => {
                v.value.write_body(&mut w);
                w.bool(v.is_unsafe);
                w.u64(v.all.len() as u64);
                for n in &v.all {
                    n.write_body(&mut w);
                }
            }
            ConstantInfo::Quot(v) => w.u8(quot_kind_tag(v.kind)),
            ConstantInfo::Induct(v) => {
                w.u32(v.num_params);
                w.u32(v.num_indices);
                w.u32(v.num_nested);
                w.bool(v.is_rec);
                w.bool(v.is_unsafe);
                w.bool(v.is_reflexive);
                w.u64(v.ctors.len() as u64);
                for n in &v.ctors {
                    n.write_body(&mut w);
                }
                // The mutual-inductive block is part of the declaration's content
                // (as it is for `Defn`/`Thm`): two inductives identical except for
                // their block grouping are distinct declarations and must not share
                // a content digest.
                w.u64(v.all.len() as u64);
                for n in &v.all {
                    n.write_body(&mut w);
                }
            }
            ConstantInfo::Ctor(v) => {
                v.induct.write_body(&mut w);
                w.u32(v.cidx);
                w.u32(v.num_params);
                w.u32(v.num_fields);
                w.bool(v.is_unsafe);
            }
            ConstantInfo::Rec(v) => {
                w.u32(v.num_params);
                w.u32(v.num_indices);
                w.u32(v.num_motives);
                w.u32(v.num_minors);
                w.bool(v.k);
                w.bool(v.is_unsafe);
                w.u64(v.rules.len() as u64);
                for rule in &v.rules {
                    rule.ctor.write_body(&mut w);
                    w.u32(rule.nfields);
                    rule.rhs.write_body(&mut w);
                }
                // The mutual block is content here too (mirrors `Defn`/`Thm`).
                w.u64(v.all.len() as u64);
                for n in &v.all {
                    n.write_body(&mut w);
                }
            }
        }
        hash(Domain::DeclContent, &w.into_bytes())
    }

    /// The logical root of this commit: declarations + extension deltas + options —
    /// and nothing else (wall-clock, paths, and schedule have no way in).
    pub fn logical_root(&self, options: &KVMap) -> LogicalRoot {
        let mut builder = LogicalRootBuilder::new();
        for (name, info) in self.constants.iter() {
            builder.add_decl(name, Environment::decl_content_digest(info));
        }
        for (name, state) in self.extensions.iter() {
            builder.add_extension_delta(name, state.content_digest());
        }
        builder.set_options(options);
        builder.finalize()
    }

    /// The operational-metadata root: host facts, paths, timings — everything the
    /// logical root deliberately excludes, digested separately so receipts can carry
    /// both without ever mixing them.
    pub fn operational_root(metadata: &KVMap) -> Digest {
        hash(Domain::OperationalMeta, &metadata.to_canonical_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{AxiomVal, ConstantVal};
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_core::options::DataValue;

    fn n(s: &str) -> Name {
        Name::str(Name::anonymous(), s)
    }

    fn axiom(name: &str) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(name),
                level_params: vec![],
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        })
    }

    fn descriptor(name: &str) -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: n(name),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Understood,
        }
    }

    #[test]
    fn add_find_and_the_one_name_one_constant_law() {
        let env = Environment::new().add_decl(axiom("a")).expect("adds");
        assert_eq!(env.len(), 1);
        assert_eq!(env.find(&n("a")).expect("found").kind_name(), "axiom");
        assert!(env.find(&n("b")).is_none());
        let dup = env.add_decl(axiom("a")).expect_err("duplicate refused");
        assert_eq!(dup, EnvError::DuplicateDeclaration { name: n("a") });
    }

    #[test]
    fn snapshots_are_isolated_forks() {
        let base = Environment::new().add_decl(axiom("a")).expect("adds");
        let fork = base.clone(); // O(1) snapshot
        let extended = base.add_decl(axiom("b")).expect("adds");
        assert_eq!(
            fork.len(),
            1,
            "mutation after fork is invisible to the fork"
        );
        assert_eq!(extended.len(), 2);
        assert!(fork.find(&n("b")).is_none());
        // And the fork can diverge independently.
        let fork2 = fork.add_decl(axiom("c")).expect("adds");
        assert!(extended.find(&n("c")).is_none());
        assert!(fork2.find(&n("b")).is_none());
    }

    #[test]
    fn logical_roots_are_insertion_order_independent_and_semantic() {
        let forward = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.add_decl(axiom("b")))
            .and_then(|e| e.add_decl(axiom("c")))
            .expect("builds");
        let reverse = Environment::new()
            .add_decl(axiom("c"))
            .and_then(|e| e.add_decl(axiom("b")))
            .and_then(|e| e.add_decl(axiom("a")))
            .expect("builds");
        let opts = KVMap::new();
        assert_eq!(forward.logical_root(&opts), reverse.logical_root(&opts));

        // Different content ⇒ different root.
        let other = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.add_decl(axiom("b")))
            .expect("builds");
        assert_ne!(forward.logical_root(&opts), other.logical_root(&opts));

        // Options are part of the logical root.
        let mut opts2 = KVMap::new();
        opts2.insert(n("maxHeartbeats"), DataValue::OfNat(400_000));
        assert_ne!(forward.logical_root(&opts), forward.logical_root(&opts2));
    }

    #[test]
    fn extension_entries_enter_the_logical_root_in_order() {
        let opts = KVMap::new();
        let env = Environment::new()
            .register_extension(descriptor("simpExt"))
            .expect("registers");
        let one = env
            .push_extension_entry(&n("simpExt"), &b"e1"[..])
            .expect("pushes");
        let two = one
            .push_extension_entry(&n("simpExt"), &b"e2"[..])
            .expect("pushes");
        assert_ne!(env.logical_root(&opts), one.logical_root(&opts));
        assert_ne!(one.logical_root(&opts), two.logical_root(&opts));
        // Replay order is preserved exactly.
        let entries: Vec<&[u8]> = two
            .extension(&n("simpExt"))
            .expect("registered")
            .entries()
            .map(|e| &*e.payload)
            .collect();
        assert_eq!(entries, vec![b"e1".as_slice(), b"e2"]);
        // Unknown extension is a typed refusal.
        assert_eq!(
            env.push_extension_entry(&n("ghost"), &b"x"[..]),
            Err(EnvError::UnknownExtension { name: n("ghost") })
        );
    }

    #[test]
    fn environment_checkpoint_apply_preserves_exact_roots_and_unrelated_state() {
        let limits = CheckpointLimits::new(100, 10_000);
        let base = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(descriptor("simpExt")))
            .and_then(|env| env.register_extension(descriptor("otherExt")))
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"base"[..]))
            .and_then(|env| env.push_extension_entry(&n("otherExt"), &b"other"[..]))
            .expect("base environment builds");
        let target = base
            .push_extension_entry(&n("simpExt"), &b"suffix-a"[..])
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"suffix-b"[..]))
            .expect("target environment builds");
        let checkpoint = target
            .checkpoint_extension(&n("simpExt"), Some(&base), limits)
            .expect("environment suffix captures");
        let restored = base
            .apply_extension_checkpoint(&checkpoint, limits)
            .expect("environment suffix applies");

        assert_eq!(restored, target);
        assert_eq!(
            restored.logical_root(&KVMap::new()),
            target.logical_root(&KVMap::new())
        );
        assert_eq!(restored.find(&n("a")), target.find(&n("a")));
        assert_eq!(
            restored.extension(&n("otherExt")),
            target.extension(&n("otherExt"))
        );

        let divergent = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(descriptor("simpExt")))
            .and_then(|env| env.register_extension(descriptor("otherExt")))
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"wrong"[..]))
            .and_then(|env| env.push_extension_entry(&n("otherExt"), &b"other"[..]))
            .expect("same-length divergent branch builds");
        assert!(matches!(
            divergent.apply_extension_checkpoint(&checkpoint, limits),
            Err(EnvError::Checkpoint(
                CheckpointError::BaseHistoryMismatch { .. }
            ))
        ));
        assert_eq!(
            divergent
                .extension(&n("simpExt"))
                .expect("still registered")
                .entries()
                .last()
                .expect("one entry")
                .payload
                .as_ref(),
            b"wrong"
        );
    }

    #[test]
    fn environment_full_checkpoint_replaces_only_the_registered_journal() {
        let limits = CheckpointLimits::new(100, 10_000);
        let full_descriptor = ExtensionDescriptor {
            checkpoint: CheckpointSemantics::FullJournal,
            ..descriptor("fullExt")
        };
        let destination = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(full_descriptor))
            .expect("destination builds");
        let source = destination
            .push_extension_entry(&n("fullExt"), &b"one"[..])
            .and_then(|env| env.push_extension_entry(&n("fullExt"), &b"two"[..]))
            .expect("source builds");
        let checkpoint = source
            .checkpoint_extension(&n("fullExt"), None, limits)
            .expect("full environment checkpoint captures");
        let restored = destination
            .apply_extension_checkpoint(&checkpoint, limits)
            .expect("full checkpoint applies without a semantic base");
        assert_eq!(restored, source);
        assert_eq!(
            restored.logical_root(&KVMap::new()),
            source.logical_root(&KVMap::new())
        );
        assert!(matches!(
            source.checkpoint_extension(&n("ghost"), None, limits),
            Err(EnvError::UnknownExtension { .. })
        ));
    }

    #[test]
    fn extension_contracts_enter_the_logical_root() {
        let root = |merge, checkpoint, provenance| {
            let descriptor = ExtensionDescriptor {
                name: n("contractExt"),
                merge,
                checkpoint,
                provenance,
            };
            Environment::new()
                .register_extension(descriptor)
                .and_then(|env| env.push_extension_entry(&n("contractExt"), &b"entry"[..]))
                .expect("extension environment builds")
                .logical_root(&KVMap::new())
        };

        let append = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        let append_again = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        assert_eq!(
            append, append_again,
            "identical extension contracts and journals have stable identity"
        );

        let set_union = root(
            MergeSemantics::SetUnion,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        let review = root(
            MergeSemantics::ConflictsRequireReview,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        assert_ne!(append, set_union, "merge semantics enter the root");
        assert_ne!(append, review, "merge semantics enter the root");
        assert_ne!(
            set_union, review,
            "every merge variant has distinct identity"
        );

        let full_journal = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::FullJournal,
            PayloadProvenance::Understood,
        );
        assert_ne!(append, full_journal, "checkpoint semantics enter the root");

        let opaque = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Opaque,
        );
        assert_ne!(append, opaque, "payload provenance enters the root");
    }

    #[test]
    fn add_decl_preserves_extension_state() {
        // The mutant this kills: add_decl rebuilding the environment with empty
        // extensions (state silently dropped) — found surviving by the
        // env_snapshots E2E mutation lane, then pinned here forever.
        let env = Environment::new()
            .register_extension(descriptor("simpExt"))
            .expect("registers")
            .push_extension_entry(&n("simpExt"), &b"e1"[..])
            .expect("pushes");
        let with_decl = env.add_decl(axiom("a")).expect("adds");
        let state = with_decl
            .extension(&n("simpExt"))
            .expect("extension state survives add_decl");
        assert_eq!(state.len(), 1);
        // And the delta still reaches the logical root after the decl lands.
        let opts = KVMap::new();
        let bare = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.register_extension(descriptor("simpExt")))
            .expect("builds");
        assert_ne!(with_decl.logical_root(&opts), bare.logical_root(&opts));
    }

    #[test]
    fn operational_metadata_never_touches_the_logical_root() {
        let env = Environment::new().add_decl(axiom("a")).expect("adds");
        let opts = KVMap::new();
        let root = env.logical_root(&opts);

        let mut host_a = KVMap::new();
        host_a.insert(n("host"), DataValue::OfString("machine-a".into()));
        let mut host_b = KVMap::new();
        host_b.insert(n("host"), DataValue::OfString("machine-b".into()));

        // Same trusted environment, different hosts: same logical root, different
        // operational roots.
        assert_eq!(root, env.logical_root(&opts));
        assert_ne!(
            Environment::operational_root(&host_a),
            Environment::operational_root(&host_b)
        );
    }

    #[test]
    fn declaration_identity_enum_tags_are_explicit_and_distinct() {
        use crate::constants::{DefinitionVal, QuotVal};

        assert_eq!(definition_safety_tag(DefinitionSafety::Unsafe), 0);
        assert_eq!(definition_safety_tag(DefinitionSafety::Safe), 1);
        assert_eq!(definition_safety_tag(DefinitionSafety::Partial), 2);
        assert_eq!(quot_kind_tag(QuotKind::Type), 0);
        assert_eq!(quot_kind_tag(QuotKind::Ctor), 1);
        assert_eq!(quot_kind_tag(QuotKind::Lift), 2);
        assert_eq!(quot_kind_tag(QuotKind::Ind), 3);

        let base = || ConstantVal {
            name: n("tagged"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        };
        let definition = |safety| {
            ConstantInfo::Defn(DefinitionVal {
                base: base(),
                value: Expr::sort(Level::zero()),
                hints: ReducibilityHints::Opaque,
                safety,
                all: vec![n("tagged")],
            })
        };
        let quotient = |kind| ConstantInfo::Quot(QuotVal { base: base(), kind });
        let assert_pairwise_distinct = |infos: Vec<ConstantInfo>| {
            let digests: Vec<Digest> = infos.iter().map(Environment::decl_content_digest).collect();
            for (index, lhs) in digests.iter().enumerate() {
                for rhs in &digests[index + 1..] {
                    assert_ne!(lhs, rhs, "distinct schema tags must change identity");
                }
            }
        };
        assert_pairwise_distinct(vec![
            definition(DefinitionSafety::Unsafe),
            definition(DefinitionSafety::Safe),
            definition(DefinitionSafety::Partial),
        ]);
        assert_pairwise_distinct(vec![
            quotient(QuotKind::Type),
            quotient(QuotKind::Ctor),
            quotient(QuotKind::Lift),
            quotient(QuotKind::Ind),
        ]);

        let options = KVMap::new();
        let root = Environment::new()
            .add_decl(definition(DefinitionSafety::Safe))
            .expect("tagged definition is valid")
            .logical_root(&options);
        let repeated = Environment::new()
            .add_decl(definition(DefinitionSafety::Safe))
            .expect("same tagged definition is valid")
            .logical_root(&options);
        assert_eq!(root, repeated, "explicit tags are stable across rebuilds");
    }

    #[test]
    fn mutual_block_membership_changes_the_content_digest() {
        use crate::constants::{
            DefinitionSafety, DefinitionVal, InductiveVal, OpaqueVal, RecursorRule, RecursorVal,
            ReducibilityHints, TheoremVal,
        };
        // Every kind that carries an `all` (mutual block) must fold it into its
        // content digest: two otherwise-identical declarations that differ only in
        // their block grouping are distinct and must not collide (a per-decl CAS
        // keyed on this digest would otherwise return a stale `all`).
        let body = || Expr::sort(Level::zero());
        let ty = || ConstantVal {
            name: n("d"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        };

        let defn = |all: Vec<Name>| {
            ConstantInfo::Defn(DefinitionVal {
                base: ty(),
                value: body(),
                hints: ReducibilityHints::Opaque,
                safety: DefinitionSafety::Safe,
                all,
            })
        };
        let thm = |all: Vec<Name>| {
            ConstantInfo::Thm(TheoremVal {
                base: ty(),
                value: body(),
                all,
            })
        };
        let opaque = |all: Vec<Name>| {
            ConstantInfo::Opaque(OpaqueVal {
                base: ty(),
                value: body(),
                is_unsafe: false,
                all,
            })
        };
        let induct = |all: Vec<Name>| {
            ConstantInfo::Induct(InductiveVal {
                base: ty(),
                num_params: 0,
                num_indices: 0,
                all,
                ctors: vec![n("mk")],
                num_nested: 0,
                is_rec: false,
                is_unsafe: false,
                is_reflexive: false,
            })
        };
        let rec = |all: Vec<Name>| {
            ConstantInfo::Rec(RecursorVal {
                base: ty(),
                all,
                num_params: 0,
                num_indices: 0,
                num_motives: 1,
                num_minors: 1,
                rules: vec![RecursorRule {
                    ctor: n("mk"),
                    nfields: 0,
                    rhs: body(),
                }],
                k: false,
                is_unsafe: false,
            })
        };

        for (kind, make) in [
            ("definition", &defn as &dyn Fn(Vec<Name>) -> ConstantInfo),
            ("theorem", &thm),
            ("opaque", &opaque),
            ("inductive", &induct),
            ("recursor", &rec),
        ] {
            let solo = Environment::decl_content_digest(&make(vec![n("d")]));
            let grouped = Environment::decl_content_digest(&make(vec![n("d"), n("e")]));
            let reordered = Environment::decl_content_digest(&make(vec![n("e"), n("d")]));
            let renamed = Environment::decl_content_digest(&make(vec![n("d"), n("f")]));
            assert_ne!(
                solo, grouped,
                "{kind} mutual-block membership must change the content digest"
            );
            assert_ne!(
                grouped, reordered,
                "{kind} mutual-block order must change the content digest"
            );
            assert_ne!(
                grouped, renamed,
                "{kind} mutual-block names must change the content digest"
            );
        }

        let options = KVMap::new();
        let solo = Environment::new()
            .add_decl(opaque(vec![n("d")]))
            .expect("solo opaque declaration is valid");
        let grouped = Environment::new()
            .add_decl(opaque(vec![n("d"), n("e")]))
            .expect("grouped opaque declaration is valid");
        assert_ne!(
            solo.logical_root(&options),
            grouped.logical_root(&options),
            "opaque mutual-block membership must propagate into logical snapshot identity"
        );
    }

    #[test]
    fn logical_root_is_schedule_independent_across_threads() {
        let names: Vec<String> = (0..64).map(|i| format!("decl{i}")).collect();
        let sequential = {
            let mut env = Environment::new();
            for name in &names {
                env = env.add_decl(axiom(name)).expect("adds");
            }
            env.logical_root(&KVMap::new())
        };
        for threads in [2usize, 8] {
            let chunks: Vec<Vec<String>> = names
                .chunks(names.len().div_ceil(threads))
                .map(<[String]>::to_vec)
                .collect();
            let root = std::thread::scope(|scope| {
                let handles: Vec<_> = chunks
                    .iter()
                    .map(|chunk| scope.spawn(move || chunk.clone()))
                    .collect();
                let mut env = Environment::new();
                for handle in handles {
                    for name in handle.join().expect("worker") {
                        env = env.add_decl(axiom(&name)).expect("adds");
                    }
                }
                env.logical_root(&KVMap::new())
            });
            assert_eq!(root, sequential, "{threads}-thread interleaving diverged");
        }
    }
}
