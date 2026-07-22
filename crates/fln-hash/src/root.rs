//! Logical roots (plan §7.1; bead franken_lean-rps, requirement d).
//!
//! A logical root digests **declarations + extension deltas + options** and nothing
//! else. Exclusion of the operational world is structural: this API has no parameter
//! through which wall-clock, paths, host names, or scheduler traces could enter, and
//! the digest is insertion-order independent, so two hosts (or two thread counts)
//! producing the same trusted environment produce the same root — the cache key the
//! Ledger, receipts, and Envoy all speak.

use std::collections::BTreeMap;

use crate::canon::{CanonWriter, Canonical};
use crate::domain::{Digest, Domain, DomainHasher, hash};
use fln_core::name::Name;
use fln_core::options::KVMap;

/// The logical root of an environment commit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LogicalRoot(pub Digest);

impl std::fmt::Display for LogicalRoot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Order-independent accumulator for one environment commit.
#[derive(Debug, Default)]
pub struct LogicalRootBuilder {
    /// Declaration name (canonical bytes) -> content digest. BTreeMap makes the
    /// digest schedule-independent by construction (FL-INV-01 posture).
    decls: BTreeMap<Vec<u8>, Digest>,
    /// Extension name (canonical bytes) -> delta digest.
    extension_deltas: BTreeMap<Vec<u8>, Digest>,
    options: Option<Digest>,
}

impl LogicalRootBuilder {
    pub fn new() -> LogicalRootBuilder {
        LogicalRootBuilder::default()
    }

    /// Record a declaration's content digest (produced under [`Domain::DeclContent`]).
    /// Re-adding the same name replaces the digest — last write wins, mirroring an
    /// environment map.
    pub fn add_decl(&mut self, name: &Name, content: Digest) -> &mut LogicalRootBuilder {
        self.decls.insert(name.to_canonical_bytes(), content);
        self
    }

    /// Record one extension's delta digest (produced under
    /// [`Domain::ExtensionDelta`]).
    pub fn add_extension_delta(
        &mut self,
        extension: &Name,
        delta: Digest,
    ) -> &mut LogicalRootBuilder {
        self.extension_deltas
            .insert(extension.to_canonical_bytes(), delta);
        self
    }

    /// Record the elaboration-relevant options set. The KVMap is digested via its
    /// canonical encoding under [`Domain::OptionsSet`].
    pub fn set_options(&mut self, options: &KVMap) -> &mut LogicalRootBuilder {
        self.options = Some(hash(Domain::OptionsSet, &options.to_canonical_bytes()));
        self
    }

    /// Finalize under [`Domain::LogicalRoot`]: a canonical stream of counts and
    /// sorted (key, digest) pairs.
    pub fn finalize(&self) -> LogicalRoot {
        let mut stream = CanonWriter::new();
        stream.u64(self.decls.len() as u64);
        for (name_bytes, digest) in &self.decls {
            stream.bytes(name_bytes);
            stream.bytes(&digest.0);
        }
        stream.u64(self.extension_deltas.len() as u64);
        for (ext_bytes, digest) in &self.extension_deltas {
            stream.bytes(ext_bytes);
            stream.bytes(&digest.0);
        }
        match &self.options {
            Some(digest) => {
                stream.u8(1);
                stream.bytes(&digest.0);
            }
            None => stream.u8(0),
        }
        let mut hasher = DomainHasher::new(Domain::LogicalRoot);
        hasher.update(&stream.into_bytes());
        LogicalRoot(hasher.finalize())
    }
}

/// Digest one declaration's content bytes under the declaration domain — the helper
/// every producer uses so nobody hand-rolls the domain choice.
pub fn decl_content_digest(canonical_content: &[u8]) -> Digest {
    hash(Domain::DeclContent, canonical_content)
}

/// Digest one extension delta's canonical bytes.
pub fn extension_delta_digest(canonical_delta: &[u8]) -> Digest {
    hash(Domain::ExtensionDelta, canonical_delta)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::options::DataValue;

    fn name(s: &str) -> Name {
        Name::str(Name::anonymous(), s)
    }

    fn sample_entries() -> Vec<(Name, Digest)> {
        (0..32)
            .map(|i| {
                (
                    Name::num(name("decl"), i),
                    decl_content_digest(format!("content-{i}").as_bytes()),
                )
            })
            .collect()
    }

    #[test]
    fn root_is_insertion_order_independent() {
        let entries = sample_entries();
        let mut forward = LogicalRootBuilder::new();
        for (n, d) in &entries {
            forward.add_decl(n, *d);
        }
        let mut reverse = LogicalRootBuilder::new();
        for (n, d) in entries.iter().rev() {
            reverse.add_decl(n, *d);
        }
        assert_eq!(forward.finalize(), reverse.finalize());
    }

    #[test]
    fn root_is_schedule_independent_across_thread_counts() {
        // The FL-INV-01 posture at this layer: {1, 8} threads, arbitrary interleaving,
        // same commit ⇒ same root.
        let entries = sample_entries();
        let sequential = {
            let mut b = LogicalRootBuilder::new();
            for (n, d) in &entries {
                b.add_decl(n, *d);
            }
            b.finalize()
        };
        for threads in [2usize, 8] {
            let chunks: Vec<Vec<(Name, Digest)>> = entries
                .chunks(entries.len().div_ceil(threads))
                .map(<[(Name, Digest)]>::to_vec)
                .collect();
            let collected = std::thread::scope(|scope| {
                let handles: Vec<_> = chunks
                    .iter()
                    .map(|chunk| scope.spawn(move || chunk.clone()))
                    .collect();
                let mut b = LogicalRootBuilder::new();
                for handle in handles {
                    for (n, d) in handle.join().expect("worker") {
                        b.add_decl(&n, d);
                    }
                }
                b.finalize()
            });
            assert_eq!(collected, sequential, "{threads} threads diverged");
        }
    }

    #[test]
    fn root_distinguishes_every_semantic_input() {
        let base = {
            let mut b = LogicalRootBuilder::new();
            b.add_decl(&name("a"), decl_content_digest(b"x"));
            b.finalize()
        };
        // Different content.
        let mut changed = LogicalRootBuilder::new();
        changed.add_decl(&name("a"), decl_content_digest(b"y"));
        assert_ne!(changed.finalize(), base);
        // Different name.
        let mut renamed = LogicalRootBuilder::new();
        renamed.add_decl(&name("b"), decl_content_digest(b"x"));
        assert_ne!(renamed.finalize(), base);
        // An extension delta changes the root.
        let mut with_ext = LogicalRootBuilder::new();
        with_ext.add_decl(&name("a"), decl_content_digest(b"x"));
        with_ext.add_extension_delta(&name("simp"), extension_delta_digest(b"d"));
        assert_ne!(with_ext.finalize(), base);
        // Options change the root.
        let mut with_opts = LogicalRootBuilder::new();
        with_opts.add_decl(&name("a"), decl_content_digest(b"x"));
        let mut opts = KVMap::new();
        opts.insert(name("pp"), DataValue::OfBool(true));
        with_opts.set_options(&opts);
        assert_ne!(with_opts.finalize(), base);
    }

    #[test]
    fn last_write_wins_like_an_environment_map() {
        let mut once = LogicalRootBuilder::new();
        once.add_decl(&name("a"), decl_content_digest(b"new"));
        let mut twice = LogicalRootBuilder::new();
        twice.add_decl(&name("a"), decl_content_digest(b"old"));
        twice.add_decl(&name("a"), decl_content_digest(b"new"));
        assert_eq!(once.finalize(), twice.finalize());
    }

    #[test]
    fn decl_and_extension_maps_do_not_alias() {
        // The same (name, digest) pair recorded as a decl vs as an extension delta
        // must produce different roots — the stream keeps the two sections apart.
        let digest = decl_content_digest(b"x");
        let mut as_decl = LogicalRootBuilder::new();
        as_decl.add_decl(&name("a"), digest);
        let mut as_ext = LogicalRootBuilder::new();
        as_ext.add_extension_delta(&name("a"), digest);
        assert_ne!(as_decl.finalize(), as_ext.finalize());
    }
}
