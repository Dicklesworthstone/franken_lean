//! The domain-separation registry (bead franken_lean-rps, requirement a).
//!
//! Every hash in the program is produced under a [`Domain`] variant; the variant IS
//! the registration act. Tags are BLAKE3 `derive_key` context strings — the
//! construction's own domain-separation mechanism — and are **frozen forever** once
//! shipped: changing a tag changes every digest under it, which is an epoch-class
//! event, never a refactor. The enum is closed and matches are exhaustive, so adding
//! a domain forces this file (the reviewed registry) to change.

use crate::blake3;

/// A 32-byte digest under a registered domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Digest(pub [u8; 32]);

impl Digest {
    /// Lowercase hex, the canonical rendering everywhere (receipts, logs, ledgers).
    pub fn to_hex(&self) -> String {
        let mut out = String::with_capacity(64);
        for byte in self.0 {
            out.push(char::from_digit(u32::from(byte >> 4), 16).expect("nibble < 16"));
            out.push(char::from_digit(u32::from(byte & 0xf), 16).expect("nibble < 16"));
        }
        out
    }
}

impl std::fmt::Display for Digest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_hex())
    }
}

/// The registered hash domains. Tag strings are versioned (`/1`) so a semantic
/// change to what a domain covers registers a NEW tag rather than mutating history.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Domain {
    /// Content digest of a single declaration (Ledger decl records, §13).
    DeclContent,
    /// The logical root of an environment commit (§7.1) — the cache key the Ledger,
    /// receipts, and Envoy all speak.
    LogicalRoot,
    /// One environment-extension delta inside a commit (§7.1).
    ExtensionDelta,
    /// A canonical options set (elaboration-relevant options only).
    OptionsSet,
    /// A kernel/consensus receipt body (§8.6).
    Receipt,
    /// A transparency-log leaf (§8.6).
    TransparencyLeaf,
    /// A transparency-log interior node (leaf/node separation is mandatory for
    /// second-preimage resistance of the tree).
    TransparencyNode,
    /// A Ledger cache key (query fingerprint, §13.2).
    CacheKey,
    /// A canonical-serialization schema descriptor (self-describing corpora).
    CanonicalSchema,
    /// Tribunal fixture and corpus identity (test apparatus only).
    Fixture,
}

impl Domain {
    /// The frozen `derive_key` context string.
    pub const fn tag(self) -> &'static str {
        match self {
            Domain::DeclContent => "fln 2026 domain decl-content/1",
            Domain::LogicalRoot => "fln 2026 domain logical-root/1",
            Domain::ExtensionDelta => "fln 2026 domain extension-delta/1",
            Domain::OptionsSet => "fln 2026 domain options-set/1",
            Domain::Receipt => "fln 2026 domain receipt/1",
            Domain::TransparencyLeaf => "fln 2026 domain tlog-leaf/1",
            Domain::TransparencyNode => "fln 2026 domain tlog-node/1",
            Domain::CacheKey => "fln 2026 domain cache-key/1",
            Domain::CanonicalSchema => "fln 2026 domain canonical-schema/1",
            Domain::Fixture => "fln 2026 domain fixture/1",
        }
    }

    /// Every registered domain, for registry-wide tests (pairwise distinctness,
    /// frozen-vector stability).
    pub const ALL: [Domain; 10] = [
        Domain::DeclContent,
        Domain::LogicalRoot,
        Domain::ExtensionDelta,
        Domain::OptionsSet,
        Domain::Receipt,
        Domain::TransparencyLeaf,
        Domain::TransparencyNode,
        Domain::CacheKey,
        Domain::CanonicalSchema,
        Domain::Fixture,
    ];
}

/// An incremental hasher bound to its domain at construction — there is no way to
/// obtain one without naming a registered domain.
#[derive(Debug)]
pub struct DomainHasher {
    inner: blake3::Hasher,
}

impl DomainHasher {
    pub fn new(domain: Domain) -> DomainHasher {
        DomainHasher {
            inner: blake3::Hasher::new_derive_key(domain.tag()),
        }
    }

    pub fn update(&mut self, bytes: &[u8]) -> &mut DomainHasher {
        self.inner.update(bytes);
        self
    }

    pub fn finalize(&self) -> Digest {
        Digest(self.inner.finalize())
    }
}

/// One-shot domain hash.
pub fn hash(domain: Domain, bytes: &[u8]) -> Digest {
    DomainHasher::new(domain).update(bytes).finalize()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_bytes_under_two_domains_must_differ() {
        // The domain-confusion law: pairwise, across the whole registry.
        let inputs: [&[u8]; 3] = [b"", b"abc", &[0u8; 1024]];
        for input in inputs {
            for (i, a) in Domain::ALL.iter().enumerate() {
                for b in &Domain::ALL[i + 1..] {
                    assert_ne!(
                        hash(*a, input),
                        hash(*b, input),
                        "domains {a:?} and {b:?} collided on {} bytes",
                        input.len()
                    );
                }
            }
        }
    }

    #[test]
    fn tags_are_unique_and_versioned() {
        let mut seen = std::collections::BTreeSet::new();
        for domain in Domain::ALL {
            assert!(seen.insert(domain.tag()), "duplicate tag {}", domain.tag());
            assert!(
                domain.tag().starts_with("fln 2026 domain "),
                "tag missing the registry prefix: {}",
                domain.tag()
            );
            assert!(
                domain.tag().ends_with("/1"),
                "tag missing its version: {}",
                domain.tag()
            );
        }
    }

    #[test]
    fn incremental_equals_one_shot() {
        let mut h = DomainHasher::new(Domain::DeclContent);
        h.update(b"ab").update(b"c");
        assert_eq!(h.finalize(), hash(Domain::DeclContent, b"abc"));
    }

    #[test]
    fn hex_rendering_is_lowercase_and_stable() {
        let d = Digest([0xAB; 32]);
        assert_eq!(d.to_hex().len(), 64);
        assert!(d.to_hex().chars().all(|c| c == 'a' || c == 'b'));
        assert_eq!(format!("{d}"), d.to_hex());
    }
}
