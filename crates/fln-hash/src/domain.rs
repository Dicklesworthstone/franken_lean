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
    /// The operational-metadata root of an environment commit (§7.1) — host facts,
    /// paths, timings: everything the logical root deliberately excludes, digested
    /// separately so receipts carry both without mixing them.
    OperationalMeta,
    /// A canonical-serialization schema descriptor (self-describing corpora).
    CanonicalSchema,
    /// Immutable module topology plus declaration/extension contribution
    /// provenance. This is an explicit additional Ledger/receipt identity and is
    /// deliberately separate from both `LogicalRoot` and `OperationalMeta`.
    ModuleProvenance,
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
            Domain::OperationalMeta => "fln 2026 domain operational-meta/1",
            Domain::CanonicalSchema => "fln 2026 domain canonical-schema/1",
            Domain::ModuleProvenance => "fln 2026 domain module-provenance/1",
            Domain::Fixture => "fln 2026 domain fixture/1",
        }
    }

    /// Every registered domain, for registry-wide tests (pairwise distinctness,
    /// frozen-vector stability).
    pub const ALL: [Domain; 12] = [
        Domain::DeclContent,
        Domain::LogicalRoot,
        Domain::ExtensionDelta,
        Domain::OptionsSet,
        Domain::Receipt,
        Domain::TransparencyLeaf,
        Domain::TransparencyNode,
        Domain::CacheKey,
        Domain::OperationalMeta,
        Domain::CanonicalSchema,
        Domain::ModuleProvenance,
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

    /// The display name a fixture row uses for a domain. Written out rather than
    /// derived from `Debug` so the fixture's first column is a stable contract and not
    /// hostage to a formatting change.
    fn row_name(domain: Domain) -> &'static str {
        match domain {
            Domain::DeclContent => "DeclContent",
            Domain::LogicalRoot => "LogicalRoot",
            Domain::ExtensionDelta => "ExtensionDelta",
            Domain::OptionsSet => "OptionsSet",
            Domain::Receipt => "Receipt",
            Domain::TransparencyLeaf => "TransparencyLeaf",
            Domain::TransparencyNode => "TransparencyNode",
            Domain::CacheKey => "CacheKey",
            Domain::OperationalMeta => "OperationalMeta",
            Domain::CanonicalSchema => "CanonicalSchema",
            Domain::ModuleProvenance => "ModuleProvenance",
            Domain::Fixture => "Fixture",
        }
    }

    /// The four fixture inputs, in column order. See the fixture header for why these:
    /// empty, a short input, exactly one BLAKE3 chunk, and a multi-chunk input that
    /// forces the parent/tree path.
    fn fixture_inputs() -> [Vec<u8>; 4] {
        [
            Vec::new(),
            b"abc".to_vec(),
            vec![0u8; 1024],
            (0..2049).map(|i| (i % 251) as u8).collect(),
        ]
    }

    /// **The whole fixture contract, in one function.**
    ///
    /// Both the suite and every plant below call exactly this, because a mutation
    /// harness that drives a subset of the production contract can report a false green
    /// — the lesson from this bead's BLAKE3 fixture round, where a dropped-row plant
    /// survived because the row count lived in the test body instead of the parser.
    ///
    /// Returns the number of rows checked, or the first violation.
    fn check_domain_vector_contract(text: &str) -> Result<usize, String> {
        let mut saw_schema = false;
        let mut rows: std::collections::BTreeMap<&str, (&str, Vec<&str>)> =
            std::collections::BTreeMap::new();
        for line in text.lines() {
            if line == "# schema fln-domain-vectors/1" {
                saw_schema = true;
                continue;
            }
            if line.starts_with('#') || line.trim().is_empty() {
                continue;
            }
            let fields: Vec<&str> = line.split('|').collect();
            // domain + tag + one digest per input. A short row and a trailing field are
            // both rejected: the BLAKE3 fixture silently accepted trailing fields until
            // a plant found it.
            if fields.len() != 2 + fixture_inputs().len() {
                return Err(format!(
                    "row has {} fields, expected {}: {line}",
                    fields.len(),
                    2 + fixture_inputs().len()
                ));
            }
            for digest in &fields[2..] {
                if digest.len() != 64 || !digest.bytes().all(|b| b.is_ascii_hexdigit()) {
                    return Err(format!("field is not a 64-char hex digest: {digest}"));
                }
                if digest.bytes().any(|b| b.is_ascii_uppercase()) {
                    return Err(format!("digest must be lowercase hex: {digest}"));
                }
            }
            if rows
                .insert(fields[0], (fields[1], fields[2..].to_vec()))
                .is_some()
            {
                return Err(format!("duplicate row for domain {}", fields[0]));
            }
        }
        if !saw_schema {
            return Err("fixture missing its schema line".to_string());
        }

        // The join, both directions. A registered domain with no row means the fixture
        // is stale (a new domain shipped unfrozen); a row naming no registered domain
        // means the fixture describes something that no longer exists.
        let inputs = fixture_inputs();
        for domain in Domain::ALL {
            let name = row_name(domain);
            let Some((tag, digests)) = rows.remove(name) else {
                return Err(format!(
                    "no fixture row for registered domain {name}; every domain's tag must \
                     be frozen, or a new domain can change nothing visibly and everything \
                     underneath"
                ));
            };
            if tag != domain.tag() {
                return Err(format!(
                    "{name}: tag drifted from the frozen value.\n  fixture: {tag}\n  code:    {}\n\
                     A tag change re-digests every artifact under this domain — it is an \
                     epoch-class event, not a refactor.",
                    domain.tag()
                ));
            }
            for (input, expected) in inputs.iter().zip(&digests) {
                let actual = hash(domain, input).to_hex();
                if actual != *expected {
                    return Err(format!(
                        "{name}: digest drifted for the {}-byte input.\n  expected: {expected}\n\
                         \n  actual:   {actual}",
                        input.len()
                    ));
                }
            }
        }
        if let Some((extra, _)) = rows.iter().next() {
            return Err(format!(
                "fixture row {extra} names no registered domain — the registry shrank, or \
                 the row is a typo that was silently checking nothing"
            ));
        }
        Ok(Domain::ALL.len())
    }

    use fln_core::name::Name;

    const DOMAIN_VECTORS: &str = include_str!("../fixtures/domain_vectors.txt");

    #[test]
    fn every_domain_tag_and_digest_matches_the_frozen_fixture() {
        match check_domain_vector_contract(DOMAIN_VECTORS) {
            Ok(rows) => assert_eq!(rows, Domain::ALL.len()),
            Err(violation) => panic!("{violation}"),
        }
    }

    const HOST_ATTESTATIONS: &str = include_str!("../fixtures/host_attestations.txt");

    /// One recorded attestation.
    #[derive(Debug, PartialEq, Eq)]
    struct Attestation {
        platform: String,
        host: String,
        fixture_digest: String,
        logical_root: String,
    }

    fn recorded_attestations(text: &str) -> Vec<Attestation> {
        let mut rows = Vec::new();
        for line in text.lines() {
            if line.starts_with('#') || line.trim().is_empty() {
                continue;
            }
            let fields: Vec<&str> = line.split('|').collect();
            assert_eq!(
                fields.len(),
                4,
                "attestation row must have 4 fields: {line}"
            );
            for digest in &fields[2..] {
                assert_eq!(digest.len(), 64, "digest must be 64 hex chars: {digest}");
                assert!(digest.bytes().all(|b| b.is_ascii_hexdigit()));
            }
            rows.push(Attestation {
                platform: fields[0].to_string(),
                host: fields[1].to_string(),
                fixture_digest: fields[2].to_string(),
                logical_root: fields[3].to_string(),
            });
        }
        rows
    }

    /// **The multi-host identity claim, at exactly the level the evidence supports**
    /// (bead fln-laxj).
    ///
    /// This is deliberately NOT "a cross-platform test". A cross-platform test that only
    /// ever runs on one platform passes trivially and reads as evidence, which is the trap
    /// this bead exists to close. What is asserted here is the honest pair:
    ///
    /// 1. **Agreement is enforced on whatever host runs it.** The recorded rows form a
    ///    consensus, and this host must reproduce it. So every CI machine that runs the
    ///    suite is checking host-independence rather than taking it on trust — and a host
    ///    can only be *added* to the file by actually running there.
    /// 2. **The platform set is asserted to be a single member**, because it is. That is
    ///    not a limitation dressed up as a check: it is the trigger that makes the
    ///    unearned claim visible. The day a genuinely different platform agrees, this
    ///    fails and says so, forcing the BLOCKED cross-platform row in
    ///    `ci/PARITY_LEDGER.txt` to be raised deliberately instead of letting new evidence
    ///    sit unclaimed.
    #[test]
    fn recorded_hosts_agree_and_the_platform_set_is_still_one_member() {
        let recorded = recorded_attestations(HOST_ATTESTATIONS);
        assert!(
            recorded.len() >= 2,
            "the multi-host claim needs at least two recorded hosts; found {}",
            recorded.len()
        );

        let hosts: std::collections::BTreeSet<&str> =
            recorded.iter().map(|a| a.host.as_str()).collect();
        assert_eq!(
            hosts.len(),
            recorded.len(),
            "two rows name the same host, so they are one machine's evidence twice: {hosts:?}"
        );

        // Consensus: every recorded host agrees, or there is nothing to claim.
        let digests: std::collections::BTreeSet<&str> =
            recorded.iter().map(|a| a.fixture_digest.as_str()).collect();
        let roots: std::collections::BTreeSet<&str> =
            recorded.iter().map(|a| a.logical_root.as_str()).collect();
        assert_eq!(
            digests.len(),
            1,
            "recorded hosts disagree on the vectors: {digests:?}"
        );
        assert_eq!(
            roots.len(),
            1,
            "recorded hosts disagree on the logical root: {roots:?}"
        );

        // THIS host must reproduce the consensus. This is what makes the file evidence
        // rather than a claim: it is re-checked wherever the suite runs.
        let here_digest = hash(Domain::Fixture, DOMAIN_VECTORS.as_bytes()).to_hex();
        assert_eq!(
            Some(here_digest.as_str()),
            digests.iter().next().copied(),
            "this host's domain vectors differ from every recorded host's — either a tag or \
             a vector is host-dependent, or the fixture changed without the attestations \
             being regenerated"
        );

        // The unearned half, held as a trigger rather than a comment.
        let platforms: std::collections::BTreeSet<&str> =
            recorded.iter().map(|a| a.platform.as_str()).collect();
        assert_eq!(
            platforms.len(),
            1,
            "a second PLATFORM now appears in the attestations ({platforms:?}). That is new \
             evidence, not a failure: SUITE.lock declared one certified target when this \
             was written, so the cross-platform row in ci/PARITY_LEDGER.txt is BLOCKED. If \
             the matrix has genuinely grown and the platforms agree, raise that row and \
             update this assertion deliberately."
        );
    }

    /// Emit a host attestation for the multi-host identity claim (bead fln-laxj).
    ///
    /// **This test does not, and cannot, verify cross-host agreement.** A single run sees
    /// one host, so any in-process assertion of "all hosts agree" would pass trivially and
    /// read as evidence — the exact trap fln-laxj exists to close. What it does is emit the
    /// facts a comparison needs, in a line-oriented form, so agreement is established
    /// *outside* by running it on N hosts and diffing. The claim belongs to whoever ran it
    /// on N hosts and can show N attestations; it never belongs to this assertion.
    ///
    /// Run with `-- --nocapture` and compare the `fln-host-attestation/1` lines.
    #[test]
    fn emit_host_attestation_for_external_multi_host_comparison() {
        // Platform facts are compile-time, so they describe the target this binary was
        // built for — which is what a cross-PLATFORM comparison turns on.
        let platform = format!(
            "{}-{}-{}-{}bit-{}",
            std::env::consts::ARCH,
            std::env::consts::OS,
            std::env::consts::FAMILY,
            usize::BITS,
            if cfg!(target_endian = "little") {
                "le"
            } else {
                "be"
            }
        );
        // Machine identity, so a multi-HOST comparison can tell two runs apart. Absent is
        // reported as absent rather than defaulted: an unidentifiable host is not a host
        // that agreed.
        let host = std::fs::read_to_string("/etc/hostname")
            .map(|text| text.trim().to_string())
            .unwrap_or_else(|_| "unidentified".to_string());

        // One digest over the whole frozen fixture, so a single field carries every
        // domain tag and every vector: if any of them differed on another host, this
        // differs.
        let fixture_digest = hash(Domain::Fixture, DOMAIN_VECTORS.as_bytes()).to_hex();

        // And one logical root over a fixed closure, which is the other half of the
        // claim. Built from constants so it depends on nothing but the code under test.
        let root = {
            let mut builder = crate::root::LogicalRootBuilder::new();
            for index in 0..8u64 {
                builder.add_decl(
                    &Name::num(Name::str(Name::anonymous(), "Fixed"), index),
                    crate::root::decl_content_digest(format!("body-{index}").as_bytes()),
                );
            }
            builder.add_extension_delta(
                &Name::str(Name::anonymous(), "simp"),
                crate::root::extension_delta_digest(b"delta"),
            );
            builder.finalize().to_string()
        };

        println!(
            "fln-host-attestation/1 platform={platform} host={host}              fixture_digest={fixture_digest} logical_root={root}"
        );

        // The only thing assertable from one host: the attestation is well-formed and its
        // digests are the ones this build actually produces. Agreement is not asserted.
        assert_eq!(fixture_digest.len(), 64);
        assert_eq!(root.len(), 64);
        assert!(
            check_domain_vector_contract(DOMAIN_VECTORS).is_ok(),
            "the attestation is only meaningful if the fixture it digests is intact"
        );
    }

    #[test]
    fn the_fixture_contract_kills_tag_digest_and_structural_damage() {
        // Every plant runs the full contract over damaged text, exactly as the suite
        // runs it over the real fixture. The checked-in fixture is never mutated.
        let plant = |from: &str, to: &str| DOMAIN_VECTORS.replacen(from, to, 1);

        // A TAG EDIT — the drift this fixture exists for. Before it, this change
        // re-digested every artifact in the program and no test failed.
        let retagged = plant(
            "fln 2026 domain decl-content/1",
            "fln 2026 domain decl-content/2",
        );
        let error = check_domain_vector_contract(&retagged).expect_err("a tag edit must fail");
        assert!(error.contains("tag drifted"), "{error}");

        // A ONE-BIT DIGEST FLIP, on a mid-fixture row rather than the first, and on the
        // multi-chunk column rather than the empty one — so the check is known to reach
        // every row and every input, not just the cheap first cell.
        let victim = &DOMAIN_VECTORS
            .lines()
            .find(|line| line.starts_with("CacheKey|"))
            .expect("the CacheKey row exists");
        let last = victim.rsplit('|').next().expect("a last column");
        let mut flipped_hex = last.to_string();
        let first = flipped_hex.remove(0);
        let value = first.to_digit(16).expect("hex");
        flipped_hex.insert(0, std::char::from_digit(value ^ 1, 16).expect("still hex"));
        let flipped = plant(last, &flipped_hex);
        let error = check_domain_vector_contract(&flipped).expect_err("a digest flip must fail");
        assert!(error.contains("digest drifted"), "{error}");
        assert!(
            error.contains("2049"),
            "the flip must be reported against the multi-chunk input: {error}"
        );

        // STRUCTURAL DAMAGE. Each is a distinct way a fixture stops checking what it
        // claims to check.
        let dropped = DOMAIN_VECTORS.replacen(
            &format!("{}\n", DOMAIN_VECTORS.lines().last().expect("a last row")),
            "",
            1,
        );
        let error = check_domain_vector_contract(&dropped).expect_err("a dropped row must fail");
        assert!(
            error.contains("no fixture row for registered domain"),
            "{error}"
        );

        let duplicated = format!(
            "{DOMAIN_VECTORS}{}\n",
            DOMAIN_VECTORS.lines().last().unwrap()
        );
        assert!(
            check_domain_vector_contract(&duplicated)
                .expect_err("a duplicated row must fail")
                .contains("duplicate row"),
        );

        let unknown = format!(
            "{DOMAIN_VECTORS}NotADomain|fln 2026 domain nope/1|{}\n",
            std::iter::repeat_n("00".repeat(32), 4)
                .collect::<Vec<_>>()
                .join("|")
        );
        assert!(
            check_domain_vector_contract(&unknown)
                .expect_err("a row for no registered domain must fail")
                .contains("names no registered domain"),
        );

        let short = plant("CacheKey|", "CacheKey|extra|");
        assert!(
            check_domain_vector_contract(&short)
                .expect_err("a wrong-width row must fail")
                .contains("fields, expected"),
        );

        let no_schema = plant("# schema fln-domain-vectors/1", "# schema wrong/1");
        assert!(
            check_domain_vector_contract(&no_schema)
                .expect_err("a damaged schema line must fail")
                .contains("missing its schema line"),
        );

        // And the undamaged fixture still passes, so none of the above is a blanket
        // refusal that would also reject a healthy fixture.
        assert!(check_domain_vector_contract(DOMAIN_VECTORS).is_ok());
    }
}
