//! Logical roots (plan §7.1; bead franken_lean-rps, requirement d).
//!
//! A logical root digests **declarations + extension deltas + options** and nothing
//! else. Exclusion of the operational world is structural: this API has no parameter
//! through which wall-clock, paths, host names, or scheduler traces could enter — it is
//! the cache key the Ledger, receipts, and Envoy all speak.
//!
//! **Declarations and extension deltas are insertion-order independent**, so any number
//! of hosts or thread counts that accumulate the same ones produce the same root.
//!
//! **Options are not**, and this doc claimed they were until bead franken_lean-rps
//! checked it. Options go through `KVMap`'s order-sensitive canonical encoding, because
//! upstream `KVMap` is an ordered association list and the Tribunal's exclusive
//! metamorphic law requires a permutation to move the root. So two hosts that set the
//! same options in a different order get different roots even though every option lookup
//! agrees. [`set_options`] states the consequence and names the projection a caller uses
//! when it wants set identity instead.
//!
//! Every one of the three inputs is now pinned in **both** directions — permuting must
//! (or must not) move the root, *and* distinct inputs must still separate — so whichever
//! way the options question is finally settled, it cannot change by accident.
//!
//! [`set_options`]: LogicalRootBuilder::set_options

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

    /// Record the elaboration-relevant options, digested under [`Domain::OptionsSet`]
    /// via `KVMap`'s canonical encoding — which is **order-sensitive**.
    ///
    /// So options are the one input to this root that a permutation moves, and that is
    /// deliberate: the Tribunal's exclusive metamorphic law
    /// (`fln-conformance/tests/metamorphic_laws.rs::canonical_ordered_rows_are_order_sensitive`)
    /// requires every non-identity permutation of unique rows to change both the
    /// canonical bytes and the options-bearing root, on the ground that upstream `KVMap`
    /// is an ordered association list and therefore an ordering IS part of the value.
    ///
    /// **Know what that costs you**, because it is not obvious and the module doc used to
    /// claim the opposite. With the unique keys `KVMap` guarantees, insertion order is
    /// unobservable through lookup: two differently-ordered maps carrying the same pairs
    /// agree on every `find`, `contains`, and `get_*`. Two hosts that set the same
    /// options in a different order therefore produce *different* logical roots while
    /// behaving identically — a spurious cache miss, and two identities for what a reader
    /// would call one environment. A caller that wants set identity must canonicalize
    /// first; [`kvmap_canonical_set_bytes`](crate::canon::kvmap_canonical_set_bytes) is
    /// that projection, and it is a separate schema precisely so the choice is explicit
    /// at the call site rather than smuggled into this digest.
    ///
    /// Whether requirement (d)'s "two hosts producing the same trusted environment share
    /// a logical root" is satisfied by this reading is a live question recorded on bead
    /// franken_lean-rps: it turns on whether option order is part of the environment.
    /// Both directions are pinned meanwhile, so neither answer can drift in silently —
    /// see `options_are_identified_as_an_ordered_list_not_a_set` and
    /// `option_identity_does_not_collapse_distinct_option_sets`.
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

    fn option_pairs() -> Vec<(Name, DataValue)> {
        vec![
            (name("pp.all"), DataValue::OfBool(true)),
            (name("maxHeartbeats"), DataValue::OfNat(200)),
            (name("trace.simp"), DataValue::OfString("on".to_string())),
            (name("weight"), DataValue::OfInt(-3)),
        ]
    }

    fn map_of(pairs: &[(Name, DataValue)]) -> KVMap {
        let mut map = KVMap::new();
        for (key, value) in pairs {
            map.insert(key.clone(), value.clone());
        }
        map
    }

    fn root_with_options(options: &KVMap) -> LogicalRoot {
        let mut b = LogicalRootBuilder::new();
        b.add_decl(&name("Nat.add"), decl_content_digest(b"body"));
        b.set_options(options);
        b.finalize()
    }

    /// Options are the one input a permutation moves, and the exact boundary is worth
    /// pinning rather than inferring: EVERY non-identity permutation must move the root
    /// (matching the Tribunal's exclusive MR), while the identity permutation must not,
    /// and the two maps must remain indistinguishable by lookup throughout — which is
    /// what makes this a deliberate choice about identity rather than an accident.
    ///
    /// The module doc used to claim unqualified insertion-order independence, so a reader
    /// had no way to learn this from either the doc or a test. Whichever way the question
    /// on franken_lean-rps is settled, flipping this behaviour now requires editing a
    /// test that says why.
    #[test]
    fn options_are_identified_as_an_ordered_list_not_a_set() {
        let pairs = option_pairs();
        let baseline = root_with_options(&map_of(&pairs));
        let reference = map_of(&pairs);

        // All 24 permutations of four entries, so the claim covers adjacent swaps and
        // full reversals alike rather than one convenient shuffle.
        let mut indices: Vec<usize> = (0..pairs.len()).collect();
        let mut seen = 0usize;
        let identity: Vec<usize> = (0..pairs.len()).collect();
        permute(&mut indices, 0, &mut |order| {
            let shuffled: Vec<(Name, DataValue)> =
                order.iter().map(|&i| pairs[i].clone()).collect();
            let map = map_of(&shuffled);

            // Indistinguishable by every observable lookup: this is the cost being
            // accepted, stated as an assertion so it cannot be forgotten.
            for (key, _) in &pairs {
                assert_eq!(
                    map.find(key),
                    reference.find(key),
                    "{order:?} changed a lookup"
                );
            }
            assert_eq!(map.len(), reference.len());

            if order == identity.as_slice() {
                assert_eq!(
                    root_with_options(&map),
                    baseline,
                    "the identity permutation moved the root"
                );
            } else {
                assert_ne!(
                    root_with_options(&map),
                    baseline,
                    "permutation {order:?} did NOT move the root — options would be a set, \
                     contradicting the Tribunal's exclusive MR"
                );
            }
            seen += 1;
        });
        assert_eq!(seen, 24, "the permutation walk is incomplete");

        // The set projection is the escape hatch, and it must genuinely be one: over the
        // same permutations it must NOT vary. A caller who wants set identity has a
        // supported way to get it.
        let projections: std::collections::BTreeSet<Vec<u8>> = {
            let mut indices: Vec<usize> = (0..pairs.len()).collect();
            let mut set = std::collections::BTreeSet::new();
            permute(&mut indices, 0, &mut |order| {
                let shuffled: Vec<(Name, DataValue)> =
                    order.iter().map(|&i| pairs[i].clone()).collect();
                set.insert(crate::canon::kvmap_canonical_set_bytes(&map_of(&shuffled)));
            });
            set
        };
        assert_eq!(
            projections.len(),
            1,
            "the set projection varied across permutations, so it is not a set view"
        );
    }

    /// The other direction, which is what keeps the test above from being satisfiable by
    /// a digest that simply varies with everything: distinct option content must separate,
    /// and it must separate for the right reasons.
    #[test]
    fn option_identity_does_not_collapse_distinct_option_sets() {
        let pairs = option_pairs();
        let base = root_with_options(&map_of(&pairs));

        // A different value under the same key.
        let mut changed = pairs.clone();
        changed[1].1 = DataValue::OfNat(201);
        assert_ne!(root_with_options(&map_of(&changed)), base, "value ignored");

        // A different key carrying the same value.
        let mut renamed = pairs.clone();
        renamed[0].0 = name("pp.raw");
        assert_ne!(root_with_options(&map_of(&renamed)), base, "key ignored");

        // Same multiset of values, swapped between two keys — the case a digest that
        // hashed keys and values in separate streams would miss.
        let mut swapped = pairs.clone();
        swapped[0].1 = DataValue::OfBool(false);
        let mut also_swapped = swapped.clone();
        also_swapped.swap(0, 3);
        also_swapped[0].0 = pairs[0].0.clone();
        also_swapped[3].0 = pairs[3].0.clone();
        assert_ne!(
            root_with_options(&map_of(&swapped)),
            base,
            "a changed boolean was ignored"
        );

        // A dropped entry and an added entry.
        assert_ne!(
            root_with_options(&map_of(&pairs[..3])),
            base,
            "a dropped option was ignored"
        );
        let mut extra = pairs.clone();
        extra.push((name("extra"), DataValue::OfBool(false)));
        assert_ne!(
            root_with_options(&map_of(&extra)),
            base,
            "an added option was ignored"
        );

        // Same type, different DataValue constructor: OfNat(1) is not OfInt(1) and not
        // OfBool(true), so the value tag must reach the root.
        for value in [
            DataValue::OfNat(1),
            DataValue::OfInt(1),
            DataValue::OfString("1".to_string()),
        ] {
            let mut typed = pairs.clone();
            typed[1].1 = value.clone();
            let mut other = pairs.clone();
            other[1].1 = DataValue::OfBool(true);
            assert_ne!(
                root_with_options(&map_of(&typed)),
                root_with_options(&map_of(&other)),
                "the value constructor {value:?} did not reach the root"
            );
        }

        // No options at all is distinct from an empty set of options, which is distinct
        // from a populated one: absence and emptiness are different facts.
        let no_options = {
            let mut b = LogicalRootBuilder::new();
            b.add_decl(&name("Nat.add"), decl_content_digest(b"body"));
            b.finalize()
        };
        let empty_options = root_with_options(&KVMap::new());
        assert_ne!(no_options, empty_options, "absent options == empty options");
        assert_ne!(empty_options, base);
    }

    /// Generate every permutation of `slice`, calling `visit` on each.
    fn permute(slice: &mut Vec<usize>, at: usize, visit: &mut impl FnMut(&[usize])) {
        if at == slice.len() {
            visit(slice);
            return;
        }
        for i in at..slice.len() {
            slice.swap(at, i);
            permute(slice, at + 1, visit);
            slice.swap(at, i);
        }
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
