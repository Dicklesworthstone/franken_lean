//! `epoch_lab_hash_chain` — the suite the `fln-euo` epic names for the epoch
//! laboratory's revision model (bead `fln-q3u4`).
//!
//! The epic names three mutations that must fail, and each one gets a test that
//! fails for ITS OWN reason rather than merely failing: **mutable revision**,
//! **partial epoch publication**, and **root mismatch**. A test that would pass
//! for any error is not a mutation kill, so every assertion below pins the
//! specific `ChainError` variant.

#![forbid(unsafe_code)]

use fln_epoch_lab::{
    CANDIDATE_FILE, CHAIN_FILE, Chain, ChainError, content_digest, publish, verify_epoch,
};
use std::path::{Path, PathBuf};

const EPOCH: &str = "v4.32.0";
const MANIFEST: &str = "MANIFEST.txt";

/// A scratch epoch directory. Named per test so runs cannot collide, and
/// per-process so two test binaries cannot either.
fn lab(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("fln-epoch-lab-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    dir
}

fn write_manifest(dir: &Path, body: &str) {
    std::fs::write(dir.join(MANIFEST), body).expect("write manifest");
}

// ---------------------------------------------------------------------------
// The model
// ---------------------------------------------------------------------------

#[test]
fn a_chain_grows_only_by_appending_and_verifies_end_to_end() {
    let c1 = Chain::genesis(EPOCH, content_digest(b"one"));
    assert_eq!(c1.verify(), Ok(()));
    assert_eq!(c1.head().index, 1);
    assert!(c1.head().parent.is_none(), "genesis has no parent");

    let c2 = c1.appended(content_digest(b"two"));
    let c3 = c2.appended(content_digest(b"three"));
    assert_eq!(c3.verify(), Ok(()));
    assert_eq!(c3.revisions().len(), 3);

    // Append is non-destructive: the earlier chain is untouched, and every
    // prefix is still exactly the history it was.
    assert_eq!(c1.revisions().len(), 1);
    assert_eq!(&c3.revisions()[..2], c2.revisions());

    // Each revision names its predecessor's root, which is what makes the
    // history tamper-evident rather than merely hashed.
    for pair in c3.revisions().windows(2) {
        assert_eq!(
            pair[1].parent,
            Some(pair[0].root),
            "revision {} must name revision {}'s root",
            pair[1].index,
            pair[0].index
        );
    }

    // Round-trips through the canonical text.
    let reparsed = Chain::parse(&c3.render(), EPOCH).expect("renders and parses");
    assert_eq!(reparsed, c3);
}

#[test]
fn identical_content_produces_identical_roots_and_different_content_does_not() {
    let a = Chain::genesis(EPOCH, content_digest(b"same"));
    let b = Chain::genesis(EPOCH, content_digest(b"same"));
    assert_eq!(
        a.head().root,
        b.head().root,
        "roots are a function of inputs"
    );

    let c = Chain::genesis(EPOCH, content_digest(b"different"));
    assert_ne!(a.head().root, c.head().root);

    // The epoch participates, so the same manifest under a different pin is a
    // different revision identity rather than a collision.
    let d = Chain::genesis("v4.33.0", content_digest(b"same"));
    assert_ne!(a.head().root, d.head().root, "the epoch tag must bind");
}

#[test]
fn parsing_is_total_on_hostile_input() {
    // Every one of these must yield a typed error, never a panic.
    for (text, what) in [
        ("", "empty"),
        ("garbage", "no schema"),
        ("schema fln-epoch-revisions/99\n", "wrong schema version"),
        ("schema fln-epoch-revisions/1\n", "no epoch, no revisions"),
        (
            "schema fln-epoch-revisions/1\nepoch v4.32.0\n",
            "no revisions",
        ),
        (
            "schema fln-epoch-revisions/1\nepoch v4.32.0\nrevision\n",
            "revision with no fields",
        ),
        (
            "schema fln-epoch-revisions/1\nepoch v4.32.0\nrevision x parent=genesis content=aa root=bb\n",
            "non-numeric index and short digests",
        ),
        (
            "schema fln-epoch-revisions/1\nepoch v4.32.0\nrevision 1 parent=genesis content=zz root=zz\n",
            "non-hex digests",
        ),
    ] {
        let got = Chain::parse(text, EPOCH);
        assert!(got.is_err(), "{what}: expected a typed error, got {got:?}");
    }
}

// ---------------------------------------------------------------------------
// Publication, and its failure atomicity
// ---------------------------------------------------------------------------

#[test]
fn publication_is_idempotent_and_appends_only_when_content_changes() {
    let dir = lab("publish");
    write_manifest(&dir, "first\n");

    let r1 = publish(&dir, EPOCH, MANIFEST).expect("genesis publishes");
    assert_eq!(r1.index, 1);
    assert!(!r1.already_current);

    // Same manifest: nothing is appended. A revision per invocation would make
    // the chain a log of runs rather than of content.
    let again = publish(&dir, EPOCH, MANIFEST).expect("republish");
    assert!(again.already_current, "unchanged content must not append");
    assert_eq!(again.index, 1);

    write_manifest(&dir, "second\n");
    let r2 = publish(&dir, EPOCH, MANIFEST).expect("append");
    assert_eq!(r2.index, 2);
    assert_ne!(r2.root, r1.root);

    let chain = verify_epoch(&dir, EPOCH, MANIFEST).expect("verifies");
    assert_eq!(chain.revisions().len(), 2);
}

/// MUTATION — PARTIAL EPOCH PUBLICATION.
///
/// A leftover candidate means a previous publication was interrupted. The prior
/// revision must remain authoritative, and the candidate must be refused by
/// name rather than consumed: whatever is in it was never verified, and reading
/// it would be exactly the "half-published identity that looks complete"
/// failure the append-only model exists to prevent.
#[test]
fn a_leftover_candidate_is_refused_and_the_prior_revision_stays_authoritative() {
    let dir = lab("partial");
    write_manifest(&dir, "authoritative\n");
    let good = publish(&dir, EPOCH, MANIFEST).expect("genesis");

    // Simulate an interrupted run: a candidate exists, and it is plausible —
    // well-formed for a DIFFERENT manifest, which is the dangerous case.
    let hijack = Chain::genesis(EPOCH, content_digest(b"attacker\n"));
    std::fs::write(dir.join(CANDIDATE_FILE), hijack.render()).expect("plant candidate");

    let publish_err = publish(&dir, EPOCH, MANIFEST).unwrap_err();
    assert!(
        matches!(publish_err, ChainError::CandidatePresent { .. }),
        "publication must refuse while a candidate remains; got {publish_err:?}"
    );
    let verify_err = verify_epoch(&dir, EPOCH, MANIFEST).unwrap_err();
    assert!(
        matches!(verify_err, ChainError::CandidatePresent { .. }),
        "verification must refuse too; got {verify_err:?}"
    );

    // And the authoritative file is untouched: the prior revision still stands.
    let text = std::fs::read_to_string(dir.join(CHAIN_FILE)).expect("chain still there");
    let chain = Chain::parse(&text, EPOCH).expect("prior chain intact");
    assert_eq!(chain.head().root.to_hex(), good.root);
    assert_eq!(chain.revisions().len(), 1);
}

/// MUTATION — MUTABLE REVISION.
///
/// The manifest is edited after publication. The chain is still perfectly
/// well-formed — every root recomputes, every parent links — and that is the
/// point: only binding the head to the manifest ON DISK catches it.
#[test]
fn editing_a_published_manifest_is_detected() {
    let dir = lab("mutable");
    write_manifest(&dir, "published\n");
    publish(&dir, EPOCH, MANIFEST).expect("genesis");
    assert!(verify_epoch(&dir, EPOCH, MANIFEST).is_ok());

    write_manifest(&dir, "published but edited\n");

    let err = verify_epoch(&dir, EPOCH, MANIFEST).unwrap_err();
    assert!(
        matches!(err, ChainError::ContentMismatch { .. }),
        "an edited published manifest must be a ContentMismatch, got {err:?}"
    );

    // The chain itself is still internally valid, which is exactly why the
    // content binding is load-bearing rather than redundant.
    let text = std::fs::read_to_string(dir.join(CHAIN_FILE)).expect("read");
    assert_eq!(Chain::parse(&text, EPOCH).expect("parses").verify(), Ok(()));
}

/// MUTATION — MUTABLE REVISION, the harder variant: rewrite HISTORY rather than
/// the manifest. An attacker who understands the format will also fix up the
/// root they edited. The parent linkage is what defeats that: correcting one
/// revision's root orphans every revision after it.
#[test]
fn rewriting_a_published_revision_is_detected_even_when_its_root_is_recomputed() {
    let dir = lab("rewrite");
    write_manifest(&dir, "one\n");
    publish(&dir, EPOCH, MANIFEST).expect("r1");
    write_manifest(&dir, "two\n");
    publish(&dir, EPOCH, MANIFEST).expect("r2");
    write_manifest(&dir, "three\n");
    publish(&dir, EPOCH, MANIFEST).expect("r3");

    let chain = verify_epoch(&dir, EPOCH, MANIFEST).expect("valid before tampering");
    assert_eq!(chain.revisions().len(), 3);

    // Rebuild history with revision 2's content replaced, recomputing roots
    // honestly — the forged chain is INTERNALLY consistent.
    let forged = Chain::genesis(EPOCH, chain.revisions()[0].content)
        .appended(content_digest(b"forged\n"))
        .appended(chain.revisions()[2].content);
    assert_eq!(forged.verify(), Ok(()), "the forgery is self-consistent");

    // It is nonetheless a different history: every root from the edit onward
    // differs, so the forgery cannot masquerade as the published chain.
    assert_ne!(forged.head().root, chain.head().root);
    assert_eq!(
        forged.revisions()[0].root,
        chain.revisions()[0].root,
        "the untouched prefix is unchanged"
    );
    assert_ne!(forged.revisions()[1].root, chain.revisions()[1].root);
}

/// MUTATION — ROOT MISMATCH.
///
/// A recorded root that is not the recomputed one, at each position in the
/// chain, must be refused with the offending index named.
#[test]
fn a_recorded_root_that_does_not_recompute_is_refused_at_its_own_index() {
    let base = Chain::genesis(EPOCH, content_digest(b"a"))
        .appended(content_digest(b"b"))
        .appended(content_digest(b"c"));
    assert_eq!(base.verify(), Ok(()));

    for victim in 1..=3u64 {
        // Corrupt exactly one recorded root and leave everything else alone.
        let text = base
            .render()
            .lines()
            .map(|l| {
                if l.starts_with(&format!("revision {victim} ")) {
                    let (head, _) = l.split_once(" root=").expect("root field");
                    format!("{head} root={}", "0".repeat(64))
                } else {
                    l.to_string()
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        let chain = Chain::parse(&text, EPOCH).expect("still parses");
        let err = chain.verify().unwrap_err();
        // A corrupted root at position n is caught either as the mismatch
        // itself or, for n > 1, as the successor's broken parent link —
        // whichever comes first. Both are the tamper being detected; what must
        // never happen is Ok.
        assert!(
            matches!(
                err,
                ChainError::RootMismatch { index } | ChainError::ParentMismatch { index }
                    if index == victim || index == victim + 1
            ),
            "corrupting revision {victim}'s root must be refused at {victim} or {}, got {err:?}",
            victim + 1
        );
    }
}

/// A chain whose epoch does not match the directory it was found in is refused.
/// Without this, a revision chain could be moved between epoch labs and still
/// verify, which would let one pin's history vouch for another's.
#[test]
fn a_chain_from_another_epoch_is_refused() {
    let chain = Chain::genesis("v4.33.0", content_digest(b"x"));
    let err = Chain::parse(&chain.render(), EPOCH).unwrap_err();
    assert!(
        matches!(err, ChainError::BadEpoch { .. }),
        "a foreign epoch must be refused, got {err:?}"
    );
}

/// The REAL lab: whatever is published under `tribunal/epochs/v4.32.0` must
/// verify. A typed skip if the chain has not been published yet, never a silent
/// pass.
#[test]
fn the_real_v4_32_0_epoch_lab_verifies() {
    let dir = fln_conformance::checked_manifest_dir!().join("../epochs/v4.32.0");
    if !dir.join(CHAIN_FILE).exists() {
        eprintln!("SKIP (typed limitation): {EPOCH} chain not published yet");
        return;
    }
    let chain = verify_epoch(&dir, EPOCH, MANIFEST).expect("the published lab must verify");
    println!(
        "epoch-lab {EPOCH}: {} revision(s), head root {}",
        chain.revisions().len(),
        chain.head().root.to_hex()
    );
}
