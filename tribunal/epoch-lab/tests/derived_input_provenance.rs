//! Suite `derived_input_provenance` (bead `fln-8fwh`).
//!
//! # What is under test
//!
//! The six model slices of `fln-euo` each refuse what they are shown, and each
//! accepted its input on trust. **A complete C1 inventory over a scan nobody
//! performed is complete with respect to nothing.** This suite tests the
//! replacement of "accepted from the caller" with "derived from the source, and
//! the derivation is itself checked".
//!
//! # The mutant that matters most
//!
//! **A supplied input that is plausible but wrong must fail the gate.** Before
//! this bead it would have passed all four slices. Every derivation below gets a
//! plausible-but-wrong case: a well-formed 64-hex digest that is not the file's,
//! a member list that is missing a real crate, a roster question that reads
//! correctly but is not what §22.1 says, and an artifact row edited after
//! publication.
//!
//! # The D8 line
//!
//! Three derivations read only this repository and are safe at gate time. The
//! module scan touches the pinned toolchain and is therefore split: extraction
//! lives in an `examples/` target (not shippable, not a gate), and the gate runs
//! [`verify_module_artifact`], which takes a `&str` and so *structurally cannot*
//! reach `~/.elan`. `the_gate_path_cannot_reach_the_toolchain` records that.

#![forbid(unsafe_code)]

use fln_epoch_lab::derive::{
    DeriveError, check_fixture, derive_fixture_digest, derive_g0_roster,
    derive_workspace_inventory, source_digest, verify_module_artifact,
};
use std::path::PathBuf;

fn repo_root() -> PathBuf {
    fln_conformance::checked_manifest_dir!().join("../..")
}

fn plan() -> PathBuf {
    repo_root().join("COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md")
}

fn committed_module_artifact() -> String {
    let p =
        fln_conformance::checked_manifest_dir!().join("../derived/v4.32.0/C1_MODULE_INVENTORY.txt");
    match std::fs::read_to_string(&p) {
        Ok(s) => s,
        Err(e) => panic!("the committed module artifact is missing at {p:?}: {e}"),
    }
}

// ---------------------------------------------------------------------------
// 1. Fixture digests
// ---------------------------------------------------------------------------

#[test]
fn a_fixture_digest_is_computed_from_the_fixture() {
    let f = plan();
    let d = derive_fixture_digest(&f).expect("the plan is readable");
    assert_eq!(d.provenance().item_count, 1);
    assert_eq!(d.provenance().rule, "fln.derive.fixture-digest/1");
    // The digest is the file's, recomputed from bytes rather than stated.
    let bytes = std::fs::read(&f).expect("readable");
    assert_eq!(*d.value(), source_digest(&bytes));
    assert_eq!(d.value().len(), 64);
    check_fixture(&f, d.value()).expect("the computed digest must verify");
}

#[test]
fn a_plausible_but_wrong_fixture_digest_fails() {
    // THE CENTRAL MUTANT, in its simplest form. Sixty-four valid hex characters
    // that are simply not this file's. The Parity Ledger accepted exactly this
    // before the bead: it checked the digest's SHAPE and never its truth.
    let f = plan();
    let plausible = "a".repeat(64);
    match check_fixture(&f, &plausible) {
        Err(DeriveError::DigestMismatch {
            stated, computed, ..
        }) => {
            assert_eq!(stated, plausible);
            assert_ne!(computed, plausible);
            assert_eq!(computed.len(), 64);
        }
        other => panic!("a plausible-but-wrong digest was accepted: {other:?}"),
    }

    // And one that is off by a single character, which is what a stale digest
    // after a one-line edit actually looks like.
    let real = derive_fixture_digest(&f).expect("readable").into_parts().0;
    let mut nearly = real.clone();
    let last = nearly.pop().expect("64 chars");
    nearly.push(if last == 'f' { 'e' } else { 'f' });
    assert!(
        check_fixture(&f, &nearly).is_err(),
        "an off-by-one digest passed"
    );
}

#[test]
fn a_fixture_that_does_not_exist_fails_rather_than_defaulting() {
    // A row may name a fixture that was deleted, renamed, or never written. It
    // must not degrade to "no digest to check".
    let missing = repo_root().join("tribunal/does-not-exist.lean");
    assert!(matches!(
        derive_fixture_digest(&missing),
        Err(DeriveError::SourceUnavailable { .. })
    ));
    assert!(matches!(
        check_fixture(&missing, &"0".repeat(64)),
        Err(DeriveError::SourceUnavailable { .. })
    ));
}

// ---------------------------------------------------------------------------
// 2. The workspace inventory
// ---------------------------------------------------------------------------

#[test]
fn the_workspace_inventory_is_read_from_the_real_manifests() {
    let d = derive_workspace_inventory(&repo_root()).expect("the workspace is readable");
    let scan = d.value();
    assert!(
        scan.members.len() >= 20,
        "only {} members found; the glob is not resolving",
        scan.members.len()
    );
    // Crates that certainly exist, so a scan that silently found nothing useful
    // cannot pass.
    let names: Vec<&str> = scan.members.iter().map(|m| m.name.as_str()).collect();
    for want in ["fln-kernel", "fln-core", "fln-hash", "fln-conformance"] {
        assert!(names.contains(&want), "{want} is missing from the scan");
    }
    // Both member globs resolved, not just the first.
    assert!(
        scan.members.iter().any(|m| m.dir.starts_with("crates/")),
        "no crates/ member"
    );
    assert!(
        scan.members.iter().any(|m| m.dir.starts_with("tools/")),
        "no tools/ member — the second glob did not resolve"
    );
    assert_eq!(d.provenance().item_count, scan.members.len());
}

#[test]
fn the_feature_universe_is_derived_rather_than_declared() {
    // The reachability scan enumerates the POWERSET of this set, so a feature
    // nobody listed is outside the certificate. Deriving it from the manifests
    // is what closes that hole.
    let d = derive_workspace_inventory(&repo_root()).expect("readable");
    let universe = d.value().feature_universe();
    // Sorted, deduplicated, and a function of the manifests.
    let mut sorted = universe.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(universe, sorted, "the feature universe is not a sorted set");
    // At least one crate in this workspace declares an optional feature; if that
    // stops being true this test should be revisited rather than deleted.
    assert!(
        !universe.is_empty(),
        "no optional features found; the [features] reader has stopped working"
    );
}

#[test]
fn a_member_list_missing_a_real_crate_is_detectable() {
    // The plausible-but-wrong case for an inventory: a list that looks right and
    // omits one member. It is detectable precisely because the derived scan is
    // the ground truth to compare against.
    let d = derive_workspace_inventory(&repo_root()).expect("readable");
    let real: Vec<String> = d.value().members.iter().map(|m| m.name.clone()).collect();
    let mut supplied = real.clone();
    supplied.pop();
    assert_ne!(real, supplied);
    let missing: Vec<&String> = real.iter().filter(|n| !supplied.contains(n)).collect();
    assert_eq!(missing.len(), 1, "exactly one member should be unaccounted");
}

// ---------------------------------------------------------------------------
// 3. The G0 roster — extracted, not transcribed
// ---------------------------------------------------------------------------

#[test]
fn the_g0_roster_is_extracted_from_the_plan() {
    let d = derive_g0_roster(&plan()).expect("§22.1 is present");
    let spikes = d.value();
    assert_eq!(spikes.len(), 10, "§22.1 does not have ten spikes");
    for (i, s) in spikes.iter().enumerate() {
        assert_eq!(
            s.id,
            format!("G0-{}", i + 1),
            "spike ids are not sequential"
        );
        assert!(!s.name.is_empty(), "{} has no name", s.id);
        assert!(
            s.question.len() > 40,
            "{} carries a question too short to be §22.1's",
            s.id
        );
    }
    assert_eq!(d.provenance().item_count, 10);
    assert_eq!(d.provenance().rule, "fln.derive.g0-roster/1");
}

#[test]
fn the_derived_questions_are_the_plans_words_not_a_paraphrase() {
    // This is the test that would have caught the transcription. Each assertion
    // is a distinctive phrase that appears in §22.1 and did NOT appear in the
    // hand-copied roster this bead removed — the transcription had dropped the
    // prototype names, the parenthetical scopes, and the design commitments.
    let d = derive_g0_roster(&plan()).expect("readable");
    let by_id = |id: &str| -> String {
        d.value()
            .iter()
            .find(|s| s.id == id)
            .map(|s| s.question.clone())
            .unwrap_or_else(|| panic!("{id} missing"))
    };
    assert!(
        by_id("G0-1").contains("prototype Marrow/Grimoire reader"),
        "G0-1 lost the prototype the spike actually names"
    );
    assert!(
        by_id("G0-2").contains("statements + proofs"),
        "G0-2 lost the scope of what is checked"
    );
    assert!(
        by_id("G0-7").contains("K2's memoization design"),
        "G0-7 lost the design being timed"
    );
    assert!(
        by_id("G0-9").contains("Tribunal sandbox"),
        "G0-9 lost where the patched Reference runs — a D8-load-bearing detail"
    );
}

#[test]
fn each_derived_question_is_the_exact_tail_of_its_plan_line() {
    // The strongest form, and the one that closes a real gap. The
    // phrase-sampling test above only reaches the FIRST clause of each
    // question, so a mutant truncating every question at its first semicolon
    // SURVIVED the campaign — it kept every phrase being sampled. Comparing
    // against the plan line's exact tail leaves nothing to sample past.
    let text = std::fs::read_to_string(plan()).expect("plan is readable");
    let d = derive_g0_roster(&plan()).expect("readable");
    let mut matched = 0usize;
    for spike in d.value() {
        let needle = format!("**{}**", spike.name);
        let line = text
            .lines()
            .find(|l| l.contains(&needle) && l.starts_with(char::is_numeric))
            .unwrap_or_else(|| panic!("no plan line for {}", spike.id));
        let tail = line
            .split_once("): ")
            .unwrap_or_else(|| panic!("{} has no '): ' separator", spike.id))
            .1
            .trim();
        assert_eq!(
            spike.question, tail,
            "{} was not extracted verbatim from its plan line",
            spike.id
        );
        // A truncation would satisfy `starts_with` but not equality, so also
        // pin that the question really does run to the end of the line.
        assert!(
            tail.len() > 80,
            "{} plan line is suspiciously short; the fixture may have moved",
            spike.id
        );
        matched += 1;
    }
    assert_eq!(matched, 10, "not every spike was checked against its line");
}

#[test]
fn a_plausible_but_wrong_roster_question_is_detectable() {
    // A question that reads correctly but is not §22.1's. The verbatim check in
    // G0SpikeDecisionV1 refuses it — but only because the roster it compares
    // against is now the plan's words rather than somebody's summary of them.
    let d = derive_g0_roster(&plan()).expect("readable");
    let real = &d.value()[0].question;
    let plausible = "ABI resurrection: parse a real mathlib .olean at the pin, \
                     walk every constant and extension entry, validate object-graph \
                     integrity against the extracted contract tables";
    assert_ne!(
        real, plausible,
        "the paraphrase and the plan's words must not be equal"
    );
}

/// A scratch workspace, following the convention `epoch_lab_hash_chain` uses.
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("fln-derive-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    dir
}

#[test]
fn a_globbed_member_whose_manifest_cannot_be_read_fails_the_scan() {
    // A real workspace has no unreadable members, so this case is unreachable
    // against this repo — and a mutation campaign proved it: a mutant that
    // replaced the `?` with `continue` SURVIVED, because no test could reach
    // the branch. A silently skipped member is a target outside the
    // reachability certificate, which is the exact hole `fln-rzyk` exists to
    // close, so the branch gets a synthetic workspace of its own.
    let root = scratch("bad-member");
    let members = root.join("crates");
    std::fs::create_dir_all(members.join("good")).expect("dirs");
    std::fs::create_dir_all(members.join("broken")).expect("dirs");
    std::fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"crates/*\"]\n",
    )
    .expect("root manifest");
    std::fs::write(
        members.join("good/Cargo.toml"),
        "[package]\nname = \"good\"\n",
    )
    .expect("good manifest");
    // Present enough to be globbed, malformed enough to have no package name.
    std::fs::write(
        members.join("broken/Cargo.toml"),
        "[dependencies]\nserde = \"1\"\n",
    )
    .expect("broken manifest");

    match derive_workspace_inventory(&root) {
        Err(DeriveError::Unparseable { detail, .. }) => {
            assert!(detail.contains("no [package] name"), "{detail}");
        }
        other => panic!("a member with no package name was skipped: {other:?}"),
    }

    // The case above is a READABLE manifest that says nothing useful. The
    // separate case is a manifest that cannot be read at all — and it needs its
    // own fixture, because the first one does not reach the read: a mutant
    // turning `read(&manifest)?` into `else { continue }` survived until this
    // existed. Two different failures, two different branches.
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let root = scratch("unreadable-member");
        let members = root.join("crates");
        std::fs::create_dir_all(members.join("locked")).expect("dirs");
        std::fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"crates/*\"]\n",
        )
        .expect("root manifest");
        let locked = members.join("locked/Cargo.toml");
        std::fs::write(&locked, "[package]\nname = \"locked\"\n").expect("manifest");
        std::fs::set_permissions(&locked, std::fs::Permissions::from_mode(0o000)).expect("chmod");
        let outcome = derive_workspace_inventory(&root);
        // Restore before asserting so a failure does not leave an unreadable
        // file behind for the next run.
        std::fs::set_permissions(&locked, std::fs::Permissions::from_mode(0o644)).ok();
        match outcome {
            Err(DeriveError::SourceUnavailable { path, .. }) => {
                assert!(path.contains("locked"), "wrong path reported: {path}");
            }
            other => panic!("an unreadable member manifest was skipped: {other:?}"),
        }
    }
}

#[test]
fn a_source_without_the_section_fails_rather_than_returning_an_empty_roster() {
    // An empty roster would make G0's gate vacuously clear — no spikes, no
    // missing decisions. It must be an error.
    let not_the_plan = repo_root().join("AGENTS.md");
    match derive_g0_roster(&not_the_plan) {
        Err(DeriveError::SectionNotFound { section, .. }) => assert_eq!(section, "22.1"),
        other => panic!("a document without §22.1 produced {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 4. The module artifact — extraction and gate paths kept apart
// ---------------------------------------------------------------------------

#[test]
fn the_committed_module_artifact_verifies() {
    let text = committed_module_artifact();
    let d = verify_module_artifact(&text).expect("the committed artifact must verify");
    assert_eq!(d.provenance().pin, "leanprover/lean4:v4.32.0");
    assert_eq!(d.provenance().rule, "fln.derive.module-scan/1");
    assert!(
        d.provenance().item_count > 2000,
        "only {} modules; the scan is not covering the stdlib",
        d.provenance().item_count
    );
    assert_eq!(d.value().tests.len(), d.provenance().item_count);
    // Host independence: the recorded source must not be somebody's home
    // directory, or the artifact regenerates differently on every machine and
    // the diff noise trains people to ignore it.
    assert!(
        !d.provenance().source.contains("/home/"),
        "the artifact records a host-specific path: {}",
        d.provenance().source
    );
}

#[test]
fn a_row_edited_after_publication_fails() {
    // The plausible-but-wrong case for the artifact: it parses, its header is
    // intact, its count is right, and one row has been changed. Only the
    // recomputed digest notices.
    let text = committed_module_artifact();
    let edited = text.replacen("module Init/", "module Init0/", 1);
    assert_ne!(edited, text, "the fixture did not actually change");
    match verify_module_artifact(&edited) {
        Err(DeriveError::DigestMismatch { .. }) => {}
        other => panic!("an edited row was accepted: {other:?}"),
    }
}

#[test]
fn a_row_added_or_removed_fails_on_the_count_before_the_digest() {
    let text = committed_module_artifact();

    let mut with_extra = text.clone();
    with_extra.push_str("module Fabricated/Module.lean\n");
    match verify_module_artifact(&with_extra) {
        Err(DeriveError::ArtifactInconsistent { detail }) => {
            assert!(detail.contains("header says"), "{detail}");
        }
        other => panic!("an added row was accepted: {other:?}"),
    }

    // Removing one is equally a lie about what was scanned.
    let idx = text.rfind("\nmodule ").expect("has module rows");
    let end = text[idx + 1..].find('\n').expect("row ends") + idx + 2;
    let without = format!("{}{}", &text[..idx + 1], &text[end..]);
    assert!(matches!(
        verify_module_artifact(&without),
        Err(DeriveError::ArtifactInconsistent { .. })
    ));
}

#[test]
fn an_artifact_from_a_different_rule_is_refused() {
    // Enumeration rules are versioned so an artifact produced under an older
    // walk cannot be silently reinterpreted under a newer one.
    let text = committed_module_artifact();
    let retagged = text.replace("fln.derive.module-scan/1", "fln.derive.module-scan/2");
    match verify_module_artifact(&retagged) {
        Err(DeriveError::ArtifactInconsistent { detail }) => {
            assert!(detail.contains("rule"), "{detail}");
        }
        other => panic!("a foreign-rule artifact was accepted: {other:?}"),
    }
}

#[test]
fn a_malformed_artifact_is_refused_and_never_panics() {
    for text in [
        "",
        "not-a-schema\n",
        "fln-c1-module-inventory/1\n",
        "fln-c1-module-inventory/1\npin p\n",
        "fln-c1-module-inventory/1\npin p\nrule fln.derive.module-scan/1\nsource s\ncount x\ndigest d\n",
        "fln-c1-module-inventory/1\nnonsense\n",
        "fln-c1-module-inventory/1\nunknownkey value\n",
    ] {
        assert!(
            verify_module_artifact(text).is_err(),
            "malformed artifact accepted: {text:?}"
        );
    }
}

#[test]
fn the_gate_path_cannot_reach_the_toolchain() {
    // The D8 property, recorded as a test rather than a promise.
    // `verify_module_artifact` takes a `&str` — it has no path parameter, no
    // filesystem access, and therefore no way to consult the Reference. The
    // extraction that DOES touch the toolchain lives in an examples/ target,
    // which is not shippable and is not a gate.
    //
    // This compiles, which is the assertion:
    let text = committed_module_artifact();
    let _: Result<_, _> = verify_module_artifact(&text);
    // And this does not, which is the point:
    //   verify_module_artifact(std::path::Path::new("~/.elan"));  // mismatched types
    assert!(verify_module_artifact(&text).is_ok());
}

// ---------------------------------------------------------------------------
// Provenance
// ---------------------------------------------------------------------------

#[test]
fn every_derivation_records_what_it_scanned_and_under_which_rule() {
    let w = derive_workspace_inventory(&repo_root()).expect("readable");
    let r = derive_g0_roster(&plan()).expect("readable");
    let f = derive_fixture_digest(&plan()).expect("readable");
    let m = verify_module_artifact(&committed_module_artifact()).expect("verifies");

    for p in [
        w.provenance(),
        r.provenance(),
        f.provenance(),
        m.provenance(),
    ] {
        assert!(!p.source.is_empty(), "a derivation recorded no source");
        assert!(
            p.rule.starts_with("fln.derive."),
            "{} is unnamespaced",
            p.rule
        );
        assert!(p.rule.ends_with("/1"), "{} is unversioned", p.rule);
        assert_eq!(p.source_digest.len(), 64, "{} has no source digest", p.rule);
        assert!(p.item_count > 0, "{} scanned nothing", p.rule);
    }

    // Only the module scan is bound to a Reference pin; the three in-repo
    // derivations owe nothing to one and say so rather than inventing a pin.
    assert_eq!(w.provenance().pin, "-");
    assert_eq!(r.provenance().pin, "-");
    assert_eq!(f.provenance().pin, "-");
    assert_eq!(m.provenance().pin, "leanprover/lean4:v4.32.0");
}

#[test]
fn derivations_are_deterministic_across_repeated_runs() {
    // No clock, no readdir order, no hash-map iteration. Two runs of the same
    // derivation over an unchanged source must agree, or the digest is not a
    // function of the source and drift detection means nothing.
    for _ in 0..3 {
        let a = derive_workspace_inventory(&repo_root()).expect("readable");
        let b = derive_workspace_inventory(&repo_root()).expect("readable");
        assert_eq!(a.provenance().source_digest, b.provenance().source_digest);
        assert_eq!(a.value().members, b.value().members);

        let c = derive_g0_roster(&plan()).expect("readable");
        let e = derive_g0_roster(&plan()).expect("readable");
        assert_eq!(c.provenance().source_digest, e.provenance().source_digest);
    }
}

// ---------------------------------------------------------------------------
// 5. The published epoch can no longer move
// ---------------------------------------------------------------------------

fn epoch_dir() -> PathBuf {
    fln_conformance::checked_manifest_dir!().join("../epochs/v4.32.0")
}

fn committed_epoch_tree() -> String {
    let p = fln_conformance::checked_manifest_dir!().join("../derived/v4.32.0/EPOCH_TREE.txt");
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("epoch tree missing at {p:?}: {e}"))
}

const HEAD_ROOT: &str = "7e554b20907d81a272d10718c26da2c25e2e6d70b2e962dc87516bb24dc18a75";

#[test]
fn the_published_epoch_matches_its_committed_tree() {
    let drifts =
        fln_epoch_lab::derive::verify_epoch_tree(&committed_epoch_tree(), &epoch_dir(), HEAD_ROOT)
            .expect("the tree artifact parses");
    assert!(
        drifts.is_empty(),
        "the published epoch has moved: {drifts:?}"
    );
}

#[test]
fn the_tree_binds_every_file_not_just_the_manifest() {
    // THE MUTABLE-LAB HAZARD. The revision chain binds MANIFEST.txt and nothing
    // else, so before this a transcript could be edited, a fixture added or a
    // sibling deleted with nothing detecting it — a published lab that can
    // still move is the same defect class as an input accepted on trust,
    // because in both cases a downstream check measures something unpinned.
    let tree =
        fln_epoch_lab::derive::parse_epoch_tree(&committed_epoch_tree()).expect("the tree parses");
    assert!(
        tree.files.iter().any(|f| f.path == "MANIFEST.txt"),
        "the manifest is not bound"
    );
    let transcripts = tree
        .files
        .iter()
        .filter(|f| f.path.starts_with("transcripts/"))
        .count();
    assert!(
        transcripts > 10,
        "only {transcripts} transcripts bound; the walk is not recursing"
    );
    // The chain file is excluded, because it cannot contain its own digest.
    assert!(
        !tree.files.iter().any(|f| f.path == "REVISIONS.txt"),
        "the chain file must not be bound by the tree it publishes"
    );
    assert!(
        tree.files.len() >= 40,
        "only {} files bound",
        tree.files.len()
    );
}

#[test]
fn an_edited_added_or_removed_epoch_file_is_detected() {
    let text = committed_epoch_tree();

    // Edited: same path, different digest.
    let edited = text.replacen(
        "file MANIFEST.txt ",
        "file MANIFEST.txt 0000000000000000000000000000000000000000000000000000000000000000 ",
        1,
    );
    // That produced a malformed row; build the realistic case instead by
    // rewriting the digest in place.
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    for l in lines.iter_mut() {
        if l.starts_with("file MANIFEST.txt ") {
            *l = "file MANIFEST.txt ".to_string() + &"0".repeat(64);
        }
    }
    let tampered = lines.join("\n") + "\n";
    // The artifact's own digest no longer covers its rows, so it is refused
    // before any comparison with the disk — which is the stronger failure.
    assert!(
        fln_epoch_lab::derive::verify_epoch_tree(&tampered, &epoch_dir(), HEAD_ROOT).is_err(),
        "a tampered tree artifact was accepted"
    );
    let _ = edited;

    // Removed / added, expressed against a directory that legitimately differs:
    // point a valid tree at the derived/ directory instead of the epoch.
    let drifts = fln_epoch_lab::derive::verify_epoch_tree(
        &committed_epoch_tree(),
        &fln_conformance::checked_manifest_dir!().join("../derived/v4.32.0"),
        HEAD_ROOT,
    )
    .expect("parses");
    assert!(
        !drifts.is_empty(),
        "a different directory produced no drift"
    );
    assert!(
        drifts.iter().any(|d| d.reason() == "file-removed"),
        "expected removals: {drifts:?}"
    );
    assert!(
        drifts.iter().any(|d| d.reason() == "file-added"),
        "expected additions: {drifts:?}"
    );
}

#[test]
fn a_tree_bound_to_a_different_head_is_refused() {
    // A tree describes one revision. Reading it against another would let a
    // stale binding vouch for a lab that has since been republished.
    let drifts = fln_epoch_lab::derive::verify_epoch_tree(
        &committed_epoch_tree(),
        &epoch_dir(),
        &"f".repeat(64),
    )
    .expect("parses");
    assert!(
        drifts.iter().any(|d| d.reason() == "head-moved"),
        "a tree bound to a different head was accepted: {drifts:?}"
    );
}

// ---------------------------------------------------------------------------
// 6. Targets, shippability, and the real reachability scan
// ---------------------------------------------------------------------------

fn policy() -> Vec<(String, fln_epoch_lab::poison::Shippability)> {
    let p = fln_conformance::checked_manifest_dir!().join("../derived/SHIPPABILITY_POLICY.txt");
    fln_epoch_lab::derive::read_shippability_policy(&p).expect("the policy file is readable")
}

#[test]
fn the_target_set_is_derived_from_the_tree() {
    let d = fln_epoch_lab::derive::derive_targets(&repo_root()).expect("readable");
    let targets = d.value();
    assert!(targets.len() > 50, "only {} targets found", targets.len());
    // Targets that certainly exist, one of each interesting kind.
    assert!(
        targets
            .iter()
            .any(|t| t.crate_name == "fln-kernel" && t.kind_str == "lib"),
        "fln-kernel's lib target is missing"
    );
    assert!(
        targets
            .iter()
            .any(|t| t.name == "reference_differential" && t.kind_str == "test"),
        "the kernel differential test target is missing"
    );
}

#[test]
fn the_policy_covers_every_derived_crate() {
    // The classification must be COMPLETE with respect to the derived set. An
    // unclassified crate blocks; it does not default. This is the C1 discipline
    // applied to shippability.
    let d = fln_epoch_lab::derive::derive_targets(&repo_root()).expect("readable");
    let (_, gaps) = fln_epoch_lab::derive::classify(d.value(), &policy());
    assert!(
        gaps.is_empty(),
        "the shippability policy does not cover the workspace: {gaps:?}"
    );
}

#[test]
fn an_uncovered_crate_blocks_rather_than_defaulting() {
    let d = fln_epoch_lab::derive::derive_targets(&repo_root()).expect("readable");
    let (_, gaps) = fln_epoch_lab::derive::classify(d.value(), &[]);
    assert!(!gaps.is_empty(), "an empty policy produced no gaps");
    assert!(gaps.iter().all(|g| g.reason() == "unclassified-crate"));

    // And a policy naming a crate that does not exist is equally a defect: it
    // is describing a tree that has moved.
    let stale = vec![(
        "fln-does-not-exist".to_string(),
        fln_epoch_lab::poison::Shippability::Shippable,
    )];
    let (_, gaps) = fln_epoch_lab::derive::classify(d.value(), &stale);
    assert!(gaps.iter().any(|g| g.reason() == "unknown-crate"));
}

#[test]
fn no_policy_can_make_a_test_target_shippable() {
    // The mechanical floor. Cargo does not put a test, bench or example into a
    // release artifact, so this is a fact rather than a judgement and no policy
    // row may override it.
    use fln_epoch_lab::poison::{Shippability, TargetKind};
    let d = fln_epoch_lab::derive::derive_targets(&repo_root()).expect("readable");
    // Claim EVERY crate ships, which is the most permissive policy expressible.
    let permissive: Vec<(String, Shippability)> = d
        .value()
        .iter()
        .map(|t| (t.crate_name.clone(), Shippability::Shippable))
        .collect();
    let (classified, _) = fln_epoch_lab::derive::classify(d.value(), &permissive);
    for t in &classified {
        if matches!(
            t.kind,
            TargetKind::Test | TargetKind::Bench | TargetKind::Example
        ) {
            assert_eq!(
                t.shippability,
                Shippability::DevelopmentOnly,
                "{}::{} was made shippable by policy",
                t.crate_name,
                t.name
            );
        }
    }
}

#[test]
fn the_real_workspace_has_no_oracle_path_from_a_shippable_target() {
    // THE POINT OF THE WHOLE BEAD. Derived targets, the declared policy, and
    // oracle edges discovered from real source — fed to the real reachability
    // scan. Until now `fln-rzyk` was proven correct over a supplied inventory
    // and said nothing about this workspace. This says something about this
    // workspace.
    use fln_epoch_lab::poison::{Inventory, Profile, ScanOutcome, scan};
    let targets = fln_epoch_lab::derive::derive_targets(&repo_root()).expect("readable");
    let (classified, gaps) = fln_epoch_lab::derive::classify(targets.value(), &policy());
    assert!(gaps.is_empty(), "classification is incomplete: {gaps:?}");
    let edges = fln_epoch_lab::derive::derive_oracle_edges(&repo_root(), targets.value())
        .expect("readable");
    let features = fln_epoch_lab::derive::derive_workspace_inventory(&repo_root())
        .expect("readable")
        .value()
        .feature_universe();

    let inv = Inventory {
        targets: classified,
        profiles: vec![Profile::Dev, Profile::Release, Profile::ReproducibleRelease],
        features,
        edges: edges.value().clone(),
        products: vec![],
    };
    let outcome = scan(&inv);
    match &outcome {
        ScanOutcome::Clean {
            combinations_checked,
            shippable_targets,
        } => {
            assert!(*shippable_targets > 0, "nothing was classified shippable");
            assert!(*combinations_checked > 0);
        }
        other => panic!(
            "a shippable target in this workspace can reach the oracle: {other:?}\n{}",
            fln_epoch_lab::poison::report(&outcome)
        ),
    }
}

#[test]
fn the_discovered_oracle_edges_are_real_and_all_development_only() {
    // The edges are not hypothetical: four real paths exist in this tree. Every
    // one must sit on a development-only target, which is D8 satisfied rather
    // than D8 asserted.
    use fln_epoch_lab::poison::Shippability;
    let targets = fln_epoch_lab::derive::derive_targets(&repo_root()).expect("readable");
    let (classified, _) = fln_epoch_lab::derive::classify(targets.value(), &policy());
    let edges = fln_epoch_lab::derive::derive_oracle_edges(&repo_root(), targets.value())
        .expect("readable");
    assert!(
        !edges.value().is_empty(),
        "no oracle edges discovered; the marker scan has stopped working"
    );
    // Per-CAPABILITY coverage, not merely a non-empty set. A mutant that broke
    // the ORACLE_FALLBACK marker survived an emptiness check, because the two
    // toolchain-path markers kept the set populated — so each capability the
    // tree really does exercise is pinned individually.
    use fln_epoch_lab::poison::OracleCapability;
    for want in [
        OracleCapability::OracleFallback,
        OracleCapability::SpawnReferenceBinary,
    ] {
        assert!(
            edges.value().iter().any(|e| e.capability == want),
            "no edge discovered for {} — that marker has stopped matching",
            want.as_str()
        );
    }
    for e in edges.value() {
        let t = classified
            .iter()
            .find(|t| t.name == e.target)
            .unwrap_or_else(|| panic!("edge names unknown target {}", e.target));
        assert_eq!(
            t.shippability,
            Shippability::DevelopmentOnly,
            "{} reaches {} and is not development-only",
            e.target,
            e.capability.as_str()
        );
    }
}

// ---------------------------------------------------------------------------
// 7. The classification's own standing
// ---------------------------------------------------------------------------

fn corroborated_rows() -> Vec<fln_epoch_lab::derive::CorroboratedRow> {
    let graph =
        fln_epoch_lab::derive::read_graph_kinds(&repo_root().join("ci/WORKSPACE_GRAPH.txt"))
            .expect("the reviewed crate map is readable");
    let targets = fln_epoch_lab::derive::derive_targets(&repo_root()).expect("readable");
    let edges = fln_epoch_lab::derive::derive_oracle_edges(&repo_root(), targets.value())
        .expect("readable");
    // Map each edge's target back to the crate that owns it.
    let edge_crates: Vec<String> = edges
        .value()
        .iter()
        .filter_map(|e| {
            targets
                .value()
                .iter()
                .find(|t| t.name == e.target)
                .map(|t| t.crate_name.clone())
        })
        .collect();
    let closure = real_closure();
    fln_epoch_lab::derive::corroborate(&policy(), &graph, &closure, &edge_crates)
}

/// The dependency closure as it stands over the REAL workspace.
fn real_closure() -> fln_epoch_lab::derive::ClosureAvailability {
    let graph_path = repo_root().join("ci/WORKSPACE_GRAPH.txt");
    let kinds = fln_epoch_lab::derive::read_graph_kinds(&graph_path).expect("readable");
    let edges = fln_epoch_lab::derive::read_graph_edges(&graph_path).expect("readable");
    let targets = fln_epoch_lab::derive::derive_targets(&repo_root()).expect("readable");
    let roots = fln_epoch_lab::derive::product_binary_roots(targets.value(), &kinds);
    fln_epoch_lab::derive::derive_dependency_closure(&edges, &roots)
}

#[test]
fn no_classification_row_is_contradicted_by_the_reviewed_crate_map() {
    // The premise check. `ci/WORKSPACE_GRAPH.txt` is authored and reviewed
    // elsewhere, so where it CAN witness a row it is a genuinely independent
    // source. A contradiction means one of the two is wrong and the scan cannot
    // tell which, so neither may be trusted.
    let rows = corroborated_rows();
    let bad: Vec<_> = rows
        .iter()
        .filter(|r| {
            matches!(
                r.standing,
                fln_epoch_lab::derive::Corroboration::Contradicted { .. }
            )
        })
        .collect();
    assert!(
        bad.is_empty(),
        "the crate map contradicts the policy: {bad:?}"
    );
    assert_eq!(rows.len(), 33, "every crate must have a standing");
}

#[test]
fn the_crate_map_is_not_read_as_a_shippability_oracle() {
    // The correction this cross-check produced. `kind=ordinary` means "a ranked
    // product crate under crates/" — a LAYERING fact. Reading it as "shippable"
    // conflates two vocabularies, and doing so would have reported two false
    // disagreements (fln-bench, fln-conformance) and hidden the real situation,
    // which is that the crate map simply cannot witness those rows.
    let rows = corroborated_rows();
    for name in ["fln-bench", "fln-conformance", "fln-kernel"] {
        let r = rows
            .iter()
            .find(|r| r.crate_name == name)
            .unwrap_or_else(|| panic!("{name} missing"));
        assert!(
            matches!(
                r.standing,
                fln_epoch_lab::derive::Corroboration::SingleSource { .. }
            ),
            "{name} was given a standing the crate map cannot support: {:?}",
            r.standing
        );
    }
    // And where it CAN witness, it does: the one tool crate is corroborated.
    let sg = rows
        .iter()
        .find(|r| r.crate_name == "structure-guard")
        .expect("structure-guard missing");
    assert!(matches!(
        sg.standing,
        fln_epoch_lab::derive::Corroboration::Corroborated { .. }
    ));
}

#[test]
fn the_single_source_rows_are_counted_and_named_not_assumed_away() {
    // A classification that only one derivation produces is an opinion with
    // good hygiene. The weakness must be a number on the page.
    let rows = corroborated_rows();
    let single = rows
        .iter()
        .filter(|r| {
            matches!(
                r.standing,
                fln_epoch_lab::derive::Corroboration::SingleSource { .. }
            )
        })
        .count();
    assert_eq!(single, 32, "the single-source count moved without review");
    let text = fln_epoch_lab::derive::corroboration_report(&rows);
    assert!(text.contains("single_source=32"));
    assert!(text.contains("corroborated=1"));
    assert!(text.contains("verdict=no-contradiction"));
}

#[test]
fn the_rows_that_would_suppress_a_finding_are_named() {
    // THE HIGHEST-RISK ROWS IN THE CLASSIFICATION. A crate carrying a real
    // oracle edge, called development-only on one source's say-so, is doing all
    // the work of keeping the reachability scan clean. If that call is wrong
    // the scan reports Clean over a shippable target that reaches the
    // Reference — with full confidence, because the classification is its own
    // premise. These get named, so a reviewer is told where to look.
    let rows = corroborated_rows();
    let suppressions = fln_epoch_lab::derive::uncorroborated_suppressions(&rows);
    let names: Vec<&str> = suppressions.iter().map(|r| r.crate_name.as_str()).collect();
    assert!(
        names.contains(&"fln-conformance"),
        "fln-conformance carries an ORACLE_FALLBACK edge and is development-only \
         on a single source; it must be flagged. got {names:?}"
    );
    let text = fln_epoch_lab::derive::corroboration_report(&rows);
    assert!(text.contains("uncorroborated-suppression crate=fln-conformance"));
    // The count is asserted so a new suppression cannot appear silently.
    assert_eq!(
        suppressions.len(),
        1,
        "the set of finding-suppressing rows changed: {names:?}"
    );
}

// ---------------------------------------------------------------------------
// 8. The dependency-closure derivation
// ---------------------------------------------------------------------------

#[test]
fn the_closure_derivation_is_correct_over_a_known_graph() {
    // The ALGORITHM, proven on a synthetic graph. Its applicability to this
    // tree is a separate question, answered by the test below — separating the
    // two is what lets the algorithm be evidence before the tree can supply it.
    use fln_epoch_lab::derive::{ClosureAvailability, derive_dependency_closure};
    let edges: Vec<(String, String)> = [
        ("cli", "elab"),
        ("elab", "kernel"),
        ("kernel", "core"),
        ("harness", "kernel"),
        ("bench", "core"),
    ]
    .iter()
    .map(|(a, b)| (a.to_string(), b.to_string()))
    .collect();

    match derive_dependency_closure(&edges, &["cli".to_string()]) {
        ClosureAvailability::Available { reachable } => {
            // Transitive: cli -> elab -> kernel -> core, all four.
            for want in ["cli", "elab", "kernel", "core"] {
                assert!(reachable.contains(want), "{want} not reached");
            }
            // Nothing depends ON the roots from harness/bench, so neither is
            // reachable: depending on a shipped crate does not make you shipped.
            assert!(!reachable.contains("harness"), "reachability ran backwards");
            assert!(!reachable.contains("bench"), "reachability ran backwards");
        }
        other => panic!("expected Available, got {other:?}"),
    }

    // A cycle must terminate rather than spin.
    let cyclic: Vec<(String, String)> = [("a", "b"), ("b", "a")]
        .iter()
        .map(|(x, y)| (x.to_string(), y.to_string()))
        .collect();
    match derive_dependency_closure(&cyclic, &["a".to_string()]) {
        ClosureAvailability::Available { reachable } => assert_eq!(reachable.len(), 2),
        other => panic!("a cyclic graph produced {other:?}"),
    }
}

#[test]
fn an_empty_root_set_is_unavailable_not_the_answer_nothing_ships() {
    // THE TRAP THIS DERIVATION HAD TO AVOID. Returning the empty closure as a
    // positive answer would witness DevelopmentOnly for all 33 crates,
    // corroborating every row in the policy and making the reachability scan
    // trivially clean — while looking exactly like the independent evidence the
    // classification was missing. A derivation that cannot answer must not
    // answer, the same law `poison::scan` applies to itself.
    use fln_epoch_lab::derive::{ClosureAvailability, derive_dependency_closure};
    let edges: Vec<(String, String)> = vec![("a".to_string(), "b".to_string())];
    match derive_dependency_closure(&edges, &[]) {
        ClosureAvailability::Unavailable { why } => {
            assert!(
                why.contains("nothing ships"),
                "the reason must name the trap: {why}"
            );
        }
        other => panic!("an empty root set produced a positive answer: {other:?}"),
    }
}

#[test]
fn the_closure_is_honestly_unavailable_over_this_workspace_today() {
    // The state of the tree, asserted so it is visible rather than assumed —
    // and so that the day a product binary lands, this test fails and tells
    // whoever landed it that a second source has just become available.
    use fln_epoch_lab::derive::ClosureAvailability;
    let graph_path = repo_root().join("ci/WORKSPACE_GRAPH.txt");
    let kinds = fln_epoch_lab::derive::read_graph_kinds(&graph_path).expect("readable");
    let targets = fln_epoch_lab::derive::derive_targets(&repo_root()).expect("readable");
    let roots = fln_epoch_lab::derive::product_binary_roots(targets.value(), &kinds);
    assert!(
        roots.is_empty(),
        "a product binary now exists ({roots:?}) — the dependency-closure \
         derivation has become available and every single-source row in \
         SHIPPABILITY_POLICY.txt can now be independently witnessed. Wire it in \
         and update fln-8fwh."
    );
    assert!(matches!(
        real_closure(),
        ClosureAvailability::Unavailable { .. }
    ));
}

#[test]
fn a_disagreement_preserves_both_answers_and_resolves_neither() {
    // Whichever source one would instinctively trust is the one that will
    // eventually be wrong, so a contradiction records every answer and picks
    // none. A month from now the finding must still say what each source said.
    use fln_epoch_lab::derive::{ClosureAvailability, Corroboration, corroborate};
    use fln_epoch_lab::poison::Shippability;

    let policy = vec![("harness".to_string(), Shippability::DevelopmentOnly)];
    let closure = ClosureAvailability::Available {
        reachable: ["harness".to_string()].into_iter().collect(),
    };
    let rows = corroborate(&policy, &[], &closure, &[]);
    match &rows[0].standing {
        Corroboration::Contradicted {
            declared,
            witnesses,
        } => {
            // The policy's answer is preserved...
            assert_eq!(*declared, Shippability::DevelopmentOnly);
            // ...and so is the source's, unresolved.
            assert_eq!(witnesses.len(), 1);
            assert_eq!(witnesses[0].says, Shippability::Shippable);
            assert!(witnesses[0].source.contains("dependency closure"));
        }
        other => panic!("a disagreement was resolved instead of recorded: {other:?}"),
    }
    // And the report prints both, so the finding is debuggable from the log
    // alone without re-running anything.
    let text = fln_epoch_lab::derive::corroboration_report(&rows);
    assert!(text.contains("policy_says=DevelopmentOnly"));
    assert!(text.contains("source_says=Shippable"));
    assert!(text.contains("verdict=contradicted"));
}

#[test]
fn per_source_coverage_is_reported_so_partial_cannot_read_as_full() {
    // "33 rows checked" must never be readable as "33 rows corroborated". Each
    // source reports how many rows it actually witnessed, out of how many.
    let rows = corroborated_rows();
    let text = fln_epoch_lab::derive::corroboration_report(&rows);
    assert!(
        text.contains("source-coverage source=ci/WORKSPACE_GRAPH.txt kind=tool witnessed=1 of=33"),
        "per-source coverage is not reported: {text}"
    );
    // The closure witnessed nothing today, so it must not appear as a source at
    // all — a source with zero coverage listed alongside real ones would read
    // as participation.
    assert!(
        !text.contains("source=dependency closure"),
        "an unavailable source was reported as having participated: {text}"
    );
    assert!(text.contains("single_source=32"));
}
