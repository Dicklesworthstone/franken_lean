//! The 533-record oracle capture must still be what the pin produces (bead
//! `franken_lean-ext-observable-fixture-drift-gap-vqnu`).
//!
//! # The two-legged chain, and which leg was missing
//!
//! Twenty-eight rows in `ci/PARITY_LEDGER.txt` rest on
//! `crates/fln-core/fixtures/core_ext_observables.txt`, and the evidence they claim is a
//! chain with two joins:
//!
//! ```text
//!   the pinned binary  --(1)-->  the capture  --(2)-->  fln-core's implementation
//! ```
//!
//! Join (2) is checked on every run by `crates/fln-core/tests/pin_ext_observables.rs`.
//! Join (1) was checked by nothing. The capture is produced by
//! `crates/fln-core/fixtures/gen_core_ext.lean` run BY HAND — its own header documents the
//! command line — and the only standing guard was that the fixture's header names a commit
//! `SUITE.lock` pins, which is a string comparison the same edit could preserve.
//!
//! So the rows were not wrong; they were *unfalsifiable in one direction*. A stale capture,
//! a hand edit, or a partial regeneration would have left all 28 rows reporting L2 against
//! a file nobody re-derived, and nothing anywhere would have said so.
//!
//! # What this test adds, and what it deliberately does not duplicate
//!
//! This closes join (1) only: it re-runs the generator under the pinned binary and compares
//! byte-for-byte. It does **not** check that `fln-core` matches the capture — that is join
//! (2)'s job and it already has an owner. Two joins, two rigs, neither pretending to cover
//! the other.
//!
//! Measured 2026-07-25: the capture was byte-identical to a fresh re-derivation, and the
//! re-derivation costs ~1.6s. The rows were backed the whole time. The defect was that
//! nobody could have known that, and the price of knowing turns out to be a second and a
//! half — which is the argument this file exists to settle permanently.
//!
//! Without the pinned toolchain this is a typed SKIP that says what was not established.

#![forbid(unsafe_code)]

use std::process::Command;

use fln_conformance::pin;

const GENERATOR: &str = "crates/fln-core/fixtures/gen_core_ext.lean";
const CAPTURE: &str = "crates/fln-core/fixtures/core_ext_observables.txt";

/// The first place two texts differ, as a line number and both sides.
///
/// A bare "they differ" would leave whoever hits this to reconstruct the diff by hand, and
/// the most likely reading of an unexplained mismatch is "the fixture is fine, the test is
/// flaky" — which is how a real drift gets waved through.
fn first_difference(checked_in: &str, rederived: &str) -> Option<String> {
    let mut ours = checked_in.lines().enumerate();
    let mut theirs = rederived.lines();
    for (index, mine) in ours.by_ref() {
        match theirs.next() {
            Some(other) if other == mine => {}
            Some(other) => {
                return Some(format!(
                    "line {}:\n  checked-in: {mine}\n  pin now says: {other}",
                    index + 1
                ));
            }
            None => {
                return Some(format!(
                    "the checked-in capture has {} extra line(s); the first is line {}:\n  \
                     {mine}",
                    checked_in.lines().count() - rederived.lines().count(),
                    index + 1
                ));
            }
        }
    }
    theirs.next().map(|extra| {
        format!(
            "the pin now emits {} line(s) the capture does not have; the first is:\n  {extra}",
            rederived.lines().count() - checked_in.lines().count()
        )
    })
}

#[test]
fn the_checked_in_capture_is_what_the_pinned_binary_produces_today() {
    let root = pin::workspace_root();
    let checked_in = std::fs::read_to_string(root.join(CAPTURE)).expect("the capture exists");

    // Guard the guard: a truncated or emptied capture must not pass by having nothing to
    // disagree with. 533 records at v4.32.0; the floor catches collapse, not growth.
    assert!(
        checked_in.lines().count() > 400,
        "the capture is {} lines — far below the 533 it carried at v4.32.0. A comparison \
         against a collapsed fixture is vacuous, not clean.",
        checked_in.lines().count()
    );

    let Some(lean) = pin::pinned_lean() else {
        eprintln!("{}", pin::skip_notice("ext_observable_capture"));
        eprintln!(
            "  In particular: the 28 Parity Ledger rows citing {CAPTURE} are NOT shown to \
             rest on anything the pin produced by this run."
        );
        return;
    };

    let out = Command::new(&lean)
        .arg("--run")
        .arg(root.join(GENERATOR))
        .current_dir(&root)
        .output()
        .map_err(|error| format!("running {}: {error}", lean.display()))
        .expect("the located pinned binary is executable");
    let rederived = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(
        out.status.success(),
        "the pinned binary refused the generator (exit {:?}):\n{}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );

    let difference = first_difference(&checked_in, &rederived).unwrap_or_default();
    assert!(
        difference.is_empty(),
        "{CAPTURE} is NOT what the pin produces today.\n\n{difference}\n\nThis is the defect \
         bead franken_lean-ext-observable-fixture-drift-gap-vqnu exists for, and it is now \
         visible instead of silent. Twenty-eight Parity Ledger rows cite this file. Do NOT \
         regenerate it to make this pass without first establishing WHY it moved: if the pin \
         is unchanged, something edited the capture, and the rows have been reporting \
         evidence that was not re-derived. Regenerate with:\n  {} --run {GENERATOR} > \
         {CAPTURE}",
        lean.display()
    );

    // The header names a commit; the lock pins one. Both are now redundant with the
    // re-derivation above — kept because a mismatch here says something different (the
    // capture was made by another Reference entirely) and its repair is different too.
    let commit = pin::pinned_commit().expect("SUITE.lock pins a reference commit");
    assert!(
        checked_in.contains(&commit),
        "the capture's header does not name the commit SUITE.lock pins ({commit})"
    );
}

/// The comparison must be shown to catch a moved record, or a green run means only that
/// the two files were read.
///
/// This is the same discipline `scripts/e2e/core_observables.sh:74-98` applies to the
/// sibling fixture with a seeded corruption — the sibling has had it all along, which is
/// exactly why the asymmetry between the two fixtures was worth filing.
#[test]
fn the_comparison_catches_a_moved_record_a_dropped_one_and_an_added_one() {
    let original = "schema fln-core-ext-observables/1\nlevel|zero|0\nname|anonymous|1\n";

    assert_eq!(first_difference(original, original), None, "equal is equal");

    let moved = original.replace("level|zero|0", "level|zero|1");
    let found = first_difference(original, &moved).expect("a changed value must be reported");
    assert!(
        found.contains("line 2") && found.contains("checked-in") && found.contains("pin now says"),
        "the report must name the line and both sides: {found}"
    );

    let dropped = "schema fln-core-ext-observables/1\nlevel|zero|0\n";
    let found = first_difference(original, dropped).expect("a dropped record must be reported");
    assert!(found.contains("extra line"), "{found}");

    let added = format!("{original}extra|record|2\n");
    let found = first_difference(original, &added).expect("an added record must be reported");
    assert!(found.contains("the pin now emits"), "{found}");
}

/// A capture that has collapsed to its header would agree with a generator that emitted
/// nothing, so the floor above is load-bearing rather than decorative.
#[test]
fn a_collapsed_capture_is_not_silently_equal_to_a_collapsed_generator() {
    let header_only = "schema fln-core-ext-observables/1\n";
    assert_eq!(
        first_difference(header_only, header_only),
        None,
        "two empty captures ARE byte-equal — which is why the line-count floor, not this \
         comparison, is what refuses a collapsed fixture"
    );
}
