//! Suite `official_test_inventory_completeness` (bead `fln-4l15`; plan §18).
//!
//! The name is the one `fln-euo` enumerates in its closure criteria.
//!
//! # What is under test
//!
//! Not "we run some official tests". **"We can prove we know about every
//! official test at the pin, and for each one we either run it or name why
//! not."** The epic: "a small smoke slice demonstrates execution but cannot
//! substitute for inventory completeness." The epoch lab already carries such a
//! slice — the ten smallest upstream elab tests — and
//! `a_smoke_slice_is_not_coverage_and_says_so_per_test` is the test that stops
//! it being mistaken for coverage.
//!
//! # Completeness is enforced four ways
//!
//! Derived-not-hand-listed (a scan digest, recomputed); every entry disposed
//! (Run with an outcome, or NotRun with a typed reason AND an owning bead);
//! a test at the pin with no entry fails; and **count conservation** —
//! `discovered == run + not_run` — which is what makes a hidden exclusion
//! arithmetically impossible rather than merely discouraged.
//!
//! # Mutants planted and killed
//!
//! Measured results, not intended ones.
//!
//! | mutant | edit | killed by |
//! |---|---|---|
//! | incomplete C1 inventory | the `MissingFromInventory` loop is skipped | `a_test_at_the_pin_with_no_entry_fails_the_gate`, `a_smoke_slice_is_not_coverage_and_says_so_per_test`, `every_gap_is_reported_not_just_the_first` |
//! | hidden exclusion | `not_run` is only pushed for non-`BlockedOnBead` reasons | `every_exclusion_appears_in_the_report_with_its_reason`, `an_exclusion_that_is_not_surfaced_breaks_the_arithmetic` |
//! | unjustified exclusion admitted | the empty-bead check is dropped | `an_exclusion_without_an_owning_bead_fails` |
//! | filtered scan accepted | the scan digest is not recomputed | `a_scan_filtered_before_comparison_is_caught_as_not_bound`, `a_hand_listed_inventory_does_not_verify` |
//! | conservation not checked | `conserved()` returns `true` unconditionally | 4 tests, incl. `a_smoke_slice_is_not_coverage_and_says_so_per_test` |
//! | scan digest ignores test kind | the kind is dropped from the hash preimage | `the_scan_digest_is_order_independent_but_content_sensitive` |
//!
//! **One row was earned.** The first run showed that
//! `an_exclusion_that_is_not_surfaced_breaks_the_arithmetic` — the test named
//! for the hidden-exclusion mutant — did **not** kill it. It hand-constructed a
//! [`Completeness`] and checked the conservation law in isolation, which proves
//! the arithmetic but never exercises `verify`, so the verifier could drop an
//! exclusion and the test would still pass. It now drives the same scenario
//! through `verify` once per non-run reason, because the realistic mutant hides
//! exactly one reason: a filter that drops `BlockedOnBead` reads as deliberate
//! policy right up until that is the only thing being deferred.

#![forbid(unsafe_code)]

use fln_epoch_lab::corpus::{
    ALL_FAMILIES, Completeness, CorpusFamily, Disposition, Entry, ExpectedOutcome, Gap, Inventory,
    Justification, NonRunReason, OfficialTest, OfficialTestKind, PinScan, report, verify,
};

const PIN: &str = "leanprover/lean4:v4.32.0";

fn official(id: &str, kind: OfficialTestKind) -> OfficialTest {
    OfficialTest {
        id: id.to_string(),
        kind,
    }
}

/// A pin scan of fifty tests, which is what the inventory is measured against.
fn scan_of(n: usize) -> PinScan {
    PinScan {
        pin: PIN.to_string(),
        tests: (0..n)
            .map(|i| {
                official(
                    &format!("tests/lean/run/t{i:03}.lean"),
                    if i % 5 == 0 {
                        OfficialTestKind::ElabExpected
                    } else {
                        OfficialTestKind::ElabRun
                    },
                )
            })
            .collect(),
    }
}

fn run_entry(t: &OfficialTest) -> Entry {
    Entry {
        id: t.id.clone(),
        kind: t.kind,
        family: CorpusFamily::C1,
        disposition: Disposition::Run(ExpectedOutcome::Accepts),
    }
}

fn excluded_entry(t: &OfficialTest, reason: NonRunReason) -> Entry {
    Entry {
        id: t.id.clone(),
        kind: t.kind,
        family: CorpusFamily::C1,
        disposition: Disposition::NotRun {
            reason,
            justification: Justification {
                bead: "fln-4l15".to_string(),
                note: "deferred pending the elaborator".to_string(),
            },
        },
    }
}

/// A complete inventory: one entry per discovered test, bound to the scan.
fn complete_inventory(scan: &PinScan) -> Inventory {
    Inventory {
        pin: PIN.to_string(),
        scan_digest: scan.digest(),
        entries: scan.tests.iter().map(run_entry).collect(),
    }
}

fn reasons(c: &Completeness) -> Vec<&'static str> {
    c.gaps.iter().map(Gap::reason).collect()
}

// ---------------------------------------------------------------------------
// The baseline
// ---------------------------------------------------------------------------

#[test]
fn a_complete_inventory_verifies() {
    let scan = scan_of(50);
    let inv = complete_inventory(&scan);
    let c = verify(&inv, &scan);
    assert!(c.is_complete(), "a complete inventory was refused: {c:?}");
    assert!(c.conserved());
    assert_eq!(c.discovered, 50);
    assert_eq!(c.run, 50);
    assert!(report(&c).contains("verdict=complete"));
}

#[test]
fn a_complete_inventory_may_run_some_and_exclude_others() {
    // Completeness is not "run everything". It is "account for everything".
    let scan = scan_of(50);
    let mut entries: Vec<Entry> = scan.tests.iter().map(run_entry).collect();
    for e in entries.iter_mut().take(7) {
        let t = official(&e.id, e.kind);
        *e = excluded_entry(&t, NonRunReason::UnsupportedFeature);
    }
    let inv = Inventory {
        pin: PIN.to_string(),
        scan_digest: scan.digest(),
        entries,
    };
    let c = verify(&inv, &scan);
    assert!(c.is_complete(), "{c:?}");
    assert_eq!(c.run, 43);
    assert_eq!(c.not_run.len(), 7);
    assert!(c.conserved());
}

// ---------------------------------------------------------------------------
// The smoke slice is not coverage
// ---------------------------------------------------------------------------

#[test]
fn a_smoke_slice_is_not_coverage_and_says_so_per_test() {
    // THE CENTRAL CASE. The epoch lab carries ten upstream elab tests; the pin
    // has fifty. A rig that reports "10 tests pass" is telling the truth and
    // saying nothing. Forty individual gaps, one per unaccounted test — not one
    // aggregate gap, because a single "incomplete" line is exactly the kind of
    // summary that gets skimmed past.
    let scan = scan_of(50);
    let slice = Inventory {
        pin: PIN.to_string(),
        scan_digest: scan.digest(),
        entries: scan.tests.iter().take(10).map(run_entry).collect(),
    };
    let c = verify(&slice, &scan);
    assert!(
        !c.is_complete(),
        "a ten-of-fifty slice verified as complete"
    );
    let missing: Vec<&Gap> = c
        .gaps
        .iter()
        .filter(|g| matches!(g, Gap::MissingFromInventory { .. }))
        .collect();
    assert_eq!(missing.len(), 40, "gaps were summarised instead of listed");
    // And the accounting is honest about what it did check.
    assert_eq!(c.run, 10);
    assert_eq!(c.discovered, 50);
    assert!(!c.conserved(), "10 + 0 must not conserve against 50");
    assert!(report(&c).contains("verdict=incomplete"));
}

#[test]
fn a_test_at_the_pin_with_no_entry_fails_the_gate() {
    // The named mutant, minimal form: one test, one omission.
    let scan = scan_of(3);
    let inv = Inventory {
        pin: PIN.to_string(),
        scan_digest: scan.digest(),
        entries: scan.tests.iter().take(2).map(run_entry).collect(),
    };
    let c = verify(&inv, &scan);
    assert!(!c.is_complete());
    assert!(reasons(&c).contains(&"missing-from-inventory"));
    match c
        .gaps
        .iter()
        .find(|g| matches!(g, Gap::MissingFromInventory { .. }))
    {
        Some(Gap::MissingFromInventory { id }) => {
            assert_eq!(id, "tests/lean/run/t002.lean", "the wrong test was named")
        }
        other => panic!("expected MissingFromInventory, got {other:?}"),
    }
}

#[test]
fn an_entry_for_a_test_the_pin_does_not_have_fails_too() {
    // The other direction. A stale or invented entry means the inventory is not
    // describing this pin, and an inventory that describes a different pin is
    // not evidence about this one.
    let scan = scan_of(3);
    let mut inv = complete_inventory(&scan);
    inv.entries.push(run_entry(&official(
        "tests/lean/run/deleted_upstream.lean",
        OfficialTestKind::ElabRun,
    )));
    let c = verify(&inv, &scan);
    assert!(!c.is_complete());
    assert!(reasons(&c).contains(&"unknown-entry"));
}

// ---------------------------------------------------------------------------
// Hidden exclusions, and the arithmetic that forbids them
// ---------------------------------------------------------------------------

#[test]
fn an_exclusion_that_is_not_surfaced_breaks_the_arithmetic() {
    // THE HIDDEN-EXCLUSION MUTANT. The disguise is that the inventory looks
    // complete: every discovered test has an entry, nothing is missing, nothing
    // is unknown. The only thing wrong is that an exclusion was not accounted
    // for — and count conservation is what turns that from invisible into
    // arithmetic. discovered == run + not_run, or it blocks.
    let scan = scan_of(10);
    let inv = complete_inventory(&scan);
    let honest = verify(&inv, &scan);
    assert!(honest.conserved());

    // The law in isolation: an exclusion that never reaches the accounting
    // makes the sum wrong, whatever else looks right.
    let hidden = Completeness {
        discovered: honest.discovered,
        run: honest.run - 1,
        not_run: vec![], // the exclusion was dropped here
        gaps: vec![],
    };
    assert!(
        !hidden.conserved(),
        "a dropped exclusion did not break conservation"
    );
    assert!(!hidden.is_complete());

    // And the same thing THROUGH `verify`, which is the half that actually
    // kills the mutant. Checking the law on a hand-built value proves the
    // arithmetic; it does not prove the verifier upholds it, and the first
    // version of this test only did the former — so the test named for the
    // hidden-exclusion mutant did not kill the hidden-exclusion mutant.
    //
    // Every reason gets its own row, because the mutant that hides ONE reason
    // is the realistic one: a filter that drops `BlockedOnBead` looks like
    // deliberate policy right up until it is the only thing being deferred.
    for reason in [
        NonRunReason::UnsupportedFeature,
        NonRunReason::UnsupportedPlatform,
        NonRunReason::RequiresNetwork,
        NonRunReason::RequiresExternalTool,
        NonRunReason::OracleHarnessOnly,
        NonRunReason::BlockedOnBead,
    ] {
        let mut inv = complete_inventory(&scan);
        inv.entries[3] = excluded_entry(&scan.tests[3], reason);
        let c = verify(&inv, &scan);
        assert!(
            c.conserved(),
            "verify lost the {} exclusion from its accounting",
            reason.as_str()
        );
        assert_eq!(
            c.not_run.len(),
            1,
            "the {} exclusion was not surfaced by verify",
            reason.as_str()
        );
        assert_eq!(c.run, 9);
        assert!(c.is_complete(), "{c:?}");
    }
}

#[test]
fn every_exclusion_appears_in_the_report_with_its_reason() {
    // The accounting is not a courtesy. If an exclusion is not printed, nobody
    // can review it, and an exclusion nobody reviews is a silent narrowing of
    // the corpus.
    let scan = scan_of(6);
    let reasons_used = [
        NonRunReason::UnsupportedFeature,
        NonRunReason::UnsupportedPlatform,
        NonRunReason::RequiresNetwork,
        NonRunReason::RequiresExternalTool,
        NonRunReason::OracleHarnessOnly,
        NonRunReason::BlockedOnBead,
    ];
    let entries: Vec<Entry> = scan
        .tests
        .iter()
        .zip(reasons_used)
        .map(|(t, r)| excluded_entry(t, r))
        .collect();
    let inv = Inventory {
        pin: PIN.to_string(),
        scan_digest: scan.digest(),
        entries,
    };
    let c = verify(&inv, &scan);
    assert!(
        c.is_complete(),
        "a fully-excluded inventory is still complete: {c:?}"
    );
    assert_eq!(c.not_run.len(), 6);
    let text = report(&c);
    for (id, reason) in &c.not_run {
        assert!(text.contains(id.as_str()), "{id} was not reported");
        assert!(
            text.contains(reason.as_str()),
            "{} was not reported for {id}",
            reason.as_str()
        );
    }
    // Every reason variant is exercised, so none of them can be the one that
    // quietly fails to surface.
    for r in reasons_used {
        assert!(text.contains(r.as_str()), "{} never appeared", r.as_str());
    }
}

#[test]
fn an_exclusion_without_an_owning_bead_fails() {
    // "Explicit exclusion mapping" means somebody's name is on it. An exclusion
    // that cannot name an owner is a decision nobody made.
    let scan = scan_of(2);
    for (bead, note, missing) in [("", "a note", "bead"), ("fln-4l15", "   ", "note")] {
        let mut inv = complete_inventory(&scan);
        inv.entries[0].disposition = Disposition::NotRun {
            reason: NonRunReason::BlockedOnBead,
            justification: Justification {
                bead: bead.to_string(),
                note: note.to_string(),
            },
        };
        let c = verify(&inv, &scan);
        assert!(
            !c.is_complete(),
            "an exclusion missing its {missing} passed"
        );
        let found = c
            .gaps
            .iter()
            .any(|g| matches!(g, Gap::UnjustifiedExclusion { missing: m, .. } if *m == missing));
        assert!(
            found,
            "expected UnjustifiedExclusion({missing}): {:?}",
            c.gaps
        );
    }
}

// ---------------------------------------------------------------------------
// Derived, never hand-listed
// ---------------------------------------------------------------------------

#[test]
fn a_scan_filtered_before_comparison_is_caught_as_not_bound() {
    // THE FILTERED-SCAN MUTANT, and the subtlest disguise of all. Drop tests
    // from the SCAN rather than the inventory and every other check passes:
    // nothing is missing, nothing is unknown, the counts conserve. The only
    // thing that notices is that the inventory was derived from a different
    // scan than the one it is being verified against.
    let full = scan_of(50);
    let inv = complete_inventory(&full);

    let filtered = PinScan {
        pin: PIN.to_string(),
        tests: full.tests.iter().take(10).cloned().collect(),
    };
    let c = verify(&inv, &filtered);
    assert!(!c.is_complete(), "a filtered scan was accepted");
    assert!(reasons(&c).contains(&"scan-not-bound"));
}

#[test]
fn a_hand_listed_inventory_does_not_verify() {
    // An inventory nobody derived has no digest to state. Whatever it puts
    // there will not be the scan's.
    let scan = scan_of(4);
    let hand = Inventory {
        pin: PIN.to_string(),
        scan_digest: "0".repeat(64),
        entries: scan.tests.iter().map(run_entry).collect(),
    };
    let c = verify(&hand, &scan);
    assert!(!c.is_complete());
    assert!(reasons(&c).contains(&"scan-not-bound"));
}

#[test]
fn the_scan_digest_is_order_independent_but_content_sensitive() {
    // Order independence: a filesystem walk under a different locale must not
    // change the digest, or every lab would look stale on a different host.
    let a = scan_of(20);
    let mut shuffled = a.clone();
    shuffled.tests.reverse();
    assert_eq!(a.digest(), shuffled.digest(), "the digest depends on order");

    // Content sensitivity: adding, removing, or reclassifying a test must move
    // it, or the binding is decorative.
    let mut added = a.clone();
    added.tests.push(official(
        "tests/lean/run/new.lean",
        OfficialTestKind::ElabRun,
    ));
    assert_ne!(a.digest(), added.digest(), "adding a test did not move it");

    let mut reclassified = a.clone();
    reclassified.tests[0].kind = OfficialTestKind::Compiler;
    assert_ne!(
        a.digest(),
        reclassified.digest(),
        "reclassifying a test did not move it"
    );

    let mut different_pin = a.clone();
    different_pin.pin = "leanprover/lean4:v4.33.0".to_string();
    assert_ne!(a.digest(), different_pin.digest(), "the pin is not bound");
}

#[test]
fn an_inventory_for_a_different_pin_fails() {
    let scan = scan_of(3);
    let mut inv = complete_inventory(&scan);
    inv.pin = "leanprover/lean4:v4.31.0".to_string();
    let c = verify(&inv, &scan);
    assert!(!c.is_complete());
    assert!(reasons(&c).contains(&"pin-mismatch"));
}

// ---------------------------------------------------------------------------
// Schema totality
// ---------------------------------------------------------------------------

#[test]
fn the_ten_families_are_the_plans_ten_and_carry_the_plans_scopes() {
    // The families are from plan §18, not invented here, and each keeps the
    // plan's own wording so one cannot be quietly repurposed to mean whatever a
    // later corpus needs.
    assert_eq!(ALL_FAMILIES.len(), 10);
    assert_eq!(
        CorpusFamily::C0.scope(),
        "micro-fixtures isolating single rules"
    );
    assert!(
        CorpusFamily::C1
            .scope()
            .contains("official source-derived tests")
    );
    assert!(CorpusFamily::C3.scope().contains("artifact archaeology"));
    assert!(CorpusFamily::C7.scope().contains("adversarial"));
    assert!(CorpusFamily::C9.scope().contains("reproducibility"));
    // No two families share a scope, which would mean one is redundant.
    let mut scopes: Vec<&str> = ALL_FAMILIES.iter().map(|f| f.scope()).collect();
    scopes.sort_unstable();
    scopes.dedup();
    assert_eq!(scopes.len(), 10);
}

#[test]
fn a_c1_inventory_refuses_an_entry_filed_under_another_family() {
    // The C1 inventory is C1. An entry filed under C7 is either misclassified
    // or an attempt to make an adversarial fixture count as official-test
    // coverage; both block.
    let scan = scan_of(3);
    let mut inv = complete_inventory(&scan);
    inv.entries[1].family = CorpusFamily::C7;
    let c = verify(&inv, &scan);
    assert!(!c.is_complete());
    assert!(reasons(&c).contains(&"wrong-family"));
}

#[test]
fn a_duplicate_entry_fails() {
    let scan = scan_of(3);
    let mut inv = complete_inventory(&scan);
    inv.entries.push(inv.entries[0].clone());
    let c = verify(&inv, &scan);
    assert!(!c.is_complete());
    assert!(reasons(&c).contains(&"duplicate-entry"));
    // The duplicate also breaks conservation: 3 discovered, 4 run.
    assert!(!c.conserved());
}

#[test]
fn an_expected_outcome_of_rejects_carries_the_diagnostic() {
    // "Rejects" alone would let us reject for the wrong reason and call it
    // parity — the same failure the kernel differential guards against.
    let scan = scan_of(1);
    let mut inv = complete_inventory(&scan);
    inv.entries[0].disposition = Disposition::Run(ExpectedOutcome::Rejects {
        diagnostic: "error: type mismatch".to_string(),
    });
    let c = verify(&inv, &scan);
    assert!(c.is_complete(), "{c:?}");
    match &inv.entries[0].disposition {
        Disposition::Run(ExpectedOutcome::Rejects { diagnostic }) => {
            assert!(!diagnostic.is_empty())
        }
        other => panic!("unexpected disposition {other:?}"),
    }
}

#[test]
fn an_empty_pin_scan_is_not_a_free_pass() {
    // A scan that found nothing is vacuously covered by an empty inventory.
    // That is arithmetically true and worth pinning, because it means the
    // scan's own completeness — that it actually looked — is a property this
    // layer does NOT establish and the extraction slice must.
    let empty = PinScan {
        pin: PIN.to_string(),
        tests: vec![],
    };
    let inv = Inventory {
        pin: PIN.to_string(),
        scan_digest: empty.digest(),
        entries: vec![],
    };
    let c = verify(&inv, &empty);
    assert!(c.is_complete());
    assert_eq!(c.discovered, 0);
    // ...and an empty scan does not match a real one, so the emptiness cannot
    // be smuggled in against a pin that does have tests.
    assert_ne!(empty.digest(), scan_of(50).digest());
}

#[test]
fn every_gap_is_reported_not_just_the_first() {
    let scan = scan_of(10);
    let mut inv = Inventory {
        pin: "wrong-pin".to_string(),
        scan_digest: "f".repeat(64),
        entries: scan.tests.iter().take(4).map(run_entry).collect(),
    };
    inv.entries[0].family = CorpusFamily::C2;
    inv.entries[1].disposition = Disposition::NotRun {
        reason: NonRunReason::BlockedOnBead,
        justification: Justification {
            bead: String::new(),
            note: String::new(),
        },
    };
    let c = verify(&inv, &scan);
    let r = reasons(&c);
    for want in [
        "pin-mismatch",
        "scan-not-bound",
        "wrong-family",
        "unjustified-exclusion",
        "missing-from-inventory",
        "count-not-conserved",
    ] {
        assert!(r.contains(&want), "{want} was not reported: {:?}", c.gaps);
    }
}
