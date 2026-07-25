//! Suite `oracle_only_reachability` (bead `fln-rzyk`; plan §18, doctrine D8).
//!
//! The name is the one `fln-euo` enumerates in its closure criteria.
//!
//! # The failure under test
//!
//! **A release binary that quietly consults the Reference.** D8 says the
//! Reference appears in exactly one place — inside the Tribunal, as the
//! differential oracle — and that the development-only lockstep harness
//! "poisons everything it touches with `ORACLE_FALLBACK`, satisfies no gate,
//! and is compiled out of releases — with a CI check proving its absence".
//! This suite is that check's laws.
//!
//! # Exhaustive, not sampled
//!
//! The scan enumerates every shippable target × profile × **feature subset**.
//! A scan that misses one feature flag is worse than none, because it certifies
//! what it did not check — so the tests below verify the combination COUNT, not
//! merely that a leak was found, and verify that a space the scan could not
//! enumerate comes back Inconclusive rather than clean.
//!
//! # Both directions
//!
//! False positives are a failure mode too. Development-only Tribunal targets
//! MAY contain oracle machinery; a scan that flags them cries wolf, and a gate
//! that cries wolf gets routed around. Every leak test has a companion that
//! proves the legitimate case is left alone.
//!
//! # Mutants planted and killed
//!
//! The three the epic names, plus three the design invited. "Killed by" is the
//! measured result of running each mutant, not the test that was expected to
//! catch it.
//!
//! | mutant | edit | killed by |
//! |---|---|---|
//! | test-only oracle read as release-reachable | the shippable filter accepts every target | 8 tests, incl. `a_development_only_target_may_contain_the_oracle_machinery` |
//! | unpoisoned product admitted | the `OracleDerived ⇒ poisoned` check is skipped | `an_unpoisoned_oracle_derived_product_blocks`, `every_leak_is_reported_not_just_the_first` |
//! | oracle path under one non-default feature missed | the powerset walk is `.take(1)`, i.e. default features only | 8 tests, incl. `an_oracle_path_reachable_under_one_non_default_feature_is_caught` |
//! | poison does not propagate | `inherited` is hardcoded `false` | `poison_propagates_transitively_through_derivation` |
//! | budget overflow sampled instead of refused | the pre-walk budget check is disabled | `a_space_too_large_to_enumerate_is_inconclusive_not_clean` |
//! | conjunctive feature gate weakened to disjunctive | `requires.iter().all` becomes `any` | `a_path_requiring_two_features_is_caught_only_when_both_are_on` |
//!
//! **Two of these rows were earned rather than designed, and both are recorded
//! because the first attempt was wrong.**
//!
//! The budget mutant originally did not fail a test — it **hung**, attempting
//! 2⁴⁰ × 6 ≈ 3.3 × 10¹² iterations. A gate that hangs is caught by a CI timeout
//! rather than by a named test, which is a far weaker signal, so the scan now
//! carries a second in-loop guard and termination is structural.
//!
//! Adding that guard then made the budget mutant **survive**, because the
//! fallback produced the same outcome and the deleted check became
//! unobservable. So the two guards report different reasons —
//! `BudgetExceeded` for the honest pre-walk refusal, `EnumerationRunaway` for
//! "our size arithmetic was wrong" — and the test asserts the exact one. Two
//! redundant guards that are indistinguishable are one guard plus dead code
//! that no campaign can see.

#![forbid(unsafe_code)]

use fln_epoch_lab::poison::{
    ENUMERATION_BUDGET, Inventory, Leak, ORACLE_FALLBACK, OracleCapability, OracleEdge, Poisoned,
    Product, Profile, Provenance, ScanOutcome, Shippability, Target, TargetKind, derive_product,
    report, scan,
};
use std::collections::BTreeSet;

fn features(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|s| (*s).to_string()).collect()
}

fn target(name: &str, shippability: Shippability) -> Target {
    Target {
        crate_name: "fln-lake".to_string(),
        name: name.to_string(),
        kind: TargetKind::Bin,
        shippability,
    }
}

/// A clean inventory: two shippable targets, one development-only Tribunal
/// target that legitimately holds the lockstep harness, three profiles, two
/// optional features, no oracle edge from anything shippable.
fn clean_inventory() -> Inventory {
    Inventory {
        targets: vec![
            target("lean", Shippability::Shippable),
            target("lake", Shippability::Shippable),
            target("tribunal-lockstep", Shippability::DevelopmentOnly),
        ],
        profiles: vec![Profile::Dev, Profile::Release, Profile::ReproducibleRelease],
        features: vec!["frontier".to_string(), "olean-next".to_string()],
        edges: vec![
            // The harness IS allowed to reach the oracle. That is what it is for.
            OracleEdge {
                target: "tribunal-lockstep".to_string(),
                capability: OracleCapability::OracleFallback,
                requires: BTreeSet::new(),
            },
            OracleEdge {
                target: "tribunal-lockstep".to_string(),
                capability: OracleCapability::SpawnReferenceBinary,
                requires: BTreeSet::new(),
            },
        ],
        products: vec![
            Product {
                name: "fln-kernel.rlib".to_string(),
                provenance: Provenance::OwnWork,
                poisoned: false,
            },
            Product {
                name: "oracle-trace.jsonl".to_string(),
                provenance: Provenance::OracleDerived,
                poisoned: true,
            },
        ],
    }
}

fn leaks(outcome: &ScanOutcome) -> Vec<&'static str> {
    match outcome {
        ScanOutcome::Leaks(l) => l.iter().map(Leak::reason).collect(),
        _ => vec![],
    }
}

// ---------------------------------------------------------------------------
// The baseline, and the false-positive direction
// ---------------------------------------------------------------------------

#[test]
fn a_clean_workspace_clears_the_release() {
    // Without this every leak test below could be passing because the fixture
    // is broken rather than because the rule works.
    let outcome = scan(&clean_inventory());
    assert!(
        outcome.clears_release(),
        "a clean inventory was refused: {outcome:?}"
    );
    assert!(report(&outcome).contains("verdict=pass"));
}

#[test]
fn a_development_only_target_may_contain_the_oracle_machinery() {
    // THE FALSE-POSITIVE MUTANT, stated as a law. The lockstep harness is
    // supposed to reach the oracle; that is the one place D8 permits it. A scan
    // that flags it cries wolf, and a gate that cries wolf gets routed around
    // — the same failure mode as an oracle rig that manufactures divergences.
    let mut inv = clean_inventory();
    // Give it every capability there is, under no feature gate at all.
    inv.edges = vec![
        OracleCapability::SpawnReferenceBinary,
        OracleCapability::LinkReferenceSymbol,
        OracleCapability::ReadReferenceArtifact,
        OracleCapability::OracleFallback,
    ]
    .into_iter()
    .map(|capability| OracleEdge {
        target: "tribunal-lockstep".to_string(),
        capability,
        requires: BTreeSet::new(),
    })
    .collect();
    let outcome = scan(&inv);
    assert!(
        outcome.clears_release(),
        "a development-only target was flagged: {outcome:?}"
    );
}

// ---------------------------------------------------------------------------
// Reachability, exhaustively
// ---------------------------------------------------------------------------

#[test]
fn the_scan_visits_every_target_times_profile_times_feature_subset() {
    // The completeness claim, as a number. 2 shippable targets × 3 profiles ×
    // 2^2 feature subsets = 24. If the enumeration is ever narrowed — to
    // default features, to release-only, to one target — this is what says so.
    let outcome = scan(&clean_inventory());
    match outcome {
        ScanOutcome::Clean {
            combinations_checked,
            shippable_targets,
        } => {
            assert_eq!(shippable_targets, 2);
            assert_eq!(
                combinations_checked, 24,
                "the scan did not visit the whole space"
            );
        }
        other => panic!("expected Clean, got {other:?}"),
    }

    // And it scales with each dimension independently.
    let mut inv = clean_inventory();
    inv.features.push("iron-jit".to_string());
    match scan(&inv) {
        ScanOutcome::Clean {
            combinations_checked,
            ..
        } => assert_eq!(
            combinations_checked, 48,
            "the feature dimension did not double"
        ),
        other => panic!("expected Clean, got {other:?}"),
    }
}

#[test]
fn an_oracle_path_reachable_under_one_non_default_feature_is_caught() {
    // THE SAMPLING MUTANT. This edge is invisible to every scan that only
    // checks the default feature set: it needs `frontier`, which is off by
    // default. It is reachable in exactly half the feature subsets, and in NONE
    // of the ones a default-only scan would visit.
    let mut inv = clean_inventory();
    inv.edges.push(OracleEdge {
        target: "lean".to_string(),
        capability: OracleCapability::SpawnReferenceBinary,
        requires: features(&["frontier"]),
    });
    let outcome = scan(&inv);
    assert!(!outcome.clears_release(), "the gated path was not caught");
    assert!(leaks(&outcome).contains(&"reachable-capability"));

    // The finding names the exact combination, so it is reproducible rather
    // than a claim. Every reported hit must actually enable the feature.
    match &outcome {
        ScanOutcome::Leaks(l) => {
            let hits: Vec<&Leak> = l
                .iter()
                .filter(|x| matches!(x, Leak::ReachableCapability { .. }))
                .collect();
            // 3 profiles × 2 subsets containing `frontier` = 6.
            assert_eq!(hits.len(), 6, "wrong number of reachable combinations");
            for h in hits {
                match h {
                    Leak::ReachableCapability {
                        target, features, ..
                    } => {
                        assert_eq!(target, "fln-lake::lean");
                        assert!(
                            features.iter().any(|f| f == "frontier"),
                            "a hit was reported for a combination that does not enable it"
                        );
                    }
                    other => panic!("unexpected leak {other:?}"),
                }
            }
        }
        other => panic!("expected Leaks, got {other:?}"),
    }
}

#[test]
fn a_path_requiring_two_features_is_caught_only_when_both_are_on() {
    // Conjunctive gating. A scan that treated `requires` as "any" rather than
    // "all" would report four hits per profile instead of one, and a scan that
    // ignored it entirely would report all four subsets.
    let mut inv = clean_inventory();
    inv.edges.push(OracleEdge {
        target: "lean".to_string(),
        capability: OracleCapability::OracleFallback,
        requires: features(&["frontier", "olean-next"]),
    });
    match scan(&inv) {
        ScanOutcome::Leaks(l) => {
            let hits = l
                .iter()
                .filter(|x| matches!(x, Leak::ReachableCapability { .. }))
                .count();
            // Exactly one subset enables both, times 3 profiles.
            assert_eq!(hits, 3, "conjunctive feature gating is wrong");
        }
        other => panic!("expected Leaks, got {other:?}"),
    }
}

#[test]
fn an_ungated_oracle_path_is_caught_in_every_combination() {
    let mut inv = clean_inventory();
    inv.edges.push(OracleEdge {
        target: "lake".to_string(),
        capability: OracleCapability::LinkReferenceSymbol,
        requires: BTreeSet::new(),
    });
    match scan(&inv) {
        ScanOutcome::Leaks(l) => {
            let hits = l
                .iter()
                .filter(|x| matches!(x, Leak::ReachableCapability { .. }))
                .count();
            // 3 profiles × 4 subsets.
            assert_eq!(hits, 12);
        }
        other => panic!("expected Leaks, got {other:?}"),
    }
}

#[test]
fn an_edge_naming_an_unknown_target_blocks_rather_than_being_ignored() {
    // An edge the scan cannot classify must not be silently dropped. Ignoring
    // it would be assuming the answer that happens to be convenient.
    let mut inv = clean_inventory();
    inv.edges.push(OracleEdge {
        target: "ghost-binary".to_string(),
        capability: OracleCapability::SpawnReferenceBinary,
        requires: BTreeSet::new(),
    });
    let outcome = scan(&inv);
    assert!(!outcome.clears_release());
    assert!(leaks(&outcome).contains(&"dangling-edge"));
}

// ---------------------------------------------------------------------------
// An incomplete scan is Inconclusive, never a pass
// ---------------------------------------------------------------------------

#[test]
fn a_space_too_large_to_enumerate_is_inconclusive_not_clean() {
    // FL-INV-07 applied to the scan itself. A scan that cannot enumerate its
    // space has not cleared the release; it has failed to look. Reporting a
    // pass here is precisely "certifying what it did not check".
    let mut inv = clean_inventory();
    inv.features = (0..40).map(|i| format!("f{i}")).collect();
    let outcome = scan(&inv);
    assert!(!outcome.clears_release());
    match &outcome {
        ScanOutcome::Inconclusive(why) => {
            let text = format!("{why:?}");
            // Specifically the PRE-WALK refusal, made before any work. The
            // fallback runaway guard would also stop this, but only after a
            // million iterations, and it means something different: that the
            // size computation was wrong. Asserting the exact reason keeps the
            // two guards independently observable, so a mutation deleting
            // either one is still visible to the campaign.
            assert!(
                text.contains("BudgetExceeded"),
                "expected the pre-walk refusal, got {text}"
            );
            assert!(
                !text.contains("EnumerationRunaway"),
                "the pre-walk check did not fire and the fallback had to catch it: {text}"
            );
        }
        other => panic!("expected Inconclusive, got {other:?}"),
    }
    assert!(report(&outcome).contains("verdict=inconclusive"));
    // And it is not a leak either — the scan is not claiming to have found
    // something, it is declining to answer.
    assert!(leaks(&outcome).is_empty());
}

#[test]
fn the_budget_boundary_is_enumerated_rather_than_refused() {
    // The other side: a space that fits must actually be walked, so the budget
    // cannot be satisfied by refusing everything.
    let mut inv = clean_inventory();
    inv.features = (0..10).map(|i| format!("f{i}")).collect();
    match scan(&inv) {
        ScanOutcome::Clean {
            combinations_checked,
            ..
        } => {
            assert_eq!(combinations_checked, 2 * 3 * 1024);
            assert!(combinations_checked <= ENUMERATION_BUDGET);
        }
        other => panic!("a space inside the budget was not enumerated: {other:?}"),
    }
}

#[test]
fn a_scan_with_no_profiles_is_inconclusive() {
    // "Every profile" over an empty set is vacuously true, and a vacuous pass
    // is the most dangerous kind.
    let mut inv = clean_inventory();
    inv.profiles.clear();
    let outcome = scan(&inv);
    assert!(!outcome.clears_release());
    assert!(matches!(outcome, ScanOutcome::Inconclusive(_)));
}

// ---------------------------------------------------------------------------
// Poison typing
// ---------------------------------------------------------------------------

#[test]
fn an_unpoisoned_oracle_derived_product_blocks() {
    // THE UNPOISONED-PRODUCT MUTANT. Oracle-derived implies poisoned; a
    // product that violates it has laundered its provenance.
    let mut inv = clean_inventory();
    inv.products.push(Product {
        name: "extracted-census.tsv".to_string(),
        provenance: Provenance::OracleDerived,
        poisoned: false,
    });
    let outcome = scan(&inv);
    assert!(!outcome.clears_release());
    assert!(leaks(&outcome).contains(&"unpoisoned-product"));
}

#[test]
fn a_poisoned_product_satisfies_no_gate_and_enters_no_cache() {
    // Two separate questions with the same answer. A cached poisoned product is
    // worse than an admitted one, because the cache outlives the run that made
    // it and nothing downstream can tell where it came from.
    let poisoned = Product {
        name: "oracle-trace.jsonl".to_string(),
        provenance: Provenance::OracleDerived,
        poisoned: true,
    };
    assert!(!poisoned.admissible_to_gate());
    assert!(!poisoned.cacheable());

    let own = Product {
        name: "fln-kernel.rlib".to_string(),
        provenance: Provenance::OwnWork,
        poisoned: false,
    };
    assert!(own.admissible_to_gate());
    assert!(own.cacheable());
}

#[test]
fn poison_propagates_transitively_through_derivation() {
    // A three-step chain where only the first input is oracle-derived. If
    // propagation were shallow, step three would come out clean and the whole
    // boundary would leak through one indirection.
    let oracle = Product {
        name: "reference-dump".to_string(),
        provenance: Provenance::OracleDerived,
        poisoned: true,
    };
    let own = Product {
        name: "our-fixture".to_string(),
        provenance: Provenance::OwnWork,
        poisoned: false,
    };
    let step1 = derive_product("normalized-dump", Provenance::OwnWork, &[&oracle, &own]);
    assert!(step1.poisoned, "poison did not propagate one step");
    let step2 = derive_product("summary", Provenance::OwnWork, &[&step1]);
    assert!(step2.poisoned, "poison did not propagate two steps");
    let step3 = derive_product("gate-input", Provenance::OwnWork, &[&step2, &own]);
    assert!(step3.poisoned, "poison did not propagate three steps");
    assert!(!step3.admissible_to_gate());

    // And a chain with no oracle input anywhere stays clean, so the rule is not
    // satisfied by poisoning everything.
    let clean = derive_product("pure", Provenance::OwnWork, &[&own]);
    assert!(clean.admissible_to_gate());
    assert!(clean.cacheable());
}

#[test]
fn a_poisoned_value_cannot_be_unwrapped_only_derived_or_inspected() {
    // The structural half. `Poisoned<T>` has no `into_inner`, no `Deref`, no
    // `AsRef` and no `From<Poisoned<T>> for T`: poison that can be removed is
    // a label, and a label is what D8 says is not enough. The only accessor is
    // named for diagnosis, so any use of it reads as the argument it needs to
    // be at the call site.
    let p = Poisoned::new("lean 4.32.0\n".to_string());
    assert_eq!(p.marker(), ORACLE_FALLBACK);
    assert!(p.inspect_for_diagnosis().contains("4.32.0"));

    // The only map-shaped operation returns another Poisoned, so no chain of
    // ordinary combinators ends in a clean value.
    let derived: Poisoned<usize> = p.derive(|s| s.len());
    assert_eq!(*derived.inspect_for_diagnosis(), 12);
    assert_eq!(derived.marker(), ORACLE_FALLBACK);

    // These do not compile, which is the actual guarantee:
    //   let clean: String = p.into_inner();      // no such method
    //   let clean: &str = &*p;                   // no Deref impl
    //   let clean: String = String::from(p);     // no From impl
}

#[test]
fn every_leak_is_reported_not_just_the_first() {
    // An inventory with four problems should report four rather than turning
    // one fix-and-rerun cycle into four.
    let mut inv = clean_inventory();
    inv.edges.push(OracleEdge {
        target: "lean".to_string(),
        capability: OracleCapability::OracleFallback,
        requires: BTreeSet::new(),
    });
    inv.edges.push(OracleEdge {
        target: "ghost".to_string(),
        capability: OracleCapability::SpawnReferenceBinary,
        requires: BTreeSet::new(),
    });
    inv.products.push(Product {
        name: "laundered".to_string(),
        provenance: Provenance::OracleDerived,
        poisoned: false,
    });
    let outcome = scan(&inv);
    let r = leaks(&outcome);
    for want in [
        "reachable-capability",
        "dangling-edge",
        "unpoisoned-product",
    ] {
        assert!(r.contains(&want), "{want} was not reported: {outcome:?}");
    }
    assert!(report(&outcome).contains("verdict=fail"));
}

#[test]
fn the_report_distinguishes_pass_fail_and_inconclusive() {
    // Three outcomes, three verdicts. Collapsing inconclusive into either of
    // the others is the whole hazard.
    let mut leaky = clean_inventory();
    leaky.edges.push(OracleEdge {
        target: "lean".to_string(),
        capability: OracleCapability::OracleFallback,
        requires: BTreeSet::new(),
    });
    let mut huge = clean_inventory();
    huge.features = (0..40).map(|i| format!("f{i}")).collect();

    assert_eq!(scan(&clean_inventory()).verdict(), "pass");
    assert_eq!(scan(&leaky).verdict(), "fail");
    assert_eq!(scan(&huge).verdict(), "inconclusive");
    assert!(report(&scan(&huge)).contains("verdict=inconclusive"));
    assert!(!report(&scan(&huge)).contains("verdict=pass"));
}
