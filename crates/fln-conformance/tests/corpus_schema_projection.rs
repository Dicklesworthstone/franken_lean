//! The corpus-schema projection suite (bead `franken_lean-dgxa`; plan Appendix B).
//!
//! `fln_hash::canon::SCHEMA_REGISTRY` is the program's reviewed inventory of durable
//! formats, and Appendix B wants **one** specification feeding both the codecs and the
//! conformance corpus. The codec half is enforced by `fln-hash`'s own
//! `tests/schema_registry.rs`, which joins the registry against each owner's
//! declaration file. This is the corpus half: the Tribunal's descriptors are a
//! projection of that registry, joined in both directions.
//!
//! Every planted mismatch below drives the **production** join,
//! [`fln_conformance::corpus::project`], over perturbed copies of the real tables. A
//! mutation harness that re-implements the thing it is mutating can report a false
//! green; that lesson is already recorded in `fln-hash`'s suite and it applies here
//! unchanged. The checked-in tables are never modified — the plants are local `Vec`s.

#![forbid(unsafe_code)]

use fln_conformance::corpus::{
    CORPUS_COVERAGE, CorpusCoverage, CorpusDescriptor, ProjectionFault, descriptors, project,
    projection_root,
};
use fln_hash::canon::{SCHEMA_REGISTRY, SchemaId, SchemaOwner, SchemaRow};

fn registry() -> Vec<SchemaRow> {
    SCHEMA_REGISTRY.to_vec()
}

fn coverage() -> Vec<CorpusCoverage> {
    CORPUS_COVERAGE.to_vec()
}

/// The control every plant is measured against.
#[test]
fn the_live_projection_is_clean_and_derives_from_the_registry() {
    let projection = descriptors();
    // Every fault is rendered, not just the first: this is the message someone repairs
    // the tree from, and a one-at-a-time gate turns one edit into N runs.
    let report = projection
        .as_ref()
        .err()
        .map(|faults| {
            faults
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n\n")
        })
        .unwrap_or_default();
    assert!(
        projection.is_ok(),
        "the corpus and SCHEMA_REGISTRY disagree:\n\n{report}"
    );
    let live = projection.expect("asserted Ok immediately above");

    assert_eq!(
        live.len(),
        SCHEMA_REGISTRY.len(),
        "the projection must have one descriptor per registered format; a shorter one \
         is a corpus that covers a subset while reading as if it covered everything"
    );

    // "Derived rather than restated beside it" is a property of the *type*, and this
    // loop is where it is stated: a CorpusDescriptor's only registry-facing field is a
    // borrowed `&SchemaRow`, and a CorpusCoverage has no owner and no `covers` field at
    // all — so there is nowhere in the corpus for those to be restated and drift. The
    // one thing the corpus does spell out is the join key (name + version), and the
    // join below is precisely what makes that safe.
    //
    // Pointer identity is deliberately not asserted: SCHEMA_REGISTRY is a `const`, not
    // a `static`, so every use site materialises its own copy and there is no single
    // instance to point at. An assertion that cannot hold would be a false guard.
    for (index, descriptor) in live.iter().enumerate() {
        let row = &SCHEMA_REGISTRY[index];
        assert_eq!(
            *descriptor.row, *row,
            "descriptor {index} does not carry the registry's row, or the projection is \
             not in registry order"
        );
        assert_eq!(
            descriptor.coverage.schema, row.id.name,
            "descriptor bound to the wrong row"
        );
        assert_eq!(descriptor.coverage.version, row.id.version);
    }
}

/// Coverage is not prose: every claim runs.
#[test]
fn every_coverage_claim_demonstrates_itself() {
    let live = descriptors().expect("control: the live projection is clean");
    for descriptor in &live {
        let outcome = (descriptor.coverage.run)(descriptor.row);
        assert!(
            outcome.is_ok(),
            "the corpus claims to cover {}/{} by \"{}\", and the exercise failed:\n{}",
            descriptor.row.id.name,
            descriptor.row.id.version,
            descriptor.coverage.exercise,
            outcome.err().unwrap_or_default()
        );
    }
    assert_eq!(
        live.len(),
        20,
        "the exercise count moved; if a durable format was added or removed, say so in \
         this assertion deliberately rather than letting the loop shrink silently"
    );
}

/// An exercise cannot be about a format other than the row it is registered under.
///
/// The name join proves a row *has* an exercise; only this proves the exercise is
/// *about* that row. Without it a copy-pasted entry could cover one format twice while
/// another went untested, and both joins would still pass.
#[test]
fn an_exercise_registered_under_the_wrong_row_is_refused() {
    let live = descriptors().expect("control: the live projection is clean");
    let mut checked = 0usize;
    for (index, descriptor) in live.iter().enumerate() {
        let other = &live[(index + 1) % live.len()];
        let failure = (descriptor.coverage.run)(other.row).expect_err(
            "an exercise ran happily against a different format's row, so nothing binds \
             a coverage claim to what it actually exercises",
        );
        assert!(
            failure.contains("registered under"),
            "the binding refusal must say which row it was handed: {failure}"
        );
        checked += 1;
    }
    assert_eq!(checked, live.len());
}

#[test]
fn a_registered_format_with_no_corpus_coverage_fails() {
    let registry = registry();
    let mut planted = coverage();
    let dropped = planted.remove(4);

    let faults = project(&registry, &planted).expect_err(
        "a registry row whose coverage was deleted must fail the join, or the corpus \
         can go blind to a durable format one deletion at a time",
    );
    assert!(
        faults.contains(&ProjectionFault::Uncovered {
            schema: dropped.schema.to_string(),
            version: dropped.version,
        }),
        "expected an Uncovered fault for {}: {faults:?}",
        dropped.schema
    );
    // Deleting coverage must not also read as an unregistered claim.
    assert_eq!(faults.len(), 1, "{faults:?}");
}

#[test]
fn a_corpus_descriptor_naming_no_registered_format_fails() {
    let registry = registry();
    let mut planted = coverage();
    planted.push(CorpusCoverage {
        schema: "fln.canon.sneak",
        version: 1,
        exercise: "nothing at all",
        run: |_row| Ok(()),
    });

    let faults = project(&registry, &planted).expect_err(
        "coverage of a format with no registry row must fail; certifying an \
         unpublished identity is how a corpus starts testing its own fixtures",
    );
    assert!(
        faults.contains(&ProjectionFault::Unregistered {
            schema: "fln.canon.sneak".to_string(),
            version: 1,
        }),
        "{faults:?}"
    );
    assert_eq!(faults.len(), 1, "{faults:?}");
}

#[test]
fn a_version_bump_fails_as_drift_from_either_side() {
    // 1. The registry moves and the corpus does not.
    let mut moved_registry = registry();
    let target = moved_registry[2];
    moved_registry[2] = SchemaRow {
        id: SchemaId {
            name: target.id.name,
            version: target.id.version + 1,
        },
        ..target
    };
    let faults = project(&moved_registry, &CORPUS_COVERAGE).expect_err(
        "a registry version bump the corpus has not followed must fail: the corpus \
         would otherwise assert a round trip it ran against the previous encoding",
    );
    assert_eq!(
        faults,
        vec![ProjectionFault::VersionDrift {
            schema: target.id.name.to_string(),
            registry: target.id.version + 1,
            corpus: target.id.version,
        }],
        "drift must be reported as drift, not as an Uncovered/Unregistered pair — the \
         repairs are opposite"
    );

    // 2. The corpus moves and the registry does not.
    let mut moved_corpus = coverage();
    moved_corpus[2].version += 1;
    let faults = project(&SCHEMA_REGISTRY, &moved_corpus)
        .expect_err("a corpus version bump ahead of the registry must fail too");
    assert_eq!(
        faults,
        vec![ProjectionFault::VersionDrift {
            schema: moved_corpus[2].schema.to_string(),
            registry: SCHEMA_REGISTRY[2].id.version,
            corpus: moved_corpus[2].version,
        }]
    );
}

#[test]
fn a_duplicate_row_on_either_side_fails_rather_than_binding_to_the_first() {
    let mut duplicated_coverage = coverage();
    duplicated_coverage.push(CORPUS_COVERAGE[0]);
    let faults = project(&SCHEMA_REGISTRY, &duplicated_coverage)
        .expect_err("two coverage rows for one format must fail");
    assert!(
        faults.contains(&ProjectionFault::DuplicateCoverage {
            schema: CORPUS_COVERAGE[0].schema.to_string(),
        }),
        "{faults:?}"
    );

    let mut duplicated_registry = registry();
    duplicated_registry.push(SCHEMA_REGISTRY[0]);
    let faults = project(&duplicated_registry, &CORPUS_COVERAGE)
        .expect_err("two registry rows for one format must fail");
    assert!(
        faults.contains(&ProjectionFault::DuplicateRegistryRow {
            schema: SCHEMA_REGISTRY[0].id.name.to_string(),
        }),
        "{faults:?}"
    );
}

#[test]
fn the_join_reports_every_disagreement_at_once_and_deterministically() {
    let mut registry = registry();
    let mut planted = coverage();
    planted.remove(0);
    planted.push(CorpusCoverage {
        schema: "fln.canon.sneak",
        version: 1,
        exercise: "nothing at all",
        run: |_row| Ok(()),
    });
    registry[5] = SchemaRow {
        id: SchemaId {
            name: registry[5].id.name,
            version: 9,
        },
        ..registry[5]
    };

    let faults = project(&registry, &planted).expect_err("three independent faults");
    assert_eq!(
        faults.len(),
        3,
        "the join must report every disagreement, not stop at the first: {faults:?}"
    );

    // Same inputs, same order — the report is a diffable artifact, not a set that
    // reshuffles per run (FL-INV-01).
    let again = project(&registry, &planted).expect_err("three independent faults");
    assert_eq!(faults, again);
    let mut sorted = faults.clone();
    sorted.sort();
    assert_eq!(faults, sorted, "faults must come back sorted");
}

#[test]
fn the_projection_root_binds_every_field_a_reader_relies_on() {
    let live = descriptors().expect("control: the live projection is clean");
    let root = projection_root(&live);
    assert_eq!(
        root,
        projection_root(&descriptors().expect("clean")),
        "the root must be a function of the projection alone"
    );

    // Each mutant below changes exactly one field and must move the root. A root that
    // ignores a field is a root that cannot notice that field drifting.
    let row = SCHEMA_REGISTRY[0];
    let claim = CORPUS_COVERAGE[0];
    let base = vec![CorpusDescriptor {
        row: &row,
        coverage: &claim,
    }];
    let base_root = projection_root(&base);

    let renamed = SchemaRow {
        id: SchemaId {
            name: "fln.canon.renamed",
            version: row.id.version,
        },
        ..row
    };
    let bumped = SchemaRow {
        id: SchemaId {
            name: row.id.name,
            version: row.id.version + 1,
        },
        ..row
    };
    let reowned = SchemaRow {
        owner: SchemaOwner::Verdict,
        ..row
    };
    let redescribed = SchemaRow {
        covers: "something else entirely",
        ..row
    };
    for (label, mutant) in [
        ("name", renamed),
        ("version", bumped),
        ("owner", reowned),
        ("covers", redescribed),
    ] {
        let projected = vec![CorpusDescriptor {
            row: &mutant,
            coverage: &claim,
        }];
        assert_ne!(
            projection_root(&projected),
            base_root,
            "changing a row's {label} did not move the projection root"
        );
    }

    let reexercised = CorpusCoverage {
        exercise: "something weaker",
        ..claim
    };
    let projected = vec![CorpusDescriptor {
        row: &row,
        coverage: &reexercised,
    }];
    assert_ne!(
        projection_root(&projected),
        base_root,
        "weakening the stated exercise did not move the projection root, so the claim \
         could be quietly downgraded"
    );

    // Length-prefixing, not concatenation: two projections whose fields concatenate to
    // the same bytes must still differ.
    let ambiguous = SchemaRow {
        id: SchemaId {
            name: "fln.canon.nam",
            version: row.id.version,
        },
        ..row
    };
    let shifted = CorpusCoverage {
        schema: "fln.canon.nam",
        ..claim
    };
    let projected = vec![CorpusDescriptor {
        row: &ambiguous,
        coverage: &shifted,
    }];
    assert_ne!(projection_root(&projected), base_root);
}
