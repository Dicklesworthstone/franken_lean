//! The Parity-Ledger gate (bead fln-euo): the REAL ledger must parse, every cited
//! fixture must exist, and the aggregate view must be derivable — on every CI run.
//! A ledger that cites missing evidence is marketing and fails here.

#![forbid(unsafe_code)]

use std::path::Path;

use fln_conformance::ledger::{self, ClaimState, LLevel};

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
}

#[test]
fn the_real_ledger_parses_validates_and_aggregates() {
    let root = workspace_root();
    let text = std::fs::read_to_string(root.join("ci/PARITY_LEDGER.txt")).expect("ledger exists");
    let parsed = ledger::parse(&text).expect("ledger parses");
    assert!(!parsed.rows.is_empty(), "the ledger has rows");
    ledger::validate_fixtures(&parsed, root).expect("every cited fixture exists");

    let agg = ledger::aggregate(&parsed);
    assert_eq!(agg.total_rows, parsed.rows.len());
    // The bootstrap posture: the proven core observables sit at L2 OBSERVED.
    assert!(
        agg.by_surface_level
            .get(&("meta-api".to_string(), LLevel::L2))
            .copied()
            .unwrap_or(0)
            >= 5,
        "the p8a-proven observable rows are present at L2"
    );
    assert!(agg.by_claim.contains_key(&ClaimState::Observed));
}

#[test]
fn rows_above_l0_cite_real_evidence() {
    let root = workspace_root();
    let text = std::fs::read_to_string(root.join("ci/PARITY_LEDGER.txt")).expect("ledger exists");
    let parsed = ledger::parse(&text).expect("ledger parses");
    for row in &parsed.rows {
        if row.level > LLevel::L0 {
            assert!(
                !row.fixtures.is_empty(),
                "row `{}` is above L0 with no fixtures",
                row.symbol
            );
        }
    }
}

// ---------------------------------------------------------------------------
// The oracle-supports-level law (bead fln-parity-ledger-l2-pinned-source-qydn)
// ---------------------------------------------------------------------------

/// A synthetic ledger, so the planted cases drive the real parser and the real law rather
/// than a re-implementation of either.
fn synthetic(rows: &[&str]) -> ledger::Ledger {
    let mut text = String::from("schema fln-parity-ledger/1\n");
    for row in rows {
        text.push_str(row);
        text.push('\n');
    }
    ledger::parse(&text).expect("synthetic ledger parses")
}

const OK_FIXTURE: &str = "crates/fln-conformance/fixtures/core_observables.txt";

/// The live ledger obeys the law, with its thirteen exceptions declared.
///
/// This is the direction that will fail as rows are repaired, and that is intended: the
/// allowance is checked in both directions, so shrinking it is part of the repair rather
/// than a follow-up somebody schedules and forgets.
#[test]
fn the_real_ledger_never_earns_a_level_its_oracle_did_not_produce() {
    let text = std::fs::read_to_string(workspace_root().join("ci/PARITY_LEDGER.txt"))
        .expect("ledger exists");
    let parsed = ledger::parse(&text).expect("ledger parses");
    let outcome = ledger::validate_level_is_supported_by_its_oracle(&parsed);
    let rendered = outcome
        .as_ref()
        .err()
        .map(|errors| {
            errors
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n  ")
        })
        .unwrap_or_default();
    assert!(
        outcome.is_ok(),
        "the ledger claims levels its oracles did not produce:\n  {rendered}\n\nDeclared \
         remainder:\n{}",
        ledger::SOURCE_READ_ALLOWANCE_REASON
    );
}

/// THE FOURTEENTH. A new source-read row above L1 is refused even though thirteen exactly
/// like it are permitted — which is the entire value of a declared remainder over a
/// grandfather clause.
#[test]
fn an_undeclared_source_read_row_above_l1_is_refused() {
    let planted = synthetic(&[&format!(
        "row meta-api | Lean.Something.brandNew | function | native | L2 | faithful | \
         pinned-source | exact | {OK_FIXTURE} | D0 | OBSERVED | pin-census-v4.32.0"
    )]);
    let errors = ledger::validate_level_is_supported_by_its_oracle(&planted)
        .expect_err("a source-read row above L1 must be refused unless declared");
    assert!(
        errors
            .iter()
            .any(|error| error.what.contains("Lean.Something.brandNew")
                && error.what.contains("produced no value to compare against")),
        "{errors:?}"
    );
}

/// The allowance cannot outlive the defect. A declared row that has been repaired fails
/// until its entry is removed, so the remainder is a record of work outstanding rather than
/// a permanent exemption.
#[test]
fn a_declared_row_that_was_repaired_fails_until_the_allowance_shrinks() {
    let repaired = synthetic(&[&format!(
        "row meta-api | maxRecDepth | option | native | L2 | faithful | pinned-binary | \
         exact | {OK_FIXTURE} | D0 | OBSERVED | pin-census-v4.32.0"
    )]);
    let errors = ledger::validate_level_is_supported_by_its_oracle(&repaired)
        .expect_err("a stale allowance entry must fail");
    assert!(
        errors
            .iter()
            .any(|error| error.what.contains("maxRecDepth") && error.what.contains("is stale")),
        "{errors:?}"
    );
}

/// The orphan half, which is a property of the WHOLE file rather than of a row — the
/// distinction the planted permission case below forced into the open, because folding it
/// into the per-row law made the law refuse every subset of the ledger.
#[test]
fn an_allowance_entry_naming_no_row_is_refused() {
    let gone = synthetic(&[&format!(
        "row meta-api | Lean.Unrelated.symbol | function | native | L1 | faithful | \
         pinned-source | exact | {OK_FIXTURE} | D0 | OBSERVED | pin-census-v4.32.0"
    )]);
    let errors = ledger::validate_allowance_has_no_orphans(&gone)
        .expect_err("an allowance entry with no row must fail");
    assert_eq!(errors.len(), ledger::SOURCE_READ_ABOVE_L1_ALLOWANCE.len());
    assert!(
        errors
            .iter()
            .any(|error| error.what.contains("is not a row in this ledger")),
        "{errors:?}"
    );

    let text = std::fs::read_to_string(workspace_root().join("ci/PARITY_LEDGER.txt"))
        .expect("ledger exists");
    let real = ledger::parse(&text).expect("ledger parses");
    assert!(
        ledger::validate_allowance_has_no_orphans(&real).is_ok(),
        "every declared exception must name a row that exists in the real ledger"
    );
}

// ---------------------------------------------------------------------------
// The successor law: a repaired row must cite the oracle it claims
// (bead fln-parity-ledger-l2-pinned-source-qydn, extending cc_3's guard)
// ---------------------------------------------------------------------------

/// The live ledger obeys the successor law, and every rig it can demand a citation to exists.
///
/// The first assertion is VACUOUS today — all twelve rows are still in the remainder — and
/// that is by construction, not an oversight. The allowance-scoped guards in
/// `pin_option_defaults.rs` and `pin_ctor_inventory.rs` check exactly the rows this one
/// skips, and go quiet exactly as this one takes over. Neither alone covers both states.
///
/// The second assertion is NOT vacuous and is what stops the first from rotting into a
/// demand nobody can satisfy.
#[test]
fn the_real_ledger_obeys_the_successor_law_and_its_rigs_exist() {
    let root = workspace_root();
    let text = std::fs::read_to_string(root.join("ci/PARITY_LEDGER.txt")).expect("ledger exists");
    let parsed = ledger::parse(&text).expect("ledger parses");

    ledger::validate_oracle_backing_paths_exist(root)
        .expect("every rig ORACLE_BACKING can require a citation to must exist");

    // ORPHAN HALF, and it is not decoration. The law finds each row by symbol and SKIPS a
    // symbol it cannot find, so a typo or a renamed row turns an entry into a silent no-op —
    // the guard reporting a clean tree because it looked for the wrong thing. Checked here
    // against the real ledger, which is the only place the question is meaningful.
    for (symbol, _rig) in ledger::ORACLE_BACKING {
        assert!(
            parsed.rows.iter().any(|row| row.symbol == symbol),
            "ORACLE_BACKING names `{symbol}`, which is not a row in this ledger — the entry \
             is a silent no-op. Move it in the change that moved the row."
        );
    }

    let outcome = ledger::validate_repaired_rows_cite_their_oracle(&parsed);
    let rendered = outcome
        .as_ref()
        .err()
        .map(|errors| {
            errors
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n  ")
        })
        .unwrap_or_default();
    assert!(
        outcome.is_ok(),
        "a repaired row does not cite its oracle:\n  {rendered}"
    );
}

/// THE HALF-REPAIR. Flipping `oracle_kind` to a value-producing one while leaving a
/// source-reading citation in place must be refused.
///
/// This is the failure the successor law exists for, and it is the easy mistake: all twelve
/// rows currently cite `pin_inventory_census.rs`, which reads vendored `.lean` text. A row
/// that says `pinned-binary` on that evidence reports our READING of the oracle under the
/// name of the oracle, and every other check in the module passes it.
#[test]
fn a_repaired_row_that_still_cites_only_its_source_reader_is_refused() {
    let half_repaired = synthetic(&[
        "row meta-api | maxErrors | option | native | L2 | faithful | pinned-binary | exact \
         | crates/fln-core/tests/pin_inventory_census.rs | D0 | OBSERVED | pin-census-v4.32.0",
    ]);
    let errors = ledger::validate_repaired_rows_cite_their_oracle(&half_repaired)
        .expect_err("a repaired row citing only a source reader must be refused");
    assert!(
        errors.iter().any(|error| error.what.contains("maxErrors")
            && error.what.contains("pin_option_defaults.rs")),
        "the finding must name the exact rig to cite, or it cannot be acted on: {errors:?}"
    );
}

/// THE PERMISSION HALF OF THE SUCCESSOR LAW, in both states.
///
/// A fully repaired row that cites its rig is admitted, and an UNREPAIRED row is untouched
/// even though it cites only a source reader — because while it is still declared, the
/// allowance guards own it. Getting this direction wrong would redden the build today for
/// every one of the thirteen.
#[test]
fn the_successor_law_admits_a_full_repair_and_ignores_an_undeclared_repair() {
    let fully_repaired = synthetic(&[
        "row meta-api | maxErrors | option | native | L2 | faithful | pinned-binary | exact \
         | crates/fln-conformance/tests/pin_option_defaults.rs | D0 | OBSERVED | \
         pin-census-v4.32.0",
    ]);
    assert!(
        ledger::validate_repaired_rows_cite_their_oracle(&fully_repaired).is_ok(),
        "a row citing the rig that produced its value is exactly what this law asks for"
    );

    // Still in the remainder: not this law's business, whatever it cites.
    assert!(
        ledger::SOURCE_READ_ABOVE_L1_ALLOWANCE.contains(&"maxRecDepth"),
        "precondition: maxRecDepth is still declared"
    );
    let unrepaired = synthetic(&[
        "row meta-api | maxRecDepth | option | native | L2 | faithful | pinned-source | exact \
         | crates/fln-core/tests/pin_inventory_census.rs | D0 | OBSERVED | pin-census-v4.32.0",
    ]);
    assert!(
        ledger::validate_repaired_rows_cite_their_oracle(&unrepaired).is_ok(),
        "a row still in the declared remainder is the allowance guards' subject, not this law's"
    );
}

/// The two halves must not leave a gap between them: every rig-backed symbol is covered by
/// the allowance guards while declared, and by the successor law once it is not.
///
/// Asserted rather than described, because "these two mechanisms compose" is precisely the
/// kind of claim AGENTS.md item 7 is about — a property stated in prose across two artifacts
/// with nothing checking the join.
#[test]
fn every_declared_row_bar_mixhash_has_a_rig_that_can_retire_it() {
    // ONE-WAY, and the direction is the whole point. Every row still in the remainder needs
    // a rig, or nothing can ever retire it. The converse — every ORACLE_BACKING entry must
    // still be declared — would be a WALL: the map has to OUTLIVE the repair, because the
    // successor law uses it to demand the citation precisely when the row is no longer
    // declared. So ORACLE_BACKING does not shrink with the allowance, and asserting a
    // length relation between them would redden the build on a correct repair.
    for symbol in ledger::SOURCE_READ_ABOVE_L1_ALLOWANCE {
        if symbol == "mixHash" {
            continue;
        }
        assert!(
            ledger::ORACLE_BACKING
                .iter()
                .any(|(backed, _)| *backed == symbol),
            "`{symbol}` is in the declared remainder with no rig in ORACLE_BACKING, so no \
             repair can retire it and the successor law can demand nothing of it"
        );
    }

    // mixHash is the one declared row with no rig, and must not silently acquire one: its
    // repair is a one-token oracle-kind edit against a binary-produced fixture it already
    // cites. If it ever gains an entry, that is a decision, not drift.
    assert!(
        !ledger::ORACLE_BACKING
            .iter()
            .any(|(symbol, _)| *symbol == "mixHash"),
        "mixHash has no rig; its oracle is the binary-produced fixture it already cites"
    );
}

/// THE PERMISSION HALF. The law must admit what it is supposed to admit, or it is a wall:
/// source-read evidence AT L1 is exactly what the ledger's tier note says L1 is, and a
/// value-producing oracle above L1 is the shape the law exists to require.
#[test]
fn source_read_at_l1_and_value_produced_above_it_are_both_permitted() {
    let honest = synthetic(&[
        &format!(
            "row meta-api | Lean.Read.fromSource | function | native | L1 | faithful | \
             pinned-source | exact | {OK_FIXTURE} | D0 | OBSERVED | pin-census-v4.32.0"
        ),
        &format!(
            "row meta-api | Lean.Asked.ofBinary | function | native | L2 | faithful | \
             pinned-binary | exact | {OK_FIXTURE} | D0 | OBSERVED | core-observables-v4.32.0"
        ),
        &format!(
            // Deliberately NOT the real hasher's name: fln-hash's domain-enforcement
            // guard refuses that identifier anywhere outside fln-hash, and it cannot
            // tell fixture prose from a call site. Naming it here made the workspace
            // red from d5cc084b until this line was fixed.
            "row hash | spec.vector | function | native | L2 | faithful | spec-vectors | \
             exact | {OK_FIXTURE} | D0 | OBSERVED | rfc-vectors"
        ),
        "row cli | lean --version | flag | pending | L0 | faithful | pinned-source | exact \
         | , | D1 | TARGETED | inventory-v4.32.0",
    ]);
    let errors = ledger::validate_level_is_supported_by_its_oracle(&honest);
    assert!(
        errors.is_ok(),
        "the law refused evidence it exists to permit: {errors:?}"
    );
}
