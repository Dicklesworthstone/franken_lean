//! The pinned binary's own option table, asked at test time (bead
//! `fln-parity-ledger-l2-pinned-source-qydn`).
//!
//! # What this is for
//!
//! Eight rows in `ci/PARITY_LEDGER.txt` record option defaults at level **L2** with
//! oracle-kind **pinned-source**. The ledger's own tier note (`:41-48`) defines L2 as "the
//! pinned Reference binary produced the expected value" and L1 as "implemented against the
//! pinned SOURCE semantics ... no Reference-produced value is compared". Those eight are
//! earned by `crates/fln-core/tests/pin_inventory_census.rs`, which reads vendored upstream
//! `.lean` text — real evidence, and by the ledger's own definition L1, not L2.
//!
//! This asks the binary instead. `Lean.getOptionDeclsArray` is stock
//! (`vendor/lean4-src/src/Lean/Data/Options.lean:127`), so the whole registered option
//! table — name, default, description — prints from an unpatched pin through ordinary
//! metaprogramming. No patched Reference, no §18.3 instrumented oracle. That is bead
//! `franken_lean-c24a`'s finding (the pin is reachable through its own surface) applied to
//! a second surface.
//!
//! # Why there is no fixture here, deliberately
//!
//! The oracle runs *in this test*, so there is no capture that can go stale between runs.
//! That is not a stylistic preference: bead `franken_lean-ext-observable-fixture-drift-gap-vqnu`
//! records 28 rows resting on a 533-record capture that nothing re-derives, one directory
//! over. A live differential cannot acquire that defect. The cost is that this test is a
//! typed SKIP without the pinned toolchain, which is the same trade every pin-dependent rig
//! here already makes.
//!
//! # What a green run does and does not establish
//!
//! It establishes that every option default `fln-core` claims is the value the pinned
//! binary reports for that option, right now, on this host. It establishes nothing about
//! the 653 options in that table which `fln-core` does not implement: this is a differential
//! over OUR claims, not a census of upstream's surface. The count is reported on every run
//! so the ratio cannot be mistaken for coverage.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::path::Path;

use fln_conformance::{ledger, pin};
use fln_core::options::limits;

fn workspace_root() -> &'static Path {
    static ROOT: std::sync::OnceLock<std::path::PathBuf> = std::sync::OnceLock::new();
    ROOT.get_or_init(|| fln_conformance::checked_workspace_root!())
        .as_path()
}

/// What `fln-core` claims, and the exact ledger row each claim backs.
///
/// Kept as data rather than a sequence of assertions so the planted-violation test below
/// can drive the same comparison the live test does. A test whose failure path is a
/// different code path from its success path has not been shown to fail.
const CLAIMED_DEFAULTS: [(&str, u64); 8] = [
    ("maxHeartbeats", limits::MAX_HEARTBEATS_DEFAULT),
    ("maxRecDepth", limits::MAX_REC_DEPTH_DEFAULT),
    (
        "synthInstance.maxHeartbeats",
        limits::SYNTH_INSTANCE_MAX_HEARTBEATS_DEFAULT,
    ),
    (
        "synthInstance.maxSize",
        limits::SYNTH_INSTANCE_MAX_SIZE_DEFAULT,
    ),
    (
        "maxSynthPendingDepth",
        limits::MAX_SYNTH_PENDING_DEPTH_DEFAULT,
    ),
    ("maxUniverseOffset", limits::MAX_UNIVERSE_OFFSET_DEFAULT),
    (
        "exponentiation.threshold",
        limits::EXPONENTIATION_THRESHOLD_DEFAULT,
    ),
    ("maxErrors", limits::MAX_ERRORS_DEFAULT),
];

/// The probe. `logInfo` on a command is the pin's ordinary reporting surface; nothing here
/// patches, links against, or otherwise executes upstream implementation code (D8) — the
/// binary is being *asked a question*, which is exactly the oracle role the Oracle-Only Law
/// reserves for it.
const PROBE: &str = r#"import Lean
open Lean
run_cmd do
  let decls ← Lean.getOptionDeclsArray
  let mut n : Nat := 0
  for (name, decl) in decls do
    n := n + 1
    logInfo m!"OPTION|{name}|{decl.defValue}"
  logInfo m!"TABLE_SIZE|{n}"
"#;

/// Parse `OPTION|<name>|<default>` out of whatever else the binary prints.
///
/// Marker-anchored rather than line-anchored on purpose: message rendering is not a
/// contract this test wants to depend on, and a prefix change should not be reported as an
/// option divergence.
fn parse_table(stdout: &str) -> (BTreeMap<String, String>, Option<usize>) {
    let mut table = BTreeMap::new();
    let mut size = None;
    for line in stdout.lines() {
        if let Some(rest) = line.split("OPTION|").nth(1) {
            let mut parts = rest.splitn(2, '|');
            if let (Some(name), Some(value)) = (parts.next(), parts.next()) {
                table.insert(name.trim().to_string(), value.trim().to_string());
            }
        } else if let Some(rest) = line.split("TABLE_SIZE|").nth(1) {
            size = rest.trim().parse::<usize>().ok();
        }
    }
    (table, size)
}

/// Every claim that the oracle does not corroborate, rendered for a human.
///
/// Absence and disagreement are separate findings: an option we implement that upstream
/// does not register at all is a different defect from one whose default moved, and
/// collapsing them would hide the first behind the second.
fn divergences(claimed: &[(&str, u64)], table: &BTreeMap<String, String>) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ours) in claimed {
        match table.get(*name) {
            None => out.push(format!(
                "{name}: fln-core claims a default of {ours}, and the pinned binary registers \
                 no option by that name — either the option was renamed upstream or ours is \
                 an invention"
            )),
            Some(theirs) if theirs != &ours.to_string() => out.push(format!(
                "{name}: fln-core says {ours}, the pinned binary says {theirs}"
            )),
            Some(_) => {}
        }
    }
    out
}

// ---------------------------------------------------------------------------
// The live differential
// ---------------------------------------------------------------------------

#[test]
fn every_option_default_fln_core_claims_is_the_one_the_pinned_binary_reports() {
    let Some(lean) = pin::pinned_lean() else {
        eprintln!("{}", pin::skip_notice("pin_option_defaults"));
        return;
    };

    // A pin that is present but unrunnable fails the test rather than skipping it: the
    // toolchain was located, so this is a broken oracle, not an absent one.
    let answer = pin::ask(&lean, "pin_option_defaults", PROBE)
        .expect("the located pinned binary is executable");

    let (table, size) = parse_table(&answer.stdout);
    assert!(
        answer.success,
        "the pinned binary refused the probe (exit {:?}).\nstdout:\n{}\nstderr:\n{}",
        answer.code, answer.stdout, answer.stderr
    );

    // A parse that quietly returned a handful of rows would make the comparison below
    // vacuous for everything it did not see. The pin registered 661 options at v4.32.0;
    // the floor is deliberately far below that, because this guards against a broken
    // parse, not against upstream adding options.
    let reported = size.unwrap_or(0);
    assert_eq!(
        reported,
        table.len(),
        "the binary reported {reported} options and the parse recovered {}; a partial parse \
         makes every absent-option finding below meaningless",
        table.len()
    );
    assert!(
        table.len() > 500,
        "only {} options parsed out of the pin's registered table — this is a parse failure \
         wearing the costume of a clean run",
        table.len()
    );

    let found = divergences(&CLAIMED_DEFAULTS, &table);
    assert!(
        found.is_empty(),
        "fln-core disagrees with the pinned binary about {} option default(s):\n  {}",
        found.len(),
        found.join("\n  ")
    );

    // Reported, never asserted as coverage: this is a differential over OUR claims.
    println!(
        "pin_option_defaults: {} of {} registered options implemented and corroborated \
         against the pinned binary; the remaining {} are NOT covered by this or any other \
         rig, and this ratio is not a compatibility figure",
        CLAIMED_DEFAULTS.len(),
        table.len(),
        table.len() - CLAIMED_DEFAULTS.len()
    );
}

// ---------------------------------------------------------------------------
// Planted violations — the comparison must be shown to fail
// ---------------------------------------------------------------------------

/// A differential that has only ever been observed agreeing is not evidence of agreement.
/// These drive the same `divergences` the live test does, over a synthetic table, so they
/// run with or without the pinned toolchain.
#[test]
fn the_comparison_catches_a_moved_default_a_renamed_option_and_nothing_else() {
    let honest: BTreeMap<String, String> = CLAIMED_DEFAULTS
        .iter()
        .map(|(name, value)| ((*name).to_string(), value.to_string()))
        .collect();
    assert!(
        divergences(&CLAIMED_DEFAULTS, &honest).is_empty(),
        "a table that agrees must produce no findings, or the guard is a wall"
    );

    // 1. The default moved upstream. This is the case the eight ledger rows exist to catch,
    //    and reading vendored source would catch it too — only later, and only if someone
    //    re-read the source.
    let mut moved = honest.clone();
    moved.insert("maxRecDepth".into(), "1024".into());
    let found = divergences(&CLAIMED_DEFAULTS, &moved);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].contains("fln-core says 512, the pinned binary says 1024"),
        "the finding must name both numbers, or it cannot be triaged: {found:?}"
    );

    // 2. The option is gone, or was never real. Distinct from a moved default: one is a
    //    value drifting, the other is a claim about a surface that does not exist.
    let mut renamed = honest.clone();
    renamed.remove("exponentiation.threshold");
    let found = divergences(&CLAIMED_DEFAULTS, &renamed);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].contains("registers no option by that name"),
        "an absent option must not be reported as a value disagreement: {found:?}"
    );

    // 3. Options we do not claim are not our business. A table full of upstream options we
    //    have never implemented must produce no findings, or this rig would grow into a
    //    census it has not earned and cannot maintain.
    let mut extra = honest;
    for i in 0..50 {
        extra.insert(format!("upstream.optionWeDoNotImplement{i}"), "7".into());
    }
    assert!(
        divergences(&CLAIMED_DEFAULTS, &extra).is_empty(),
        "unimplemented upstream options are not divergences"
    );
}

/// The parser must survive the binary's message decoration, and must not invent rows.
#[test]
fn the_parse_is_anchored_on_the_marker_not_on_the_line_shape() {
    let noisy = "probe.lean:4:2: information: OPTION|maxRecDepth|512\n\
                 some unrelated diagnostic text\n\
                 OPTION|maxErrors|100\n\
                 TABLE_SIZE|2\n";
    let (table, size) = parse_table(noisy);
    assert_eq!(size, Some(2));
    assert_eq!(table.get("maxRecDepth").map(String::as_str), Some("512"));
    assert_eq!(table.get("maxErrors").map(String::as_str), Some("100"));
    assert_eq!(
        table.len(),
        2,
        "no row may be invented from prose: {table:?}"
    );

    let (empty, no_size) = parse_table("nothing here\n");
    assert!(empty.is_empty() && no_size.is_none());
}

// ---------------------------------------------------------------------------
// This rig's scope, against the ledger
// ---------------------------------------------------------------------------

/// Every allowance entry naming an option row that this rig is supposed to back, and does
/// not.
///
/// Kept as a function over its inputs so the planted cases below drive the *same* code the
/// live check does — the discipline [`the_comparison_catches_a_moved_default_a_renamed_option_and_nothing_else`]
/// already applies to `divergences`, applied here to the scope check.
///
/// The option rows are identified by the ledger's own `kind` field rather than by a name
/// pattern over the symbol. Deriving the scope from the artifact is the point: a hand-listed
/// or spelling-inferred scope is a second copy of the ledger that rots silently when the
/// ledger moves, which is the defect class this whole rig exists to answer.
fn unbacked_option_rows<'a>(
    claimed: &[(&str, u64)],
    allowance: &[&'a str],
    ledger: &ledger::Ledger,
) -> Vec<&'a str> {
    allowance
        .iter()
        .filter(|symbol| {
            ledger
                .rows
                .iter()
                .any(|row| row.symbol == **symbol && row.kind == "option")
        })
        .filter(|symbol| !claimed.iter().any(|(name, _)| name == *symbol))
        .copied()
        .collect()
}

/// The join between the declared remainder and the oracle that is supposed to retire it
/// (bead `fln-parity-ledger-l2-pinned-source-qydn`).
///
/// `SOURCE_READ_ALLOWANCE_REASON` states, as the reason eight rows may stay in the
/// remainder, that *this file* asks the pinned binary for all eight of their defaults. That
/// sentence was prose: dropping an entry from [`CLAIMED_DEFAULTS`] narrows the probe and the
/// comparison **together**, so every other check in this file still passed while a published
/// L2 row silently lost the evidence its exemption is justified by. Measured, not argued —
/// with `maxErrors` removed, all sixteen tests across the three suites stayed green.
///
/// That is AGENTS.md item 7's shape (`a claim and the evidence that produces it, with the
/// join unwatched`) occurring *inside* the repair for item 7's own instance. The sibling rig
/// `pin_ctor_inventory.rs` already carries this guard for its four rows; the eight option
/// rows had only the sentence.
///
/// The membership direction is deliberately one-way, for the reason that rig records:
/// asserting that every backed row is still IN the allowance would turn `ci/PARITY_LEDGER.txt`
/// being *repaired* into a red build, because a repaired row leaves the remainder. A row this
/// rig still corroborates after its exemption is gone is the intended end state.
///
/// What this does **not** establish: once cod_2 repairs these rows and the remainder empties,
/// this check goes vacuous and the eight rows keep their oracle by convention again. Closing
/// that needs the repaired rows to cite this rig in their `fixtures`, which is an edit to
/// their artifact and not mine to make.
#[test]
fn this_rig_backs_eight_ledger_rows_and_every_unrepaired_option_row_is_among_them() {
    // Membership first, because it NAMES the row that lost its oracle, which is the
    // actionable half. The count below catches what membership structurally cannot see —
    // an entry added or duplicated rather than dropped.
    let text = std::fs::read_to_string(workspace_root().join("ci/PARITY_LEDGER.txt"))
        .expect("ledger exists");
    let parsed = ledger::parse(&text).expect("ledger parses");
    let unbacked = unbacked_option_rows(
        &CLAIMED_DEFAULTS,
        &ledger::SOURCE_READ_ABOVE_L1_ALLOWANCE,
        &parsed,
    );
    assert!(
        unbacked.is_empty(),
        "{unbacked:?} are still in the declared remainder as source-read L2 option rows, and \
         this rig does not ask the pinned binary about them — the remainder names rows this \
         file was supposed to give a value-producing oracle.\n\nDeclared remainder:\n{}",
        ledger::SOURCE_READ_ALLOWANCE_REASON
    );

    // The anti-vacuity floor, and it is a FLOOR rather than an equality on purpose.
    //
    // The membership check above is scoped to the declared remainder, so when cod_2 repairs
    // these rows and the remainder empties it stops checking anything at all — quietly, and
    // exactly when the rows have just become load-bearing published L2 claims. That is the
    // `uagk` lesson in AGENTS.md item 7: a scan that returns empty is a broken scan, not a
    // clean tree. This floor is what still holds when the remainder is gone.
    //
    // Not `== 8`: fln-core implementing a ninth option and this rig growing to cover it is a
    // GOOD change, and an equality would turn it into a red build for no defect — the same
    // wall-shaped mistake the membership direction above is careful to avoid.
    let mut backed: Vec<&str> = CLAIMED_DEFAULTS.iter().map(|(name, _)| *name).collect();
    backed.sort_unstable();
    backed.dedup();
    assert!(
        backed.len() >= 8,
        "this rig asks the pinned binary about {} distinct option(s), below the 8 option rows \
         of bead fln-parity-ledger-l2-pinned-source-qydn that it exists to back: {backed:?}. \
         An entry was dropped or duplicated — and once those rows leave the declared \
         remainder, this floor is the only thing still checking that they kept their oracle",
        backed.len()
    );
}

/// The scope check must be shown to fail, and to stay quiet where it should.
///
/// Three planted cases over a synthetic ledger, so this runs with or without the pinned
/// toolchain and so the one-way direction is a per-commit fact rather than something I
/// verified once by hand.
#[test]
fn the_scope_check_catches_a_dropped_option_and_permits_a_repaired_row() {
    let ledger_text = "\
schema fln-parity-ledger/1
row meta-api | maxErrors | option | native | L2 | faithful | pinned-source | exact | \
crates/fln-conformance/fixtures/core_observables.txt | D0 | OBSERVED | pin-census-v4.32.0
row meta-api | maxRecDepth | option | native | L2 | faithful | pinned-source | exact | \
crates/fln-conformance/fixtures/core_observables.txt | D0 | OBSERVED | pin-census-v4.32.0
row meta-api | Lean.Expr.ctorInventory | census | native | L2 | faithful | pinned-source | \
exact | crates/fln-conformance/fixtures/core_observables.txt | D0 | OBSERVED | pin-census-v4.32.0
";
    let parsed = ledger::parse(ledger_text).expect("synthetic ledger parses");
    let claimed: [(&str, u64); 2] = [("maxErrors", 100), ("maxRecDepth", 512)];

    // 1. Everything the remainder names is backed. No finding.
    assert!(
        unbacked_option_rows(&claimed, &["maxErrors", "maxRecDepth"], &parsed).is_empty(),
        "a rig that backs every remaining option row must produce no finding, or the guard \
         is a wall"
    );

    // 2. THE MUTANT. An option dropped from the rig while its row stays in the remainder —
    //    the exact edit that left all sixteen tests green before this guard existed.
    let dropped: [(&str, u64); 1] = [("maxRecDepth", 512)];
    assert_eq!(
        unbacked_option_rows(&dropped, &["maxErrors", "maxRecDepth"], &parsed),
        vec!["maxErrors"],
        "dropping an option from the rig must be reported while its row is still exempt"
    );

    // 3. THE REPAIR. A row that has left the remainder is not this guard's business, so
    //    shrinking the allowance cannot redden the build. This is the direction that makes
    //    the guard survive the repair it is asking for.
    assert!(
        unbacked_option_rows(&dropped, &["maxRecDepth"], &parsed).is_empty(),
        "a repaired row that left the remainder must not be reported as unbacked"
    );

    // 4. Non-option rows are out of scope: the ctorInventory rows are backed by
    //    pin_ctor_inventory.rs, and claiming them here would report a false gap.
    assert!(
        unbacked_option_rows(&claimed, &["Lean.Expr.ctorInventory"], &parsed).is_empty(),
        "a census row is not an option row and is not this rig's to back"
    );

    // 5. WHY THE FLOOR EXISTS. Once every row is repaired the remainder is empty, and this
    //    check goes vacuous — a rig that had silently stopped asking about ANY option would
    //    produce no finding here. Asserted rather than remarked, so the limitation is a
    //    property of the code and not a comment somebody has to believe.
    assert!(
        unbacked_option_rows(&[], &[], &parsed).is_empty(),
        "with an empty remainder this check cannot fail, which is what the >= 8 floor in \
         the live test is for"
    );
}

/// The pin this rig probes must be the pin the lock names. A rig that reads a toolchain
/// nobody pinned would be green against the wrong oracle.
#[test]
fn the_probed_toolchain_is_the_one_suite_lock_pins() {
    let tag = pin::pinned_tag().expect("SUITE.lock names a reference tag");
    assert!(
        tag.starts_with('v'),
        "the reference tag should look like a version: {tag:?}"
    );
    if let Ok(explicit) = std::env::var("FLN_REFERENCE_BIN") {
        eprintln!("pin_option_defaults: FLN_REFERENCE_BIN overrides the elan layout ({explicit})");
        return;
    }
    if let Some(path) = pin::pinned_lean() {
        let rendered = path.to_string_lossy().into_owned();
        assert!(
            rendered.contains(&tag),
            "the located toolchain {rendered} is not the {tag} the lock pins"
        );
    }
}
