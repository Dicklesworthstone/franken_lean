//! The Parity Ledger schema (plan §18.1, D6): row-per-symbol or it is marketing.
//!
//! File format (`ci/PARITY_LEDGER.txt`, line-oriented, '#' comments):
//!
//! ```text
//! schema fln-parity-ledger/1
//! row <surface> | <symbol> | <kind> | <semantic-status> | <L-level> | <mode>
//!     | <oracle-kind> | <comparison-class> | <fixtures> | <determinism-class>
//!     | <claim-state> | <freshness>
//! ```
//!
//! Twelve '|'-separated fields on one line. `fixtures` is a comma-separated list of
//! repo-relative paths (validated to exist); `freshness` names the evidence run.
//! Aggregation reports counts per (surface, level) and per claim state — never a
//! single headline percentage.

use std::collections::BTreeMap;
use std::path::Path;

/// Per-surface evidence level (plan §4.2). Ordered: L0 recognized … L4 attested.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LLevel {
    L0,
    L1,
    L2,
    L3,
    L4,
}

impl LLevel {
    fn parse(s: &str) -> Option<LLevel> {
        Some(match s {
            "L0" => LLevel::L0,
            "L1" => LLevel::L1,
            "L2" => LLevel::L2,
            "L3" => LLevel::L3,
            "L4" => LLevel::L4,
            _ => return None,
        })
    }
}

/// The mode a row's evidence was gathered under (plan §4.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mode {
    Faithful,
    Sound,
    Frontier,
}

impl Mode {
    fn parse(s: &str) -> Option<Mode> {
        Some(match s {
            "faithful" => Mode::Faithful,
            "sound" => Mode::Sound,
            "frontier" => Mode::Frontier,
            _ => return None,
        })
    }
}

/// Determinism class (plan D7).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeterminismClass {
    D0,
    D1,
    D2,
    D3,
    D4,
}

impl DeterminismClass {
    fn parse(s: &str) -> Option<DeterminismClass> {
        Some(match s {
            "D0" => DeterminismClass::D0,
            "D1" => DeterminismClass::D1,
            "D2" => DeterminismClass::D2,
            "D3" => DeterminismClass::D3,
            "D4" => DeterminismClass::D4,
            _ => return None,
        })
    }
}

/// Claim state (plan B8/D7 vocabulary).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClaimState {
    Observed,
    Targeted,
    Hypothesis,
    Proven,
    Blocked,
}

impl ClaimState {
    fn parse(s: &str) -> Option<ClaimState> {
        Some(match s {
            "OBSERVED" => ClaimState::Observed,
            "TARGETED" => ClaimState::Targeted,
            "HYPOTHESIS" => ClaimState::Hypothesis,
            "PROVEN" => ClaimState::Proven,
            "BLOCKED" => ClaimState::Blocked,
            _ => return None,
        })
    }
}

/// One row per symbol. Free-text fields are validated non-empty; enumerated fields
/// are typed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row {
    /// 1-based source line in the ledger file, for error reporting.
    pub line: usize,
    pub surface: String,
    pub symbol: String,
    pub kind: String,
    pub semantic_status: String,
    pub level: LLevel,
    pub mode: Mode,
    pub oracle_kind: String,
    pub comparison_class: String,
    pub fixtures: Vec<String>,
    pub determinism: DeterminismClass,
    pub claim: ClaimState,
    pub freshness: String,
}

#[derive(Debug, Default)]
pub struct Ledger {
    pub rows: Vec<Row>,
}

/// Typed parse/validation failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LedgerError {
    pub line: usize,
    pub what: String,
}

impl std::fmt::Display for LedgerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PARITY_LEDGER.txt:{}: {}", self.line, self.what)
    }
}

pub fn parse(text: &str) -> Result<Ledger, LedgerError> {
    let mut ledger = Ledger::default();
    let mut saw_schema = false;
    for (idx, raw) in text.lines().enumerate() {
        let lineno = idx + 1;
        let line = match raw.find('#') {
            Some(pos) => &raw[..pos],
            None => raw,
        }
        .trim();
        if line.is_empty() {
            continue;
        }
        let err = |what: &str| LedgerError {
            line: lineno,
            what: what.to_string(),
        };
        if !saw_schema {
            if line == "schema fln-parity-ledger/1" {
                saw_schema = true;
                continue;
            }
            return Err(err("first directive must be `schema fln-parity-ledger/1`"));
        }
        let Some(rest) = line.strip_prefix("row ") else {
            return Err(err("expected `row <12 '|'-separated fields>`"));
        };
        let fields: Vec<&str> = rest.split('|').map(str::trim).collect();
        if fields.len() != 12 {
            return Err(LedgerError {
                line: lineno,
                what: format!("expected 12 fields, found {}", fields.len()),
            });
        }
        if fields.iter().any(|f| f.is_empty()) {
            return Err(err("every field must be non-empty"));
        }
        let row = Row {
            line: lineno,
            surface: fields[0].to_string(),
            symbol: fields[1].to_string(),
            kind: fields[2].to_string(),
            semantic_status: fields[3].to_string(),
            level: LLevel::parse(fields[4]).ok_or_else(|| err("L-level must be L0..L4"))?,
            mode: Mode::parse(fields[5])
                .ok_or_else(|| err("mode must be faithful|sound|frontier"))?,
            oracle_kind: fields[6].to_string(),
            comparison_class: fields[7].to_string(),
            fixtures: fields[8]
                .split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(str::to_string)
                .collect(),
            determinism: DeterminismClass::parse(fields[9])
                .ok_or_else(|| err("determinism class must be D0..D4"))?,
            claim: ClaimState::parse(fields[10]).ok_or_else(|| {
                err("claim state must be OBSERVED|TARGETED|HYPOTHESIS|PROVEN|BLOCKED")
            })?,
            freshness: fields[11].to_string(),
        };
        if row.fixtures.is_empty() && row.level > LLevel::L0 {
            return Err(err("a row above L0 must cite at least one fixture"));
        }
        if ledger
            .rows
            .iter()
            .any(|r| r.surface == row.surface && r.symbol == row.symbol && r.mode == row.mode)
        {
            return Err(err("duplicate (surface, symbol, mode) row"));
        }
        ledger.rows.push(row);
    }
    if !saw_schema {
        return Err(LedgerError {
            line: 0,
            what: "missing schema line".to_string(),
        });
    }
    Ok(ledger)
}

/// Oracle kinds under which somebody outside this repo **produced a value** that a row's
/// comparison ran against.
///
/// `pinned-source` is deliberately absent, and that absence is the whole law below. Reading
/// upstream's source tells you what the Reference is *written to do*; asking the pinned
/// binary tells you what it *does*. D8 makes the Reference the differential **oracle**, and
/// an oracle that is read rather than asked has been replaced by our reading of it. The
/// failure is silent by construction: source and built binary agree almost always, so a
/// source-read row is green right up until they diverge — which is precisely the class of
/// divergence the Tribunal exists to catch, arriving in the one place nothing is watching.
pub const VALUE_PRODUCING_ORACLES: [&str; 4] = [
    "pinned-binary",
    "spec-vectors",
    "multi-host-attestation",
    "certified-matrix",
];

/// A row asserts that somebody produced a value it compared against.
///
/// Extracted so the two laws that turn on this question cannot drift apart. Both
/// [`validate_repaired_rows_cite_their_oracle`] and
/// [`validate_freshness_names_the_oracle_it_claims`] fire exactly when a row has left the
/// declared remainder, and two hand-written copies of that predicate would be a join between
/// two rules with nothing watching it — this module's own defect class, one floor down.
fn claims_a_produced_value(row: &Row) -> bool {
    row.level > LLevel::L1 && VALUE_PRODUCING_ORACLES.contains(&row.oracle_kind.as_str())
}

/// The rows that break the law today, declared so that the FOURTEENTH cannot.
///
/// A declared remainder, not a silent one — the same discipline the concept censuses use in
/// [`crate::witness::CONCEPT_CENSUS`]. Landing the law as a bare assertion would fail the
/// build until thirteen published levels are re-earned or re-stated, and a gate that cannot
/// be green is a gate people learn to bypass (the `franken_lean-e5k7` lesson). Landing it
/// with a shrinking allowance stops the class from growing while its existing members are
/// triaged.
///
/// The list is checked in BOTH directions: an entry whose row no longer breaks the law is
/// itself a failure, so the remainder cannot quietly outlive the defect it records.
pub const SOURCE_READ_ABOVE_L1_ALLOWANCE: [&str; 0] = [];

/// The rig that gives each remainder row a value-producing oracle, so a REPAIRED row can be
/// required to name it.
///
/// This is the successor to [`SOURCE_READ_ABOVE_L1_ALLOWANCE`], and it exists because the
/// allowance-scoped guards have an end-of-life problem. `pin_option_defaults.rs` and
/// `pin_ctor_inventory.rs` each assert that every UNREPAIRED row in the remainder is backed
/// by them — correctly one-way, so that repairing a row cannot redden the build. But that
/// makes both guards go quiet exactly as the remainder empties, which is the moment those
/// rows stop being declared exceptions and become ordinary published L2 claims. A guard that
/// switches off when its subject becomes load-bearing is the `uagk` shape in AGENTS.md item 7:
/// a scan returning empty is a broken scan, not a clean tree.
///
/// So the two halves are complementary and the coverage is continuous:
///
/// | row state              | allowance guards       | this law                       |
/// |------------------------|------------------------|--------------------------------|
/// | in the remainder       | must be backed by rig  | silent (repair not yet claimed)|
/// | repaired, left it      | silent (by design)     | must CITE the rig it claims    |
///
/// mixHash is deliberately absent: its oracle is not a rig but the fixture
/// `core_observables.txt`, which it already cites, and which
/// `scripts/extract/gen_core_fixtures.sh` generates by running the pinned binary. Its repair
/// is a one-token `oracle_kind` edit with no fixture change, so this law has nothing to add.
pub const ORACLE_BACKING: [(&str, &str); 12] = [
    (
        "Lean.DataValue.ctorInventory",
        "crates/fln-conformance/tests/pin_ctor_inventory.rs",
    ),
    (
        "Lean.Expr.ctorInventory",
        "crates/fln-conformance/tests/pin_ctor_inventory.rs",
    ),
    (
        "Lean.Level.ctorInventory",
        "crates/fln-conformance/tests/pin_ctor_inventory.rs",
    ),
    (
        "Lean.Name.ctorInventory",
        "crates/fln-conformance/tests/pin_ctor_inventory.rs",
    ),
    (
        "exponentiation.threshold",
        "crates/fln-conformance/tests/pin_option_defaults.rs",
    ),
    (
        "maxErrors",
        "crates/fln-conformance/tests/pin_option_defaults.rs",
    ),
    (
        "maxHeartbeats",
        "crates/fln-conformance/tests/pin_option_defaults.rs",
    ),
    (
        "maxRecDepth",
        "crates/fln-conformance/tests/pin_option_defaults.rs",
    ),
    (
        "maxSynthPendingDepth",
        "crates/fln-conformance/tests/pin_option_defaults.rs",
    ),
    (
        "maxUniverseOffset",
        "crates/fln-conformance/tests/pin_option_defaults.rs",
    ),
    (
        "synthInstance.maxHeartbeats",
        "crates/fln-conformance/tests/pin_option_defaults.rs",
    ),
    (
        "synthInstance.maxSize",
        "crates/fln-conformance/tests/pin_option_defaults.rs",
    ),
];

/// A repaired row must cite the oracle it now claims.
///
/// LIVE, and the sentence that stood here said the opposite. It read "vacuous today by
/// construction — all twelve rows are still in the remainder", which was true when written
/// and was falsified by the qydn repair: measured at `efc5e730`, all twelve have LEFT the
/// remainder — every one is `L2` on `pinned-binary` — so this law examines all twelve and
/// admits them on merit, 12/12 citing their rig. It is not vacuous and has not been since
/// `8eb2f892`.
///
/// The design claim underneath survives and is why the correction matters: this law GAINS
/// force as the remainder shrinks, where the allowance-scoped guards lose it, so the two
/// together mean no row is unwatched in either state or in the transition. What nothing
/// watched was the transition ITSELF — a stale "vacuous" invites a reader to treat this law
/// as dead code, and the assertion in the suite could not tell the two worlds apart either.
/// [`SUCCESSOR_LAW_LIVE_FLOOR`] is the repair.
///
/// What it catches is the specific half-repair this bead makes easy. Every one of the twelve
/// currently cites `crates/fln-core/tests/pin_inventory_census.rs`, which READS vendored
/// upstream source. Flipping `oracle_kind` to `pinned-binary` while leaving that citation
/// alone produces a row asserting the binary was asked, evidenced by a test that only ever
/// read a file — the exact substitution of *our reading of the oracle* for *the oracle* that
/// the whole bead is about, and it would otherwise pass every check in this module.
///
/// It is not a wall against a correct repair: citing the rig is one path added to a field
/// that already lists evidence paths, which is the convention twelve of these rows already
/// follow. The failure message names the exact path to add.
pub fn validate_repaired_rows_cite_their_oracle(ledger: &Ledger) -> Result<(), Vec<LedgerError>> {
    let mut errors: Vec<LedgerError> = Vec::new();
    for (symbol, rig) in ORACLE_BACKING {
        // Absent rows are the orphan question, which lives in
        // `validate_allowance_has_no_orphans` and is a whole-file property.
        let Some(row) = ledger.rows.iter().find(|row| row.symbol == symbol) else {
            continue;
        };
        // "Repaired" is read off the ROW, not off the allowance const.
        //
        // Deriving it from the artifact rather than from a second list is the point: keying
        // this on `SOURCE_READ_ABOVE_L1_ALLOWANCE` would make the law depend on a join
        // between two constants staying in step, which is the defect class this bead is
        // about — and it would also make the law untestable, because no synthetic ledger can
        // shrink a compile-time const.
        //
        // A row claims a produced value exactly when its level is above L1 AND its
        // oracle-kind is one that produced one. Until then the repair has not been asserted
        // and there is nothing to require; the allowance-scoped guards own it.
        if !claims_a_produced_value(row) {
            continue;
        }
        if row.fixtures.iter().any(|fixture| fixture == rig) {
            continue;
        }
        errors.push(LedgerError {
            line: row.line,
            what: format!(
                "`{symbol}` has left the declared remainder — so it now claims {:?} on the \
                 strength of oracle-kind `{}` — but it does not cite the rig that produces \
                 that value. Add `{rig}` to its fixtures. Citing only a source-reading test \
                 for a binary-produced level is the substitution this bead exists to prevent: \
                 it reports our READING of the oracle under the name of the oracle.",
                row.level, row.oracle_kind
            ),
        });
    }
    errors.sort_by_key(|error| error.line);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// How many of [`ORACLE_BACKING`]'s symbols [`validate_repaired_rows_cite_their_oracle`]
/// actually REACHES rather than skips.
///
/// A FLOOR, deliberately not an equality, and the direction is forced. The population grows
/// only when a row is repaired out of the remainder — the event this module exists to
/// encourage — and equality would redden the build for a correct addition to
/// [`ORACLE_BACKING`]: a thirteenth symbol whose row is still unrepaired. It may never
/// shrink, because every way of shrinking it is a published claim being withdrawn or a repair
/// being reverted, and both must be deliberate rather than silent. That is the
/// shrinking-allowance direction this repository has already paid for twice.
///
/// Measured at `efc5e730`: 12 of 12.
pub const SUCCESSOR_LAW_LIVE_FLOOR: usize = 12;

/// The [`ORACLE_BACKING`] symbols the successor law examines rather than skips.
///
/// Exposed because the anti-vacuity floor cannot be written in the integration suite without
/// it, and re-deriving it there is the one repair that is not available.
/// [`claims_a_produced_value`] is private on purpose — the two laws that turn on it must not
/// drift apart — so a suite that answered "is this row under the law" for itself would plant
/// exactly the second copy that predicate was extracted to prevent. The module that owns the
/// predicate reports the population; the suite asserts against it and re-implements nothing.
pub fn rows_bound_by_the_successor_law(ledger: &Ledger) -> Vec<&'static str> {
    ORACLE_BACKING
        .iter()
        .filter(|(symbol, _rig)| {
            ledger
                .rows
                .iter()
                .any(|row| row.symbol == *symbol && claims_a_produced_value(row))
        })
        .map(|(symbol, _rig)| *symbol)
        .collect()
}

/// Every rig this law can require a citation to must exist.
///
/// Without this, renaming or deleting a rig turns [`ORACLE_BACKING`] into a demand that rows
/// cite a file nobody can open — a guard that fails in a direction no repair can satisfy.
/// Checked against the workspace root the same way [`validate_fixtures`] checks the ledger's
/// own citations.
pub fn validate_oracle_backing_paths_exist(root: &Path) -> Result<(), Vec<LedgerError>> {
    let mut errors: Vec<LedgerError> = Vec::new();
    for (symbol, rig) in ORACLE_BACKING {
        if !root.join(rig).exists() {
            errors.push(LedgerError {
                line: 0,
                what: format!(
                    "ORACLE_BACKING names `{rig}` as the oracle for `{symbol}`, and no such \
                     file exists. A repaired row cannot cite a rig that is not there — move \
                     the entry in the change that moved the rig."
                ),
            });
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// The disposition of the now-empty remainder, retained in failure output so a future
/// exception cannot obscure why the original thirteen left it.
pub const SOURCE_READ_ALLOWANCE_REASON: &str = "\
Bead fln-parity-ledger-l2-pinned-source-qydn is repaired and the declared remainder is empty. \
Eight option rows cite pin_option_defaults.rs and carry pin-option-defaults-v4.32.0; four \
ctorInventory rows cite pin_ctor_inventory.rs and carry pin-ctor-inventory-v4.32.0; mixHash \
cites the binary-produced core_observables.txt fixture and carries its existing \
core-observables-v4.32.0 tag. All thirteen now say pinned-binary. A future exception must \
name its own evidence and justification rather than inheriting this closed remainder.";

/// Every way a row's level outruns the oracle that backs it, reported together and in file
/// order so the result is a diffable artifact rather than whichever one was hit first.
///
/// Two distinct failures, kept apart because they have opposite repairs: a row that breaks
/// the law without being declared, and a declared row that no longer breaks it.
pub fn validate_level_is_supported_by_its_oracle(ledger: &Ledger) -> Result<(), Vec<LedgerError>> {
    validate_level_is_supported_by_its_oracle_against(ledger, &SOURCE_READ_ABOVE_L1_ALLOWANCE)
}

/// The oracle-support law over an explicit allowance.
///
/// Public only so the integration suite can keep planting stale allowance entries after the
/// real remainder reaches zero. Production validation always calls
/// [`validate_level_is_supported_by_its_oracle`], which binds this to the canonical allowance.
#[doc(hidden)]
pub fn validate_level_is_supported_by_its_oracle_against(
    ledger: &Ledger,
    allowance: &[&str],
) -> Result<(), Vec<LedgerError>> {
    let breaks_law = |row: &Row| row.level > LLevel::L1 && !claims_a_produced_value(row);
    let mut errors: Vec<LedgerError> = Vec::new();

    for row in &ledger.rows {
        if breaks_law(row) && !allowance.contains(&row.symbol.as_str()) {
            errors.push(LedgerError {
                line: row.line,
                what: format!(
                    "`{}` claims {:?} with oracle-kind `{}`, which produced no value to \
                     compare against. Levels above L1 require an oracle that was ASKED, not \
                     read: {:?}. Either earn the level against one of those, or state the \
                     level the evidence supports. If this row is a known exception, it must \
                     join SOURCE_READ_ABOVE_L1_ALLOWANCE with a reason — the remainder is \
                     declared, never silent.",
                    row.symbol, row.level, row.oracle_kind, VALUE_PRODUCING_ORACLES
                ),
            });
        }
    }

    for symbol in allowance {
        // Rows absent from this slice are the orphan question, which is a whole-file
        // property and lives in `validate_allowance_has_no_orphans`.
        let Some(row) = ledger.rows.iter().find(|row| row.symbol == *symbol) else {
            continue;
        };
        if breaks_law(row) {
            continue;
        }
        errors.push(LedgerError {
            line: row.line,
            what: format!(
                "`{symbol}` no longer breaks the oracle-supports-level law (it is now {:?} via \
                 `{}`), so its entry in SOURCE_READ_ABOVE_L1_ALLOWANCE is stale. Shrink the \
                 allowance in the same change that repaired the row — a remainder that does \
                 not shrink stops being a record of work outstanding.",
                row.level, row.oracle_kind
            ),
        });
    }

    errors.sort_by_key(|error| error.line);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// Every declared exception must name a row that exists.
///
/// Split from the law itself because the two have different SCOPES, and conflating them
/// made the law unusable on any subset of the ledger — which is how the planted permission
/// case caught this. The law is a per-row property and holds on any slice; orphan detection
/// is a property of the whole file and is meaningful only against it.
///
/// An allowance that outlives its row is a grandfather clause: the next row to take that
/// symbol would silently inherit an exemption nobody granted it.
pub fn validate_allowance_has_no_orphans(ledger: &Ledger) -> Result<(), Vec<LedgerError>> {
    validate_allowance_has_no_orphans_against(ledger, &SOURCE_READ_ABOVE_L1_ALLOWANCE)
}

/// The orphan half over an explicit allowance, for a permanent planted case after closure.
#[doc(hidden)]
pub fn validate_allowance_has_no_orphans_against(
    ledger: &Ledger,
    allowance: &[&str],
) -> Result<(), Vec<LedgerError>> {
    let orphans: Vec<LedgerError> = allowance
        .iter()
        .filter(|symbol| !ledger.rows.iter().any(|row| &row.symbol == *symbol))
        .map(|symbol| LedgerError {
            line: 0,
            what: format!(
                "SOURCE_READ_ABOVE_L1_ALLOWANCE lists `{symbol}`, which is not a row in this \
                 ledger. Remove it in the change that removed the row."
            ),
        })
        .collect();
    if orphans.is_empty() {
        Ok(())
    } else {
        Err(orphans)
    }
}

/// Freshness tags that name a run which only READ the pin, never asked it.
///
/// The ledger's header calls `freshness` "the evidence run", and the tags bear that out: each
/// names a *run* by prefix and the pin epoch by suffix (`core-observables-` / `pin-census-` /
/// `core-ext-observables-`, all at `v4.32.0`). So the tag encodes the same provenance fact
/// that `oracle_kind` does — and until this law it was the one field of the twelve that was
/// parsed into a typed field and never compared to anything, which is verbatim the defect
/// this bead opened with about `level` and `oracle_kind`.
///
/// A DENYLIST, not an allowlist. TWO reasons were given for that direction and only the
/// SECOND still holds; both are named because a reader cannot otherwise tell which one is
/// load-bearing, and a justification resting on a false premise is worse than one resting on
/// a narrow premise.
///
/// EXPIRED — "repairing the twelve requires a tag that does not exist yet (both pin rigs are
/// deliberately fixture-less, so their run has no tag today)". True when written at
/// `3208f099` (2026-07-26 12:27:40) and falsified 31 minutes later by `8eb2f892`, which
/// repaired the thirteen rows and created exactly those tags: measured at `efc5e730`,
/// `pin-option-defaults-v4.32.0` sits on 8 rows and `pin-ctor-inventory-v4.32.0` on 4. That
/// commit edited THIS doc block — it rewrote the `pin-census-v4.32.0` paragraph below for the
/// new state — and left this paragraph asserting the old one.
///
/// STANDS — a new honest tag must pass without asking anyone's permission, and a known
/// source-reading tag must not. The permission test
/// `source_read_at_l1_and_value_produced_above_it_are_both_permitted` exercises `rfc-vectors`,
/// which still appears nowhere in the real ledger: re-measured at `efc5e730`, 0 occurrences.
///
/// So the conclusion survives and one of its two supports does not. This is NOT the repair
/// bead `fln-parity-freshness-denylist-direction-dy22` asks for — that bead's finding is that
/// this denylist classifies 0 of 85 produced-value rows, and its proposed repair is a DERIVED
/// tag-to-rig binding rather than a hand-maintained allowlist, which the now-existing tags
/// make cheaper than when it was filed. Correcting a justification does not perform a repair;
/// dy22 stays open.
///
/// `unit-suite-v4.32.0` and `inventory-v4.32.0` sit on L1/L0 rows today, where the law never
/// reaches them. They are declared anyway, so that raising one of those rows without moving
/// its tag is caught at the moment it happens rather than becoming instance ten.
///
/// `pin-census-v4.32.0` no longer appears on a real row after qydn, but stays here
/// permanently. This is a denylist of provenance facts, not an allowance: removing a retired
/// tag would let a later produced-value row reuse a run already known to have read only source.
pub const SOURCE_READING_FRESHNESS_TAGS: [&str; 3] = [
    "inventory-v4.32.0",
    "pin-census-v4.32.0",
    "unit-suite-v4.32.0",
];

/// A row that claims a produced value may not name a source-reading run as its evidence.
///
/// THE GAP THIS CLOSES, which is a two-field repair passing every existing check. Repairing
/// one of the twelve means moving three fields: `oracle_kind` to `pinned-binary`, `fixtures`
/// to cite the rig, and `freshness` to name the rig's run. The oracle law watches the first,
/// [`validate_repaired_rows_cite_their_oracle`] watches the second, and nothing watched the
/// third. A row flipped to `pinned-binary` and citing `pin_option_defaults.rs` while still
/// tagged `pin-census-v4.32.0` was fully green, with its stated evidence run naming the
/// source-reading census as the provenance of a binary-produced level.
///
/// Read entirely off the ROW, for the reason cc_3 recorded when they made the successor law
/// row-derived: keying it on a second constant would make the law depend on a join between
/// two lists staying in step, and would make it untestable, because no synthetic ledger can
/// shrink a compile-time const.
///
/// Scoped by exactly [`claims_a_produced_value`], so the coverage hands off cleanly rather
/// than overlapping: while a row is still at `pinned-source` the oracle law owns it and this
/// one is silent; the instant it claims a produced value this one takes over. The handoff is
/// the transition the gap lived in.
pub fn validate_freshness_names_the_oracle_it_claims(
    ledger: &Ledger,
) -> Result<(), Vec<LedgerError>> {
    let mut errors: Vec<LedgerError> = Vec::new();
    for row in &ledger.rows {
        if !claims_a_produced_value(row) {
            continue;
        }
        if !SOURCE_READING_FRESHNESS_TAGS.contains(&row.freshness.as_str()) {
            continue;
        }
        errors.push(LedgerError {
            line: row.line,
            what: format!(
                "`{}` claims {:?} on oracle-kind `{}`, but its freshness tag `{}` names a run \
                 that only READ the pin. The ledger's header defines freshness as the evidence \
                 run, so this row reports a binary-produced level whose evidence run is a \
                 source reader — our READING of the oracle under the name of the oracle, which \
                 is the substitution this bead exists to prevent. Repairing a row moves THREE \
                 fields: oracle-kind, fixtures, and this one. Give it a tag naming the run that \
                 produced the value.",
                row.symbol, row.level, row.oracle_kind, row.freshness
            ),
        });
    }
    errors.sort_by_key(|error| error.line);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// Validate fixture references against the workspace root: every cited fixture must
/// exist, and must be CONFINED to the workspace. A ledger citing a missing fixture is
/// marketing, not evidence — and one citing `/etc/hostname` or `../../anything` is
/// citing evidence the repository does not contain, which is worse, because it exists
/// and so used to pass (bead `fln-euo`; RubyForest's 2026-07-22 15:04 finding, live
/// until this line: `root.join(fixture)` hands an ABSOLUTE fixture path straight back,
/// and walks wherever `..` points).
///
/// Confinement is lexical: no absolute paths, no `..` components, no drive/root
/// prefixes. A symlink inside the tree pointing out is beyond a lexical check and is
/// deliberately out of scope here — ledger fixtures are tracked repository files, and
/// the tracked-tree guards own that class.
pub fn validate_fixtures(ledger: &Ledger, root: &Path) -> Result<(), LedgerError> {
    for row in &ledger.rows {
        for fixture in &row.fixtures {
            let cited = Path::new(fixture);
            let escapes = cited.is_absolute()
                || cited.components().any(|c| {
                    matches!(
                        c,
                        std::path::Component::ParentDir
                            | std::path::Component::RootDir
                            | std::path::Component::Prefix(_)
                    )
                });
            if escapes {
                return Err(LedgerError {
                    line: row.line,
                    what: format!(
                        "row for `{}` cites fixture `{fixture}` outside the workspace \
                         (absolute or parent-traversing paths cannot be evidence here)",
                        row.symbol
                    ),
                });
            }
            if !root.join(fixture).exists() {
                return Err(LedgerError {
                    line: row.line,
                    what: format!("row for `{}` cites missing fixture `{fixture}`", row.symbol),
                });
            }
        }
    }
    Ok(())
}

/// The aggregate view (never a single percentage): counts keyed by (surface, level)
/// and by claim state.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Aggregate {
    pub by_surface_level: BTreeMap<(String, LLevel), usize>,
    pub by_claim: BTreeMap<ClaimState, usize>,
    pub total_rows: usize,
}

pub fn aggregate(ledger: &Ledger) -> Aggregate {
    let mut agg = Aggregate {
        total_rows: ledger.rows.len(),
        ..Aggregate::default()
    };
    for row in &ledger.rows {
        *agg.by_surface_level
            .entry((row.surface.clone(), row.level))
            .or_insert(0) += 1;
        *agg.by_claim.entry(row.claim).or_insert(0) += 1;
    }
    agg
}

#[cfg(test)]
mod tests {
    use super::*;

    const OK: &str = "schema fln-parity-ledger/1\n\
        row meta-api | Lean.Name.hash | function | native | L2 | faithful | pinned-binary | exact | crates/fln-conformance/fixtures/core_observables.txt | D0 | OBSERVED | core-observables-v4.32.0\n";

    #[test]
    fn parses_and_aggregates() {
        let ledger = parse(OK).expect("parses");
        assert_eq!(ledger.rows.len(), 1);
        let row = &ledger.rows[0];
        assert_eq!(row.level, LLevel::L2);
        assert_eq!(row.claim, ClaimState::Observed);
        assert_eq!(row.determinism, DeterminismClass::D0);
        let agg = aggregate(&ledger);
        assert_eq!(agg.total_rows, 1);
        assert_eq!(
            agg.by_surface_level[&("meta-api".to_string(), LLevel::L2)],
            1
        );
        assert_eq!(agg.by_claim[&ClaimState::Observed], 1);
    }

    #[test]
    fn rejects_malformed_rows() {
        assert!(parse("row a | b\n").is_err(), "schema line required");
        let short = "schema fln-parity-ledger/1\nrow a | b | c\n";
        assert!(parse(short).is_err());
        let bad_level = OK.replace("| L2 |", "| L9 |");
        assert!(parse(&bad_level).is_err());
        let bad_claim = OK.replace("OBSERVED", "MAYBE");
        assert!(parse(&bad_claim).is_err());
        let empty_field = OK.replace("faithful", " ");
        assert!(parse(&empty_field).is_err());
        let dup = format!("{OK}{}", &OK["schema fln-parity-ledger/1\n".len()..]);
        assert!(parse(&dup).is_err(), "duplicate (surface,symbol,mode)");
    }

    #[test]
    fn a_row_above_l0_requires_fixtures() {
        let no_fixture = OK.replace("crates/fln-conformance/fixtures/core_observables.txt", ",");
        assert!(parse(&no_fixture).is_err());
        // L0 rows may cite none: `,` is the explicit none marker for the fixtures
        // field (recognized-only inventory entries).
        let l0 = OK
            .replace("| L2 |", "| L0 |")
            .replace("crates/fln-conformance/fixtures/core_observables.txt", ",");
        let parsed = parse(&l0).expect("L0 rows may cite no fixtures");
        assert!(parsed.rows[0].fixtures.is_empty());
    }

    #[test]
    fn fixture_validation_checks_the_filesystem() {
        let ledger = parse(OK).expect("parses");
        let root = crate::checked_workspace_root!();
        validate_fixtures(&ledger, &root).expect("fixture exists");
        let ghost = OK.replace(
            "crates/fln-conformance/fixtures/core_observables.txt",
            "crates/fln-conformance/fixtures/ghost.txt",
        );
        let bad = parse(&ghost).expect("parses");
        let err = validate_fixtures(&bad, &root).expect_err("ghost fixture rejected");
        assert_eq!(err.line, 2, "reports the row's source line, not its index");
    }

    #[test]
    fn a_fixture_outside_the_workspace_is_refused_even_when_it_exists() {
        // RubyForest's 2026-07-22 finding, previously live: `root.join(fixture)` hands
        // an absolute path straight back, so `/etc/hostname` EXISTED and therefore
        // PASSED — a ledger row resting on evidence the repository does not contain.
        // Both escape shapes, each against a target that genuinely exists, because a
        // refusal proven only against missing files is the existence check wearing a
        // confinement check's name.
        let root = crate::checked_workspace_root!();
        for escape in ["/etc/hostname", "../../../../etc/hostname"] {
            let escaped = OK.replace(
                "crates/fln-conformance/fixtures/core_observables.txt",
                escape,
            );
            let bad = parse(&escaped).expect("parses");
            let err = validate_fixtures(&bad, &root)
                .expect_err("an escaping fixture citation must be refused");
            assert!(
                err.what.contains("outside the workspace"),
                "the refusal must name confinement, not existence: {}",
                err.what
            );
        }
        // The control that keeps the fence from widening into a wall: the honest
        // repo-relative citation still validates.
        let ledger = parse(OK).expect("parses");
        validate_fixtures(&ledger, &root).expect("a confined existing fixture still passes");
    }
}
