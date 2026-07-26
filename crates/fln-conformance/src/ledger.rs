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
pub const SOURCE_READ_ABOVE_L1_ALLOWANCE: [&str; 13] = [
    "Lean.DataValue.ctorInventory",
    "Lean.Expr.ctorInventory",
    "Lean.Level.ctorInventory",
    "Lean.Name.ctorInventory",
    "exponentiation.threshold",
    "maxErrors",
    "maxHeartbeats",
    "maxRecDepth",
    "maxSynthPendingDepth",
    "maxUniverseOffset",
    "mixHash",
    "synthInstance.maxHeartbeats",
    "synthInstance.maxSize",
];

/// Why each group is still in the remainder, so the list is reviewable rather than a
/// grandfather clause nobody can shrink.
pub const SOURCE_READ_ALLOWANCE_REASON: &str = "\
Bead fln-parity-ledger-l2-pinned-source-qydn. Thirteen rows carry L2 with oracle-kind \
pinned-source, which the ledger's own tier note defines as L1 (`no Reference-produced value \
is compared'). Three groups, three different repairs:\n\
  * The eight option defaults now HAVE a value-producing oracle — \
crates/fln-conformance/tests/pin_option_defaults.rs asks the pinned binary for its \
registered option table on every run and compares all eight. What remains is the row edit \
itself, in ci/PARITY_LEDGER.txt, which is cod_2's artifact.\n\
  * The four ctorInventory rows now HAVE one too — \
crates/fln-conformance/tests/pin_ctor_inventory.rs asks the pinned binary's environment for \
each inductive's `ctors` list and compares all six inventories (33 constructors) in \
declaration order on every run. The route this bead recorded as `plausible and untried' is \
`Lean.Environment.find?' on an unpatched pin, and it is now tried. What remains is again the \
row edit, in cod_2's artifact.\n\
  * mixHash is not a level question at all: its oracle-kind says pinned-source while its \
cited fixture is crates/fln-conformance/fixtures/core_observables.txt. That fixture is \
generated by scripts/extract/gen_core_fixtures.sh, which runs the PINNED BINARY over \
gen_core_fixtures.lean after verifying its commit against SUITE.lock, and every value in it \
is computed by that binary. So the fixture is binary-produced, the level L2 is right, and \
the field that is wrong is the oracle-kind: it should read pinned-binary. That is a \
one-token row edit, and it is also cod_2's.";

/// Every way a row's level outruns the oracle that backs it, reported together and in file
/// order so the result is a diffable artifact rather than whichever one was hit first.
///
/// Two distinct failures, kept apart because they have opposite repairs: a row that breaks
/// the law without being declared, and a declared row that no longer breaks it.
pub fn validate_level_is_supported_by_its_oracle(ledger: &Ledger) -> Result<(), Vec<LedgerError>> {
    let breaks_law = |row: &Row| {
        row.level > LLevel::L1 && !VALUE_PRODUCING_ORACLES.contains(&row.oracle_kind.as_str())
    };
    let mut errors: Vec<LedgerError> = Vec::new();

    for row in &ledger.rows {
        if breaks_law(row) && !SOURCE_READ_ABOVE_L1_ALLOWANCE.contains(&row.symbol.as_str()) {
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

    for symbol in SOURCE_READ_ABOVE_L1_ALLOWANCE {
        // Rows absent from this slice are the orphan question, which is a whole-file
        // property and lives in `validate_allowance_has_no_orphans`.
        let Some(row) = ledger.rows.iter().find(|row| row.symbol == symbol) else {
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
    let orphans: Vec<LedgerError> = SOURCE_READ_ABOVE_L1_ALLOWANCE
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

/// Validate fixture references against the workspace root: every cited fixture must
/// exist. A ledger citing a missing fixture is marketing, not evidence.
pub fn validate_fixtures(ledger: &Ledger, root: &Path) -> Result<(), LedgerError> {
    for row in &ledger.rows {
        for fixture in &row.fixtures {
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
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("workspace root");
        validate_fixtures(&ledger, root).expect("fixture exists");
        let ghost = OK.replace(
            "crates/fln-conformance/fixtures/core_observables.txt",
            "crates/fln-conformance/fixtures/ghost.txt",
        );
        let bad = parse(&ghost).expect("parses");
        let err = validate_fixtures(&bad, root).expect_err("ghost fixture rejected");
        assert_eq!(err.line, 2, "reports the row's source line, not its index");
    }
}
