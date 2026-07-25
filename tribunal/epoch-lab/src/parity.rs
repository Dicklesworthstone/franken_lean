//! The Parity Ledger schema (bead `franken_lean-9pnc`, carved out of `fln-euo`;
//! plan §18, doctrine D7).
//!
//! # The governing sentence
//!
//! **The Parity Ledger is row-per-symbol or it is marketing.**
//!
//! That is doctrine (D7), not a preference, and it decides the shape of this
//! module. A row is about ONE symbol. It cannot exist without naming a real
//! fixture, exact roots, the oracle that produced the observation, the class of
//! comparison performed, its D7 claim type, its evidence state, its L-level,
//! mode and platform, its stated limitations, and its freshness. Absence is a
//! refusal, not a default — there is no `Option` in [`ParityRow`] and no
//! `Default` impl, so a row that omits a field does not parse.
//!
//! # This is the first consumer of the closed vocabularies
//!
//! Oracle kind, comparison class, normalizer id/version, D7 claim type,
//! evidence kind/state, L-level, mode, platform and freshness all come from
//! [`crate::oracle`] and [`crate::normalize`] unchanged. A schema that puts them
//! side by side is exactly where conflation would happen, so the three that are
//! most often confused for one another — **claim type, evidence state, and
//! L-level** — stay three separate fields, and none is derived from, defaulted
//! from, or substituted for another. [`ParityRow`] has no constructor that
//! computes one from another, and the verifier's refusals read each one for its
//! own purpose only.
//!
//! # Blocking conditions are refusals, not lint
//!
//! The seven conditions the epic names each get their own [`Block`] variant, so
//! each fails for ITS OWN reason and a mutant that breaks one cannot be caught
//! by a generic "something is wrong" check:
//!
//! | condition | variant |
//! |---|---|
//! | missing | [`Block::MissingSymbol`] |
//! | duplicate | [`Block::DuplicateRow`] |
//! | stale | [`Block::StaleRevision`] |
//! | unknown | [`Block::UnknownSymbol`] |
//! | root-mismatched | [`Block::RootMismatch`] |
//! | mock-only | [`Block::MockOnlyClosure`] |
//! | overclaimed | [`Block::OverclaimedLevel`], [`Block::OverclaimedClaim`] |
//!
//! [`verify`] returns every block it finds rather than the first, because a
//! ledger with four problems should report four, and it BLOCKS on any non-empty
//! result. There is no warning level: the epic's acceptance criteria are the
//! blocking conditions.
//!
//! # Two things this schema refuses to represent
//!
//! **No aggregates and no percentages.** A headline number is never evidence
//! under D7. This is enforced twice: structurally, because no field can hold
//! one, and by [`Block::AggregateRow`], which refuses a symbol shaped like a
//! total or a percentage — so the prohibition survives someone adding a numeric
//! field later without thinking about it. `report` deliberately emits counts of
//! *blocks* and never a parity score.
//!
//! **No mock-backed row closes an L-level.** A mock may support a unit test and
//! may not close a public claim. [`Backing`] is its own closed vocabulary and
//! not a variant of [`EvidenceKind`], because whether a run was backed by the
//! real Reference is a property of the RUN, not of the kind of evidence — and
//! folding it into `EvidenceKind` is exactly the conflation this epic keeps
//! warning about.

use crate::normalize::{NormalizerId, NormalizerVersion};
use crate::oracle::{
    ClaimType, ComparisonClass, EvidenceKind, EvidenceState, Freshness, LLevel, Mode, OracleKind,
    Platform,
};
use std::collections::{BTreeMap, HashMap, HashSet};

/// Schema line. Versioned: a change to what a row must name registers a NEW
/// schema rather than reinterpreting rows already recorded under the old one.
pub const LEDGER_SCHEMA: &str = "fln-parity-ledger/1";

/// What actually backed a run. Its own closed vocabulary — see the module note.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Backing {
    /// A real pinned Reference process produced the oracle side.
    RealReference,
    /// A committed artifact from a real Reference run.
    RealArtifact,
    /// A mock, stub, or hand-written expectation. May support a unit test; may
    /// not close a public claim.
    Mock,
}

impl Backing {
    fn parse(s: &str) -> Option<Backing> {
        match s {
            "real-reference" => Some(Backing::RealReference),
            "real-artifact" => Some(Backing::RealArtifact),
            "mock" => Some(Backing::Mock),
            _ => None,
        }
    }
}

/// Which normalizer touched the bytes, if any.
///
/// `None` is a *declared* absence, spelled `-` in the file, not a missing field:
/// a byte-identical comparison names no normalizer and must say so.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NormalizerRef {
    pub id: NormalizerId,
    pub version: NormalizerVersion,
}

/// A content digest as it appears in the ledger, or a declared absence.
///
/// `Absent` is spelled `-` and means "no artifact digest was compared", which is
/// a claim the comparison class has to agree with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Root {
    Digest(String),
    Absent,
}

/// One row. One symbol. Every field required.
///
/// No `Option`, no `Default`, and no constructor that derives one field from
/// another. Claim type, evidence state and L-level are three separate fields
/// and stay that way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParityRow {
    /// The one symbol this row is about.
    pub symbol: String,
    /// A real fixture this row was produced from.
    pub fixture: String,
    /// That fixture's content digest, so "a real fixture" is checkable and not
    /// merely a path someone typed.
    pub fixture_digest: String,
    /// Our artifact's root.
    pub ours_root: Root,
    /// The oracle's artifact root.
    pub oracle_root: Root,
    pub oracle: OracleKind,
    pub comparison: ComparisonClass,
    pub normalizer: Option<NormalizerRef>,
    /// D7 claim type. Never derived from `state` or `level`.
    pub claim: ClaimType,
    pub evidence: EvidenceKind,
    /// Evidence state. Never derived from `claim` or `level`.
    pub state: EvidenceState,
    /// Per-surface compatibility level. Never derived from `claim` or `state`.
    pub level: LLevel,
    pub mode: Mode,
    pub platform: Platform,
    pub backing: Backing,
    pub freshness: Freshness,
    /// Stated limitations. Required and non-empty: a row with nothing to say
    /// must write `no-known-limitations` explicitly, so silence is an assertion
    /// somebody made rather than a field somebody forgot.
    pub limits: String,
}

/// The key a row is unique under. Deliberately three fields: the same symbol
/// legitimately has different results per platform and per mode, and collapsing
/// those would either hide a real row or manufacture a false duplicate.
///
/// `Hash`, not `Ord`: neither [`Platform`] nor [`Mode`] is an ordered
/// vocabulary, and deriving `Ord` here would have meant giving them an ordering
/// they must not have just to satisfy a container.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RowKey {
    pub symbol: String,
    pub platform: Platform,
    pub mode: Mode,
}

/// A parsed ledger.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ledger {
    pub epoch: String,
    /// The epoch-lab revision root this ledger was published against. Freshness
    /// is checked against the chain head, so a ledger cannot quietly describe a
    /// manifest that has since been revised.
    pub revision: String,
    pub rows: Vec<ParityRow>,
}

/// Why a ledger is refused. Every variant blocks; there is no warning level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Block {
    /// The file is not a ledger at all.
    BadSchema { found: String },
    /// A line that is not a well-formed row.
    Malformed { line: usize, reason: String },
    /// An expected symbol has no row.
    MissingSymbol { symbol: String },
    /// Two rows share a symbol/platform/mode key.
    DuplicateRow { key: RowKey },
    /// The ledger names a revision that is not the chain head.
    StaleRevision { stated: String, head: String },
    /// A row for a symbol outside the expected set.
    UnknownSymbol { symbol: String },
    /// The stated roots contradict the declared comparison class.
    RootMismatch { symbol: String, detail: String },
    /// A mock-backed row closing an L-level.
    MockOnlyClosure { symbol: String, level: LLevel },
    /// A level the evidence state does not support.
    OverclaimedLevel {
        symbol: String,
        state: EvidenceState,
        level: LLevel,
    },
    /// A claim the evidence state does not support.
    OverclaimedClaim {
        symbol: String,
        state: EvidenceState,
        claim: ClaimType,
    },
    /// A row that is a total, an average, or a percentage rather than a symbol.
    AggregateRow { symbol: String },
    /// A comparison class and a normalizer declaration that disagree.
    IncoherentComparison { symbol: String, detail: String },
    /// The row's fixture does not exist, or does not hash to the stated digest.
    ///
    /// Until `fln-8fwh` the schema could refuse a row that OMITTED a fixture and
    /// not one that INVENTED one: `fixture_digest` was checked for shape and
    /// never for truth. This is that refusal.
    FixtureUnverified { symbol: String, detail: String },
}

impl Block {
    /// A stable machine token naming the reason. One token per variant, so a
    /// gate can assert WHICH refusal fired rather than merely that one did.
    pub fn reason(&self) -> &'static str {
        match self {
            Block::BadSchema { .. } => "bad-schema",
            Block::Malformed { .. } => "malformed",
            Block::MissingSymbol { .. } => "missing",
            Block::DuplicateRow { .. } => "duplicate",
            Block::StaleRevision { .. } => "stale",
            Block::UnknownSymbol { .. } => "unknown",
            Block::RootMismatch { .. } => "root-mismatch",
            Block::MockOnlyClosure { .. } => "mock-only",
            Block::OverclaimedLevel { .. } => "overclaimed-level",
            Block::OverclaimedClaim { .. } => "overclaimed-claim",
            Block::AggregateRow { .. } => "aggregate",
            Block::IncoherentComparison { .. } => "incoherent-comparison",
            Block::FixtureUnverified { .. } => "fixture-unverified",
        }
    }
}

/// The exact field order a row must use, after the symbol.
///
/// Fixed order makes the file diffable and a reordered row a refusal rather than
/// a silent acceptance. Note what is NOT here: no count, no total, no
/// percentage, no score. `no_field_can_hold_an_aggregate` walks this list.
pub const ROW_FIELDS: &[&str] = &[
    "fixture",
    "fixture_digest",
    "ours_root",
    "oracle_root",
    "oracle",
    "comparison",
    "normalizer",
    "claim",
    "evidence",
    "state",
    "level",
    "mode",
    "platform",
    "backing",
    "freshness",
    "limits",
];

fn parse_root(s: &str) -> Option<Root> {
    if s == "-" {
        return Some(Root::Absent);
    }
    let ok = s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit());
    ok.then(|| Root::Digest(s.to_string()))
}

fn parse_oracle(s: &str) -> Option<OracleKind> {
    match s {
        "reference-binary" => Some(OracleKind::ReferenceBinary),
        "reference-checker" => Some(OracleKind::ReferenceChecker),
        "pinned-artifact" => Some(OracleKind::PinnedArtifact),
        "epoch-transcript" => Some(OracleKind::EpochTranscript),
        _ => None,
    }
}

fn parse_comparison(s: &str) -> Option<ComparisonClass> {
    match s {
        "byte-identical" => Some(ComparisonClass::ByteIdentical),
        "normalized-identical" => Some(ComparisonClass::NormalizedIdentical),
        "acceptance-only" => Some(ComparisonClass::AcceptanceOnly),
        "diagnostic-equivalent" => Some(ComparisonClass::DiagnosticEquivalent),
        _ => None,
    }
}

fn parse_normalizer(s: &str) -> Option<Option<NormalizerRef>> {
    if s == "-" {
        return Some(None);
    }
    let (id, version) = s.split_once('/')?;
    let id = match id {
        "diagnostic-text" => NormalizerId::DiagnosticText,
        _ => return None,
    };
    let version = version.parse::<u32>().ok()?;
    Some(Some(NormalizerRef {
        id,
        version: NormalizerVersion(version),
    }))
}

fn parse_claim(s: &str) -> Option<ClaimType> {
    match s {
        "invariant" => Some(ClaimType::Invariant),
        "proof" => Some(ClaimType::Proof),
        "bounded_model" => Some(ClaimType::BoundedModel),
        "statistical" => Some(ClaimType::Statistical),
        "slo" => Some(ClaimType::Slo),
        "benchmark" => Some(ClaimType::Benchmark),
        _ => None,
    }
}

fn parse_evidence(s: &str) -> Option<EvidenceKind> {
    match s {
        "unit_test" => Some(EvidenceKind::UnitTest),
        "property_test" => Some(EvidenceKind::PropertyTest),
        "mutation_kill" => Some(EvidenceKind::MutationKill),
        "differential" => Some(EvidenceKind::Differential),
        "no_mock_e2e" => Some(EvidenceKind::NoMockE2E),
        _ => None,
    }
}

fn parse_state(s: &str) -> Option<EvidenceState> {
    match s {
        "observed" => Some(EvidenceState::Observed),
        "targeted" => Some(EvidenceState::Targeted),
        "hypothesis" => Some(EvidenceState::Hypothesis),
        "proven" => Some(EvidenceState::Proven),
        "blocked" => Some(EvidenceState::Blocked),
        _ => None,
    }
}

fn parse_level(s: &str) -> Option<LLevel> {
    match s {
        "L0" => Some(LLevel::L0),
        "L1" => Some(LLevel::L1),
        "L2" => Some(LLevel::L2),
        "L3" => Some(LLevel::L3),
        "L4" => Some(LLevel::L4),
        _ => None,
    }
}

fn parse_mode(s: &str) -> Option<Mode> {
    match s {
        "faithful" => Some(Mode::Faithful),
        "sound" => Some(Mode::Sound),
        "frontier" => Some(Mode::Frontier),
        _ => None,
    }
}

fn parse_platform(s: &str) -> Option<Platform> {
    match s {
        "linux-x86_64" => Some(Platform::LinuxX86_64),
        "macos-aarch64" => Some(Platform::MacOSAarch64),
        "windows-x86_64" => Some(Platform::WindowsX86_64),
        _ => None,
    }
}

fn parse_freshness(s: &str) -> Option<Freshness> {
    match s {
        "current" => Some(Freshness::Current),
        "stale" => Some(Freshness::Stale),
        "absent" => Some(Freshness::Absent),
        _ => None,
    }
}

/// Whether a symbol is really an aggregate wearing a symbol's clothes.
///
/// A headline number is never evidence under D7, so a "row" that summarises
/// many symbols is not a row. Checked on the SYMBOL because that is where an
/// aggregate would have to hide once the struct has no numeric field to put it
/// in.
pub fn is_aggregate_symbol(symbol: &str) -> bool {
    let upper = symbol.to_ascii_uppercase();
    if symbol.contains('*') || symbol.contains('%') {
        return true;
    }
    const AGGREGATE_WORDS: &[&str] = &[
        "TOTAL",
        "TOTALS",
        "ALL",
        "SUMMARY",
        "AVERAGE",
        "MEAN",
        "OVERALL",
        "AGGREGATE",
        "PERCENT",
        "PERCENTAGE",
        "SCORE",
    ];
    if AGGREGATE_WORDS.contains(&upper.as_str()) {
        return true;
    }
    // A bare number, or a number with a unit, is a measurement and not a symbol.
    symbol
        .trim_end_matches(|c: char| c.is_ascii_alphabetic())
        .parse::<f64>()
        .is_ok()
}

/// Parse a ledger. Total: hostile input yields [`Block`]s, never a panic.
///
/// Every field is required and the order is fixed, so a row that omits, repeats,
/// reorders or misspells a field does not become a partially-valid row — it does
/// not become a row at all.
pub fn parse(text: &str) -> Result<Ledger, Vec<Block>> {
    let mut blocks = Vec::new();
    let mut lines = text.lines().enumerate();

    let schema = lines.next();
    match schema {
        Some((_, l)) if l.trim() == LEDGER_SCHEMA => {}
        Some((_, l)) => {
            return Err(vec![Block::BadSchema {
                found: l.trim().to_string(),
            }]);
        }
        None => {
            return Err(vec![Block::BadSchema {
                found: String::new(),
            }]);
        }
    }

    let mut epoch = None;
    let mut revision = None;
    let mut rows = Vec::new();

    for (idx, raw) in lines {
        let line = raw.trim_end();
        let no = idx + 1;
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some((verb, rest)) = line.split_once(' ') else {
            blocks.push(Block::Malformed {
                line: no,
                reason: format!("no verb: {line:?}"),
            });
            continue;
        };
        match verb {
            "epoch" => epoch = Some(rest.trim().to_string()),
            "revision" => revision = Some(rest.trim().to_string()),
            "row" => match parse_row(rest, no) {
                Ok(r) => rows.push(r),
                Err(b) => blocks.push(b),
            },
            other => blocks.push(Block::Malformed {
                line: no,
                reason: format!("unknown verb {other:?}"),
            }),
        }
    }

    let (Some(epoch), Some(revision)) = (epoch, revision) else {
        blocks.push(Block::Malformed {
            line: 0,
            reason: "ledger must declare both an epoch and a revision".to_string(),
        });
        return Err(blocks);
    };

    if blocks.is_empty() {
        Ok(Ledger {
            epoch,
            revision,
            rows,
        })
    } else {
        Err(blocks)
    }
}

fn parse_row(rest: &str, line: usize) -> Result<ParityRow, Block> {
    let malformed = |reason: String| Block::Malformed { line, reason };

    // `limits` is last and takes the remainder of the line, because stated
    // limitations are prose and prose contains spaces. Everything before it is
    // whitespace-separated `k=v`.
    let (head, limits) = rest
        .split_once(" limits=")
        .ok_or_else(|| malformed("row has no limits= field".to_string()))?;
    let limits = limits.trim();
    if limits.is_empty() {
        return Err(malformed(
            "limits= is empty; write no-known-limitations to assert it".to_string(),
        ));
    }

    let mut parts = head.split_whitespace();
    let symbol = parts
        .next()
        .ok_or_else(|| malformed("row has no symbol".to_string()))?
        .to_string();

    let mut fields: BTreeMap<&str, &str> = BTreeMap::new();
    let mut order: Vec<&str> = Vec::new();
    for p in parts {
        let (k, v) = p
            .split_once('=')
            .ok_or_else(|| malformed(format!("field {p:?} is not k=v")))?;
        if fields.insert(k, v).is_some() {
            return Err(malformed(format!("field {k:?} appears twice")));
        }
        order.push(k);
    }
    // The declared order, minus `limits` which was split off above.
    let expected: Vec<&&str> = ROW_FIELDS.iter().filter(|f| **f != "limits").collect();
    if order.len() != expected.len() || order.iter().zip(&expected).any(|(a, b)| a != *b) {
        return Err(malformed(format!(
            "fields must be exactly {expected:?} in that order, got {order:?}"
        )));
    }

    let get = |k: &str| -> &str { fields.get(k).copied().unwrap_or("") };
    let bad = |k: &str, v: &str| malformed(format!("{k}={v:?} is not a valid {k}"));

    Ok(ParityRow {
        symbol,
        fixture: get("fixture").to_string(),
        fixture_digest: get("fixture_digest").to_string(),
        ours_root: parse_root(get("ours_root"))
            .ok_or_else(|| bad("ours_root", get("ours_root")))?,
        oracle_root: parse_root(get("oracle_root"))
            .ok_or_else(|| bad("oracle_root", get("oracle_root")))?,
        oracle: parse_oracle(get("oracle")).ok_or_else(|| bad("oracle", get("oracle")))?,
        comparison: parse_comparison(get("comparison"))
            .ok_or_else(|| bad("comparison", get("comparison")))?,
        normalizer: parse_normalizer(get("normalizer"))
            .ok_or_else(|| bad("normalizer", get("normalizer")))?,
        claim: parse_claim(get("claim")).ok_or_else(|| bad("claim", get("claim")))?,
        evidence: parse_evidence(get("evidence"))
            .ok_or_else(|| bad("evidence", get("evidence")))?,
        state: parse_state(get("state")).ok_or_else(|| bad("state", get("state")))?,
        level: parse_level(get("level")).ok_or_else(|| bad("level", get("level")))?,
        mode: parse_mode(get("mode")).ok_or_else(|| bad("mode", get("mode")))?,
        platform: parse_platform(get("platform"))
            .ok_or_else(|| bad("platform", get("platform")))?,
        backing: Backing::parse(get("backing")).ok_or_else(|| bad("backing", get("backing")))?,
        freshness: parse_freshness(get("freshness"))
            .ok_or_else(|| bad("freshness", get("freshness")))?,
        limits: limits.to_string(),
    })
}

/// The highest L-level an evidence state can close.
///
/// Reads `state` and NOTHING else — not the claim type, not the backing. The
/// backing rule is separate and lives in [`Block::MockOnlyClosure`], because
/// "the evidence is not established" and "the run was mocked" are two different
/// failures and a row can have either without the other.
fn level_ceiling(state: EvidenceState) -> LLevel {
    match state {
        EvidenceState::Proven | EvidenceState::Observed => LLevel::L4,
        // Nothing above L0 has been closed. L0 is "no claim", which is the only
        // honest level for evidence that has not been established.
        EvidenceState::Targeted | EvidenceState::Hypothesis | EvidenceState::Blocked => LLevel::L0,
    }
}

/// The strongest D7 claim an evidence state can carry.
///
/// Reads `state` and nothing else. Note that Observed tops out at
/// `bounded_model`: an observation is not a proof, and D7's rule that a weaker
/// class may never justify a stronger one applies to the ledger too.
fn claim_ceiling(state: EvidenceState) -> Option<ClaimType> {
    match state {
        EvidenceState::Proven => Some(ClaimType::Invariant),
        EvidenceState::Observed => Some(ClaimType::BoundedModel),
        EvidenceState::Targeted | EvidenceState::Hypothesis | EvidenceState::Blocked => None,
    }
}

fn level_rank(l: LLevel) -> u8 {
    match l {
        LLevel::L0 => 0,
        LLevel::L1 => 1,
        LLevel::L2 => 2,
        LLevel::L3 => 3,
        LLevel::L4 => 4,
    }
}

fn claim_strength(c: ClaimType) -> u8 {
    match c {
        ClaimType::Invariant => 5,
        ClaimType::Proof => 4,
        ClaimType::BoundedModel => 3,
        ClaimType::Statistical => 2,
        ClaimType::Slo => 1,
        ClaimType::Benchmark => 0,
    }
}

/// Verify a ledger against the expected symbol set and the epoch chain head.
///
/// Returns EVERY block found, not the first: a ledger with four problems should
/// report four. A non-empty result blocks; there is no warning level.
pub fn verify(ledger: &Ledger, expected: &[&str], chain_head: &str) -> Vec<Block> {
    let mut blocks = Vec::new();

    // STALE. The ledger describes a manifest revision; if that is not the head
    // the chain published, the ledger is describing something that has since
    // moved and every row in it is suspect.
    if ledger.revision != chain_head {
        blocks.push(Block::StaleRevision {
            stated: ledger.revision.clone(),
            head: chain_head.to_string(),
        });
    }

    // Never iterated, only inserted into and looked up, so `HashMap`'s random
    // iteration order cannot reach the output. Block order follows row order,
    // which is the file's order, which is deterministic.
    let mut seen: HashMap<RowKey, usize> = HashMap::new();
    for row in &ledger.rows {
        // AGGREGATE. Checked first: an aggregate is not a row, so none of the
        // per-row rules below are even meaningful for it.
        if is_aggregate_symbol(&row.symbol) {
            blocks.push(Block::AggregateRow {
                symbol: row.symbol.clone(),
            });
            continue;
        }

        // UNKNOWN.
        if !expected.contains(&row.symbol.as_str()) {
            blocks.push(Block::UnknownSymbol {
                symbol: row.symbol.clone(),
            });
        }

        // DUPLICATE, on symbol/platform/mode.
        let key = RowKey {
            symbol: row.symbol.clone(),
            platform: row.platform,
            mode: row.mode,
        };
        let count = seen.entry(key.clone()).or_insert(0);
        *count += 1;
        if *count == 2 {
            blocks.push(Block::DuplicateRow { key });
        }

        // ROOT MISMATCH. The comparison class decides what the roots must say.
        match row.comparison {
            ComparisonClass::ByteIdentical => match (&row.ours_root, &row.oracle_root) {
                (Root::Digest(a), Root::Digest(b)) if a == b => {}
                (Root::Digest(_), Root::Digest(_)) => blocks.push(Block::RootMismatch {
                    symbol: row.symbol.clone(),
                    detail: "byte-identical declared but the two roots differ".to_string(),
                }),
                _ => blocks.push(Block::RootMismatch {
                    symbol: row.symbol.clone(),
                    detail: "byte-identical declared without both roots".to_string(),
                }),
            },
            ComparisonClass::AcceptanceOnly => {
                // No artifact was compared, so citing roots claims a comparison
                // that did not happen.
                if row.ours_root != Root::Absent || row.oracle_root != Root::Absent {
                    blocks.push(Block::RootMismatch {
                        symbol: row.symbol.clone(),
                        detail: "acceptance-only declared but roots are cited".to_string(),
                    });
                }
            }
            ComparisonClass::NormalizedIdentical | ComparisonClass::DiagnosticEquivalent => {
                if row.ours_root == Root::Absent || row.oracle_root == Root::Absent {
                    blocks.push(Block::RootMismatch {
                        symbol: row.symbol.clone(),
                        detail: "a normalized comparison must cite both roots".to_string(),
                    });
                }
            }
        }

        // INCOHERENT COMPARISON. A normalizer named where nothing was
        // normalized, or normalization claimed with no normalizer named.
        match (row.comparison, row.normalizer) {
            (ComparisonClass::NormalizedIdentical, None)
            | (ComparisonClass::DiagnosticEquivalent, None) => {
                blocks.push(Block::IncoherentComparison {
                    symbol: row.symbol.clone(),
                    detail: "a normalized comparison must name its normalizer".to_string(),
                });
            }
            (ComparisonClass::ByteIdentical, Some(_))
            | (ComparisonClass::AcceptanceOnly, Some(_)) => {
                blocks.push(Block::IncoherentComparison {
                    symbol: row.symbol.clone(),
                    detail: "a normalizer is named but nothing was normalized".to_string(),
                });
            }
            _ => {}
        }

        // MOCK ONLY. A mock may support a unit test and may not close a public
        // claim. Reads `backing` and `level` only.
        if row.backing == Backing::Mock && level_rank(row.level) > 0 {
            blocks.push(Block::MockOnlyClosure {
                symbol: row.symbol.clone(),
                level: row.level,
            });
        }

        // OVERCLAIMED LEVEL. Reads `state` and `level`.
        if level_rank(row.level) > level_rank(level_ceiling(row.state)) {
            blocks.push(Block::OverclaimedLevel {
                symbol: row.symbol.clone(),
                state: row.state,
                level: row.level,
            });
        }

        // OVERCLAIMED CLAIM. Reads `state` and `claim`. Separate from the level
        // rule above and separate from the backing rule: three fields, three
        // checks, no substitution.
        let claim_ok = claim_ceiling(row.state)
            .is_some_and(|ceiling| claim_strength(row.claim) <= claim_strength(ceiling));
        if !claim_ok {
            blocks.push(Block::OverclaimedClaim {
                symbol: row.symbol.clone(),
                state: row.state,
                claim: row.claim,
            });
        }
    }

    // MISSING. Last, so a ledger that is both incomplete and wrong reports both.
    let present: HashSet<&str> = ledger.rows.iter().map(|r| r.symbol.as_str()).collect();
    for want in expected {
        if !present.contains(*want) {
            blocks.push(Block::MissingSymbol {
                symbol: (*want).to_string(),
            });
        }
    }

    blocks
}

/// Verify a ledger AND check every row's fixture against the filesystem.
///
/// [`verify`] is the schema-only check and stays available for callers that
/// have no tree to resolve against. This is the one a gate should run: a row
/// naming a fixture that does not exist, or stating a digest that is not the
/// file's, fails here rather than being recorded. `fixture_root` is the
/// directory row paths are resolved against.
pub fn verify_with_fixtures(
    ledger: &Ledger,
    expected: &[&str],
    chain_head: &str,
    fixture_root: &std::path::Path,
) -> Vec<Block> {
    let mut blocks = verify(ledger, expected, chain_head);
    for row in &ledger.rows {
        if is_aggregate_symbol(&row.symbol) {
            continue;
        }
        if let Err(e) =
            crate::derive::check_fixture(&fixture_root.join(&row.fixture), &row.fixture_digest)
        {
            blocks.push(Block::FixtureUnverified {
                symbol: row.symbol.clone(),
                detail: e.to_string(),
            });
        }
    }
    blocks
}

/// Line-oriented report. One line per block, machine-first, no decoration.
///
/// Emits counts of BLOCKS and never a parity score, a percentage, or a pass
/// rate. Under D7 a headline number is not evidence, and a report that prints
/// one invites it to be quoted as though it were.
pub fn report(blocks: &[Block]) -> String {
    let mut out = String::new();
    for b in blocks {
        out.push_str(&format!(
            "parity-ledger: block reason={} {b:?}\n",
            b.reason()
        ));
    }
    out.push_str(&format!(
        "parity-ledger: verdict={} blocks={}\n",
        if blocks.is_empty() { "pass" } else { "fail" },
        blocks.len()
    ));
    out
}

#[cfg(test)]
mod structural {
    use super::*;

    #[test]
    fn no_field_can_hold_an_aggregate() {
        // The prohibition is structural first: there is no field for a count, a
        // total, a percentage or a score, so a row cannot carry one even if
        // somebody wanted it to. If a future field name matches one of these,
        // this test is the thing that has to be argued with.
        const FORBIDDEN: &[&str] = &[
            "count",
            "total",
            "percent",
            "percentage",
            "score",
            "rate",
            "average",
            "mean",
            "ratio",
            "summary",
        ];
        for f in ROW_FIELDS {
            for bad in FORBIDDEN {
                assert!(
                    !f.contains(bad),
                    "row field {f:?} looks like an aggregate ({bad:?})"
                );
            }
        }
    }

    #[test]
    fn every_block_variant_has_its_own_reason_token() {
        // Each blocking condition must fail for ITS OWN reason. If two variants
        // shared a token, a mutant that broke one could be "caught" by the
        // other's test and the campaign would prove nothing.
        let all = [
            Block::BadSchema {
                found: String::new(),
            },
            Block::Malformed {
                line: 0,
                reason: String::new(),
            },
            Block::MissingSymbol {
                symbol: String::new(),
            },
            Block::DuplicateRow {
                key: RowKey {
                    symbol: String::new(),
                    platform: Platform::LinuxX86_64,
                    mode: Mode::Sound,
                },
            },
            Block::StaleRevision {
                stated: String::new(),
                head: String::new(),
            },
            Block::UnknownSymbol {
                symbol: String::new(),
            },
            Block::RootMismatch {
                symbol: String::new(),
                detail: String::new(),
            },
            Block::MockOnlyClosure {
                symbol: String::new(),
                level: LLevel::L1,
            },
            Block::OverclaimedLevel {
                symbol: String::new(),
                state: EvidenceState::Targeted,
                level: LLevel::L1,
            },
            Block::OverclaimedClaim {
                symbol: String::new(),
                state: EvidenceState::Targeted,
                claim: ClaimType::Proof,
            },
            Block::AggregateRow {
                symbol: String::new(),
            },
            Block::IncoherentComparison {
                symbol: String::new(),
                detail: String::new(),
            },
            Block::FixtureUnverified {
                symbol: String::new(),
                detail: String::new(),
            },
        ];
        let mut tokens: Vec<&str> = all.iter().map(Block::reason).collect();
        let before = tokens.len();
        tokens.sort_unstable();
        tokens.dedup();
        assert_eq!(
            before,
            tokens.len(),
            "two Block variants share a reason token"
        );
    }

    #[test]
    fn the_report_never_emits_a_percentage_or_a_score() {
        let blocks = vec![Block::MissingSymbol {
            symbol: "Nat.foo".to_string(),
        }];
        let text = report(&blocks);
        assert!(!text.contains('%'), "the report emitted a percentage");
        for word in ["parity=", "score", "rate=", "percent"] {
            assert!(!text.contains(word), "the report emitted {word:?}");
        }
        assert!(text.contains("verdict=fail"));
        assert!(report(&[]).contains("verdict=pass"));
    }
}
