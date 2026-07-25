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
//! refusal, not a default — every field is required and there is no `Default`
//! impl, so a row that omits a field does not parse. The two fields that are
//! `Option` ([`ParityRow::normalizer`], [`ParityRow::comparison`]) are not
//! optional in the file: they are spelled `-`, which is a *declared* absence
//! somebody asserted, and the verifier holds it to the same coherence rules as
//! any other value.
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
//! Schema 2 adds four, on the same law — one condition, one variant, one token:
//!
//! | condition | variant |
//! |---|---|
//! | the stated conclusion is not what the row's own sides produce | [`Block::Misscored`] |
//! | a divergence with nothing said about its cause, or a cause named where there is no divergence | [`Block::IncoherentDisposition`] |
//! | a comparison class named where nothing was compared, or omitted where something was | [`Block::UncomparedRow`] |
//! | a compatibility level closed by a row that compared nothing | [`Block::LevelWithoutComparison`] |
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
//!
//! # Schema 2: what version 1 could not say (bead `fln-fei1`)
//!
//! Version 1 was an **agreement** ledger wearing a parity ledger's name. Four
//! row kinds come out of a real corpus run and it could express one of them:
//! an agreeing symbol. A restrictive divergence was refused as a root mismatch,
//! because every [`ComparisonClass`] asserts an act of comparing that concluded
//! in agreement and differing roots could only mean the row was wrong. An
//! oracle-silent symbol had no encoding at all, and its NEAREST encoding —
//! `acceptance-only` with both roots absent — passed while asserting a
//! comparison that never happened. An unassessed symbol could only be absent,
//! which reports as [`Block::MissingSymbol`]: "we have no row" and "we have a
//! row that says nobody looked" are different facts.
//!
//! Version 2 adds the axis that was missing: **what each side actually said**.
//! [`ParityRow::ours_verdict`] and [`ParityRow::oracle_verdict`] are recorded
//! per side, [`ParityRow::assessment`] records what that pair scores to, and
//! the verifier re-derives the score with [`crate::oracle::score_verdicts`] —
//! the same function the live rigs use, so a row cannot state a conclusion its
//! own two sides do not support.
//!
//! Two consequences worth stating, because they change what old refusals mean:
//!
//! **A divergence is now a representable row, so [`Block::RootMismatch`] had to
//! be re-derived.** Under version 1 it fired on any two differing roots. Under
//! version 2 it fires when the roots contradict the ASSESSMENT: agreement with
//! differing roots is still a defect, and a divergence with *identical* roots is
//! now a defect too — that one was unrepresentable before and is the sharper of
//! the pair.
//!
//! **A divergence must say whether it was called.** [`Disposition`] is a
//! separate axis from [`Assessment`] on purpose: "the two implementations
//! differ" and "we have classified why" are different questions, and a schema
//! that answered only the first would force every measured-but-unclassified
//! divergence to be recorded as either a finding or nothing. `uncalled` is a
//! first-class value, and the census below reports it as its own class — never
//! folded into a pass and never into a finding.

use crate::normalize::{NormalizerId, NormalizerVersion};
use crate::oracle::{
    ClaimType, ComparisonClass, EvidenceKind, EvidenceState, Freshness, LLevel, Mode,
    NonAuthoritative, OracleKind, OracleVerdict, OurVerdict, Platform, Scored, score_verdicts,
};
use std::collections::{BTreeMap, HashMap, HashSet};

/// Schema line. Versioned: a change to what a row must name registers a NEW
/// schema rather than reinterpreting rows already recorded under the old one.
///
/// **The outcome record's own schema id — a distinct lineage, not a successor**
/// (bead `franken_lean-otwd`, deciding the question `fln-fei1` surfaced).
///
/// This file answers *what happened when we compared a symbol against the
/// oracle*: keyed `(symbol, platform, mode)`, carrying roots, oracle kind,
/// comparison class, per-side verdicts, an assessment and a disposition.
///
/// It is **not** a version of the twelve-field pipe-separated **inventory** in
/// `crates/fln-conformance/src/ledger.rs` that backs `ci/PARITY_LEDGER.txt` and
/// keeps `fln-parity-ledger/1`. That record answers a different question —
/// *which surface rows do we claim, and at what evidence level* — and is keyed
/// `(surface, symbol, mode)`. Different question, different key, different
/// grammar; neither parser accepts the other's file.
///
/// `fln-fei1` moved this record to `fln-parity-ledger/2`, which removed the live
/// collision but left a worse reading in place: `/2` looks like the successor of
/// `/1`, so a reader would reasonably assume the inventory is superseded and
/// that rows migrate between them. They do not. Naming the lineages apart is the
/// only version string that cannot be misread that way, and doing it **now** is
/// nearly free precisely because this record has no published artifact yet —
/// the same rename after publication would be a migration.
///
/// The version therefore restarts at 1: this is version 1 of the outcome record,
/// not version 3 of anything. [`refuses_the_inventory_grammar_that_shared_its_version_string`]
/// pins the separation so it cannot silently return.
///
/// [`refuses_the_inventory_grammar_that_shared_its_version_string`]: self::structural::refuses_the_inventory_grammar_that_shared_its_version_string
pub const OUTCOME_SCHEMA: &str = "fln-parity-outcome/1";

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

/// What a row concluded from its two sides.
///
/// The arms are [`Scored`]'s arms without the payload: a row records the class
/// of the conclusion, and the reason a non-answer happened is already carried by
/// the side that gave it. Kept as its own type rather than storing a `Scored`
/// because [`Scored::Unscorable`] carries a [`NonAuthoritative`] that would then
/// have to be reconstructed from text, inviting a fabricated payload — and a
/// fabricated reason is worse than a named class.
///
/// Recorded in the file AND re-derived by the verifier. The redundancy is the
/// point: a reader sees `restrictive` without doing the derivation in their
/// head, and [`Block::Misscored`] proves the file is not lying about it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Assessment {
    /// Both sides answered and agreed.
    Agree,
    /// We rejected, the oracle accepted. A finding, and the D23 carve-out
    /// direction — restrictive, not unsound.
    Restrictive,
    /// We accepted, the oracle rejected. Unsound, never carve-out-able.
    UnsoundlyPermissive,
    /// At least one side did not answer, so there is nothing to score. **Not**
    /// a divergence in either direction.
    Unscorable,
}

impl Assessment {
    /// The class of a [`Scored`]. Total, so a new `Scored` arm cannot be
    /// silently dropped into an existing class.
    pub fn of(scored: &Scored) -> Assessment {
        match scored {
            Scored::Agree => Assessment::Agree,
            Scored::Restrictive => Assessment::Restrictive,
            Scored::UnsoundlyPermissive => Assessment::UnsoundlyPermissive,
            Scored::Unscorable(_) => Assessment::Unscorable,
        }
    }

    /// Whether the two implementations differ. Mirrors
    /// [`Scored::is_divergence`], and for the same reason: an unscorable row
    /// counted as a divergence is a manufactured finding.
    pub fn is_divergence(self) -> bool {
        matches!(
            self,
            Assessment::Restrictive | Assessment::UnsoundlyPermissive
        )
    }

    pub fn token(self) -> &'static str {
        match self {
            Assessment::Agree => "agree",
            Assessment::Restrictive => "restrictive",
            Assessment::UnsoundlyPermissive => "unsoundly-permissive",
            Assessment::Unscorable => "unscorable",
        }
    }

    fn parse(s: &str) -> Option<Assessment> {
        match s {
            "agree" => Some(Assessment::Agree),
            "restrictive" => Some(Assessment::Restrictive),
            "unsoundly-permissive" => Some(Assessment::UnsoundlyPermissive),
            "unscorable" => Some(Assessment::Unscorable),
            _ => None,
        }
    }
}

/// Whether a divergence's root cause has been classified, and as what.
///
/// A **separate axis** from [`Assessment`], not a refinement of it. "The two
/// implementations differ" is a measurement; "we know why" is a conclusion; and
/// collapsing them forces every divergence whose cause is still open to be
/// filed as either a finding or nothing at all. [`Disposition::Uncalled`] is
/// what a real corpus run produces most of, and the census reports it as its
/// own class.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Disposition {
    /// There is no divergence to call. Spelled `-`: a declared absence, like
    /// every other `-` in this schema, never a default.
    NotADivergence,
    /// Measured, and deliberately not classified. Neither a pass nor a finding.
    Uncalled,
    /// Called: the cause is in our comparison apparatus — decoder, scope,
    /// fixture — and not in either implementation.
    Harness,
    /// Called: the cause is a real difference between the two implementations.
    Semantic,
}

impl Disposition {
    pub fn token(self) -> &'static str {
        match self {
            Disposition::NotADivergence => "-",
            Disposition::Uncalled => "uncalled",
            Disposition::Harness => "harness",
            Disposition::Semantic => "semantic",
        }
    }

    fn parse(s: &str) -> Option<Disposition> {
        match s {
            "-" => Some(Disposition::NotADivergence),
            "uncalled" => Some(Disposition::Uncalled),
            "harness" => Some(Disposition::Harness),
            "semantic" => Some(Disposition::Semantic),
            _ => None,
        }
    }
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
    /// What WE said about this symbol.
    pub ours_verdict: OurVerdict,
    /// What the ORACLE said about this symbol. Its `NoAnswer` arm is how a
    /// symbol the oracle does not judge gets a row instead of an absence.
    pub oracle_verdict: OracleVerdict,
    /// What those two score to. Re-derived by the verifier; see
    /// [`Block::Misscored`].
    pub assessment: Assessment,
    /// Whether a divergence's cause has been called. Its own axis; see
    /// [`Disposition`].
    pub disposition: Disposition,
    pub oracle: OracleKind,
    /// How the two artifacts were compared, or a declared `-` for "no
    /// comparison was performed".
    ///
    /// `Option` here is the same declared-absence device as [`Root::Absent`] and
    /// the normalizer's `-`, and it is what version 1 lacked: every
    /// [`ComparisonClass`] asserts that a comparison happened, so a symbol
    /// nobody compared could only be described by a class that lied about it.
    pub comparison: Option<ComparisonClass>,
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
    /// The stated assessment is not what the row's own two sides score to.
    ///
    /// Checked with [`crate::oracle::score_verdicts`], the same function the
    /// live rigs score with. A row that says `agree` over a rejection and an
    /// acceptance is the single most dangerous thing this file can contain, and
    /// before schema 2 it could not even be written down, let alone refused.
    Misscored {
        symbol: String,
        stated: Assessment,
        derived: Assessment,
    },
    /// The disposition and the assessment disagree about whether there is a
    /// divergence to call.
    IncoherentDisposition {
        symbol: String,
        assessment: Assessment,
        disposition: Disposition,
    },
    /// A comparison class was declared for a row nothing was compared in, or
    /// omitted from one that was compared.
    UncomparedRow { symbol: String, detail: String },
    /// A row that compared nothing claims an L-level above L0.
    ///
    /// Separate from [`Block::OverclaimedLevel`], which reads the evidence
    /// state: this one fires however impeccable the state is, because a level is
    /// a claim about a symbol's compatibility and an uncompared symbol has no
    /// compatibility evidence at all. Without it, `state=observed` — an honest
    /// thing to say about having observed that the oracle is silent — would
    /// carry an L4 ceiling and let a symbol nobody checked be published as
    /// attested.
    LevelWithoutComparison { symbol: String, level: LLevel },
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
            Block::Misscored { .. } => "misscored",
            Block::IncoherentDisposition { .. } => "incoherent-disposition",
            Block::UncomparedRow { .. } => "uncompared",
            Block::LevelWithoutComparison { .. } => "level-without-comparison",
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
    "ours_verdict",
    "oracle_verdict",
    "assessment",
    "disposition",
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

fn parse_comparison(s: &str) -> Option<Option<ComparisonClass>> {
    match s {
        // A declared absence, exactly like the normalizer's `-`: no comparison
        // was performed. Not a class, and not a missing field.
        "-" => Some(None),
        "byte-identical" => Some(Some(ComparisonClass::ByteIdentical)),
        "normalized-identical" => Some(Some(ComparisonClass::NormalizedIdentical)),
        "acceptance-only" => Some(Some(ComparisonClass::AcceptanceOnly)),
        "diagnostic-equivalent" => Some(Some(ComparisonClass::DiagnosticEquivalent)),
        _ => None,
    }
}

/// Our side's verdict, as a row records it.
///
/// `rejected` carries no diagnostic text here on purpose. The ledger is not a
/// diagnostic archive: comparing diagnostics is what the `diagnostic-equivalent`
/// comparison class and its normalizer are for, and a row quoting an error
/// string invites text-matching in a place where a versioned normalizer already
/// governs the question. `inconclusive` must name what was inconclusive,
/// because FL-INV-07's whole point is that a non-answer is typed rather than
/// silent.
fn parse_our_verdict(s: &str) -> Option<OurVerdict> {
    match s {
        "accepted" => Some(OurVerdict::Accepted),
        "rejected" => Some(OurVerdict::Rejected {
            diagnostic: String::new(),
        }),
        _ => {
            let what = s.strip_prefix("inconclusive:")?;
            (!what.is_empty()).then(|| OurVerdict::Inconclusive {
                what: what.to_string(),
            })
        }
    }
}

/// The oracle's verdict, as a row records it.
///
/// The non-answer reasons are a closed set, not free text: an oracle's reasons
/// for not answering are exactly the vocabulary business of [`crate::oracle`],
/// and a free string here would let anyone mint a new one. `out-of-scope` and
/// `not-assessed` are both [`NonAuthoritative::NotJudged`] — the run was fine
/// and there is still no judgment about this subject — and they are spelled
/// apart because "the oracle does not judge this kind of symbol" and "nobody
/// submitted it at this scope" are different facts about coverage.
fn parse_oracle_verdict(s: &str) -> Option<OracleVerdict> {
    match s {
        "accepted" => Some(OracleVerdict::Accepted),
        "rejected" => Some(OracleVerdict::Rejected {
            diagnostic: String::new(),
        }),
        "no-answer:out-of-scope" => Some(OracleVerdict::NoAnswer(NonAuthoritative::not_judged(
            "out-of-scope",
        ))),
        "no-answer:not-assessed" => Some(OracleVerdict::NoAnswer(NonAuthoritative::not_judged(
            "not-assessed",
        ))),
        "no-answer:internal-fault" => Some(OracleVerdict::NoAnswer(
            NonAuthoritative::internal_fault("recorded ledger row"),
        )),
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
        Some((_, l)) if l.trim() == OUTCOME_SCHEMA => {}
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
        ours_verdict: parse_our_verdict(get("ours_verdict"))
            .ok_or_else(|| bad("ours_verdict", get("ours_verdict")))?,
        oracle_verdict: parse_oracle_verdict(get("oracle_verdict"))
            .ok_or_else(|| bad("oracle_verdict", get("oracle_verdict")))?,
        assessment: Assessment::parse(get("assessment"))
            .ok_or_else(|| bad("assessment", get("assessment")))?,
        disposition: Disposition::parse(get("disposition"))
            .ok_or_else(|| bad("disposition", get("disposition")))?,
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

        // MISSCORED. First of the outcome rules, because every rule after it
        // reads the assessment and a lying assessment would poison all of them.
        // Derived with the live scoring function, never re-implemented here.
        let derived = Assessment::of(&score_verdicts(&row.ours_verdict, &row.oracle_verdict));
        if derived != row.assessment {
            blocks.push(Block::Misscored {
                symbol: row.symbol.clone(),
                stated: row.assessment,
                derived,
            });
        }

        // INCOHERENT DISPOSITION. A divergence must be called or explicitly
        // uncalled; a row with nothing to call must not name a cause.
        match (row.assessment.is_divergence(), row.disposition) {
            (true, Disposition::NotADivergence)
            | (false, Disposition::Uncalled)
            | (false, Disposition::Harness)
            | (false, Disposition::Semantic) => {
                blocks.push(Block::IncoherentDisposition {
                    symbol: row.symbol.clone(),
                    assessment: row.assessment,
                    disposition: row.disposition,
                });
            }
            _ => {}
        }

        // UNCOMPARED. Whether a comparison class is named must match whether
        // there was anything to compare. This is the rule that stops the
        // version-1 lie: an oracle-silent symbol can no longer borrow
        // `acceptance-only` to look like a comparison that agreed.
        match (row.comparison, row.assessment) {
            (Some(_), Assessment::Unscorable) => blocks.push(Block::UncomparedRow {
                symbol: row.symbol.clone(),
                detail: "a comparison class is named but one side did not answer".to_string(),
            }),
            (None, a) if a != Assessment::Unscorable => blocks.push(Block::UncomparedRow {
                symbol: row.symbol.clone(),
                detail: "both sides answered but no comparison class is named".to_string(),
            }),
            _ => {}
        }

        // ROOT MISMATCH. The comparison class decides what the roots must say —
        // and, since schema 2, so does the assessment. Under version 1 this rule
        // read the class alone, which made every divergence a defect.
        match row.comparison {
            Some(ComparisonClass::ByteIdentical) => {
                match (&row.ours_root, &row.oracle_root, row.assessment) {
                    // Agreement: two roots, and they must be the same bytes.
                    (Root::Digest(a), Root::Digest(b), Assessment::Agree) if a == b => {}
                    (Root::Digest(_), Root::Digest(_), Assessment::Agree) => {
                        blocks.push(Block::RootMismatch {
                            symbol: row.symbol.clone(),
                            detail: "byte-identical agreement declared but the two roots differ"
                                .to_string(),
                        });
                    }
                    // Divergence: two roots, and they must NOT be the same
                    // bytes. Identical roots under a divergence was
                    // unrepresentable before schema 2 and is the sharper half of
                    // this pair — it is a row claiming a finding its own
                    // evidence contradicts.
                    (Root::Digest(a), Root::Digest(b), d) if d.is_divergence() => {
                        if a == b {
                            blocks.push(Block::RootMismatch {
                                symbol: row.symbol.clone(),
                                detail: "a divergence is declared but the two roots are identical"
                                    .to_string(),
                            });
                        }
                    }
                    _ => blocks.push(Block::RootMismatch {
                        symbol: row.symbol.clone(),
                        detail: "byte-identical declared without both roots".to_string(),
                    }),
                }
            }
            Some(ComparisonClass::AcceptanceOnly) => {
                // No artifact was compared, so citing roots claims a comparison
                // that did not happen.
                if row.ours_root != Root::Absent || row.oracle_root != Root::Absent {
                    blocks.push(Block::RootMismatch {
                        symbol: row.symbol.clone(),
                        detail: "acceptance-only declared but roots are cited".to_string(),
                    });
                }
            }
            Some(ComparisonClass::NormalizedIdentical)
            | Some(ComparisonClass::DiagnosticEquivalent) => {
                if row.ours_root == Root::Absent || row.oracle_root == Root::Absent {
                    blocks.push(Block::RootMismatch {
                        symbol: row.symbol.clone(),
                        detail: "a normalized comparison must cite both roots".to_string(),
                    });
                }
            }
            // Nothing was compared. Our own root may still exist — we may have
            // produced an artifact for a symbol the oracle never judged, and
            // recording it is a limitation ON the row rather than an absence
            // from it. The oracle's root may not: an oracle that gave no answer
            // produced nothing to cite, so a digest there is a fabrication.
            None => {
                if row.oracle_root != Root::Absent {
                    blocks.push(Block::RootMismatch {
                        symbol: row.symbol.clone(),
                        detail: "the oracle gave no answer but its root is cited".to_string(),
                    });
                }
            }
        }

        // INCOHERENT COMPARISON. A normalizer named where nothing was
        // normalized, or normalization claimed with no normalizer named.
        match (row.comparison, row.normalizer) {
            (Some(ComparisonClass::NormalizedIdentical), None)
            | (Some(ComparisonClass::DiagnosticEquivalent), None) => {
                blocks.push(Block::IncoherentComparison {
                    symbol: row.symbol.clone(),
                    detail: "a normalized comparison must name its normalizer".to_string(),
                });
            }
            (Some(ComparisonClass::ByteIdentical), Some(_))
            | (Some(ComparisonClass::AcceptanceOnly), Some(_))
            | (None, Some(_)) => {
                blocks.push(Block::IncoherentComparison {
                    symbol: row.symbol.clone(),
                    detail: "a normalizer is named but nothing was normalized".to_string(),
                });
            }
            _ => {}
        }

        // LEVEL WITHOUT COMPARISON. An uncompared symbol has no compatibility
        // evidence, whatever its evidence state says. Reads `assessment` and
        // `level` only — the state rule below is separate and still applies.
        if row.assessment == Assessment::Unscorable && level_rank(row.level) > 0 {
            blocks.push(Block::LevelWithoutComparison {
                symbol: row.symbol.clone(),
                level: row.level,
            });
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
    // `schema-verdict`, not `verdict`. What this function decides is whether the
    // FILE is admissible, and a bare `verdict=pass` on a ledger of unassessed
    // rows is exactly the sentence someone quotes as "we match the Reference".
    // The parity content is in [`census`], where it cannot be read as one word.
    out.push_str(&format!(
        "parity-ledger: schema-verdict={} blocks={}\n",
        if blocks.is_empty() { "pass" } else { "fail" },
        blocks.len()
    ));
    out
}

/// What the ledger's rows actually say, one line per class.
///
/// This is not an aggregate in the D7 sense and it is the opposite of a headline
/// number: it is the disaggregation, and there is deliberately no grand total
/// and no percentage to quote. Each line names an assessment and, for
/// divergences, a disposition — so a measured-but-uncalled divergence appears as
/// its own class and is never folded into a pass or into a finding. That is the
/// requirement `fln-fei1` names first, and a report that only printed blocks
/// would satisfy it by saying nothing at all.
///
/// Ordered by the vocabularies rather than by count, so the output is stable and
/// diffable and a class that dropped to zero is visibly absent rather than
/// resorted.
pub fn census(ledger: &Ledger) -> String {
    const ASSESSMENTS: [Assessment; 4] = [
        Assessment::Agree,
        Assessment::Restrictive,
        Assessment::UnsoundlyPermissive,
        Assessment::Unscorable,
    ];
    const DISPOSITIONS: [Disposition; 4] = [
        Disposition::NotADivergence,
        Disposition::Uncalled,
        Disposition::Harness,
        Disposition::Semantic,
    ];

    let mut counts: BTreeMap<(&str, &str), usize> = BTreeMap::new();
    for row in &ledger.rows {
        *counts
            .entry((row.assessment.token(), row.disposition.token()))
            .or_insert(0) += 1;
    }

    let mut out = String::new();
    for a in ASSESSMENTS {
        for d in DISPOSITIONS {
            let n = counts.get(&(a.token(), d.token())).copied().unwrap_or(0);
            if n == 0 {
                continue;
            }
            out.push_str(&format!(
                "parity-ledger: rows assessment={} disposition={} n={n}\n",
                a.token(),
                d.token()
            ));
        }
    }
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
            Block::Misscored {
                symbol: String::new(),
                stated: Assessment::Agree,
                derived: Assessment::Unscorable,
            },
            Block::IncoherentDisposition {
                symbol: String::new(),
                assessment: Assessment::Agree,
                disposition: Disposition::Uncalled,
            },
            Block::UncomparedRow {
                symbol: String::new(),
                detail: String::new(),
            },
            Block::LevelWithoutComparison {
                symbol: String::new(),
                level: LLevel::L1,
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
    fn refuses_the_inventory_grammar_that_shared_its_version_string() {
        // Two mutually unparseable grammars were both declaring
        // `fln-parity-ledger/1`: this one, and the twelve-field pipe-separated
        // inventory in `crates/fln-conformance/src/ledger.rs` that backs
        // `ci/PARITY_LEDGER.txt`. Neither parser accepts the other's file — that
        // one prefixes its schema line with `schema ` and opens with comments,
        // this one takes line 1 verbatim — so the shared id was never a shared
        // format, only a shared name for two of them.
        //
        // `fln-fei1` moved this record to `fln-parity-ledger/2`, which removed the
        // collision but left `/2` reading as the successor of `/1`. Bead
        // `franken_lean-otwd` decided the lineages are named apart instead, so the
        // check is stronger than "the version moved": this record must not be in
        // the inventory's NAME FAMILY AT ALL. A future `fln-parity-ledger/3` would
        // otherwise reintroduce exactly the misreading, and a version-only
        // assertion would not notice.
        assert!(
            !OUTCOME_SCHEMA.starts_with("fln-parity-ledger/"),
            "the outcome record is back inside the inventory's name family \
             ({OUTCOME_SCHEMA}); they are different lineages over different \
             questions, not versions of each other"
        );
        assert_eq!(
            OUTCOME_SCHEMA, "fln-parity-outcome/1",
            "the outcome record's id is a governed decision (franken_lean-otwd), \
             not an implementation detail"
        );

        let inventory = "schema fln-parity-ledger/1\n\
            row meta-api | Lean.Name.hash | function | native | L2 | faithful \
            | pinned-binary | exact | fixtures/x.txt | D0 | OBSERVED | run-1\n";
        match parse(inventory) {
            Err(blocks) => assert_eq!(
                blocks.iter().map(Block::reason).collect::<Vec<_>>(),
                vec!["bad-schema"],
                "the inventory grammar was refused for the wrong reason"
            ),
            Ok(l) => panic!("a file in the other grammar parsed as this one: {l:?}"),
        }
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
