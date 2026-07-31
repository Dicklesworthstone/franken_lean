//! The mutation kill ledger model (plan §18.2; bead `fln-td9`, framework 1 of 6).
//!
//! # The laws this model carries
//!
//! td9's kill law is exact: a mutant counts as killed **only** when the named
//! discriminating test fails *for the stated reason*. Compile failure, an unrelated gate
//! failure, a timeout, death at another mutant's hand, and harness internal faults are
//! **not** kills — and they are not survivors either. FL-INV-07 applies to campaign
//! accounting exactly as it applies to the kernel: inconclusive is neither acceptance nor
//! rejection, so an inconclusive run is `NotKilled` with its kind named, never rounded
//! into either settled class.
//!
//! The denominator law is the second half: equivalent and unbuildable mutants are typed,
//! **evidenced** classifications. An exclusion without evidence is a typed error, because
//! a denominator that shrinks without a reason is how a campaign inflates its kill rate —
//! the `denominator drop` self-mutant td9 names. Excluded mutants stay *counted* in the
//! summary; they simply leave the active denominator, with the evidence attached.
//!
//! Every mutant carries the seven binds td9 lists: mutant id, source-root digest, patch
//! digest, build identity, production-path target, expected discriminator, and the
//! release-exclusion proof. The constructor refuses a missing or shapeless field and names
//! it — a binding is a claim, and a claim with a hole is refused at construction rather
//! than discovered at audit.
//!
//! # What this model does not establish
//!
//! The model enforces *accounting* laws over what a campaign reports. It cannot know
//! whether a campaign's `FailedForStatedReason` label is true — that is the campaign's
//! own evidence problem (uagk's campaign pins the failure message, which is why its
//! receipts can feed this model as the real controlled target). A ledger full of lies
//! balances perfectly; the accounting just makes the lies enumerable.

use std::collections::BTreeMap;
use std::fmt;

/// The ledger row schema. Versioned so a drifted emitter fails loudly rather than
/// feeding a stale shape to a consumer that trusts it.
pub const KILL_LEDGER_SCHEMA: &str = "fln.mutation-kill-ledger/1";

/// Why a run is not a kill — td9's taxonomy, verbatim: "Compile failure, unrelated gate
/// failure, timeout, another mutant, or harness InternalFault is not a kill."
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NotAKill {
    /// The mutated tree did not build. The discriminating test never ran.
    CompileFailure,
    /// A gate other than the discriminating test failed; the mutant's own effect was
    /// never isolated.
    UnrelatedGateFailure,
    /// The run exceeded its budget. FL-INV-07: a typed non-answer.
    Timeout,
    /// The discriminating test failed, but not for the stated reason — the mutant died
    /// at another mutant's hand, or the test drifted. uagk measured this live: with
    /// positivity skipped the bad block is still rejected, for "block declares 0
    /// recursors", and only the pinned-message assertion notices.
    AnotherMutant,
    /// The harness itself faulted. FL-INV-07: an internal fault is never evidence
    /// about the mutant.
    HarnessFault,
}

impl NotAKill {
    /// The stable wire token, used in NDJSON rows and error text.
    pub fn token(self) -> &'static str {
        match self {
            Self::CompileFailure => "compile_failure",
            Self::UnrelatedGateFailure => "unrelated_gate_failure",
            Self::Timeout => "timeout",
            Self::AnotherMutant => "another_mutant",
            Self::HarnessFault => "harness_fault",
        }
    }

    fn from_token(token: &str) -> Option<Self> {
        match token {
            "compile_failure" => Some(Self::CompileFailure),
            "unrelated_gate_failure" => Some(Self::UnrelatedGateFailure),
            "timeout" => Some(Self::Timeout),
            "another_mutant" => Some(Self::AnotherMutant),
            "harness_fault" => Some(Self::HarnessFault),
            _ => None,
        }
    }
}

/// What one run of the discriminating test under the mutant observed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Observation {
    /// The named test failed and the failure carried the stated reason. The only
    /// observation that is a kill.
    FailedForStatedReason,
    /// The named test passed. The mutant survived — the campaign's finding.
    Passed,
    /// The named test failed, but the failure did not carry the stated reason.
    WrongFailureReason,
    /// The mutated tree did not build.
    CompileFailure,
    /// A gate other than the discriminating test failed.
    UnrelatedGateFailure,
    /// The run exceeded its budget.
    Timeout,
    /// The harness itself faulted.
    HarnessFault,
}

/// The three-way verdict an observation settles to. `NotKilled` is deliberately not
/// called `Survived`: an inconclusive run says nothing about the mutant's fate, and
/// naming it survivor would be FL-INV-07's forbidden promotion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KillVerdict {
    /// Killed, for the stated reason, by the named discriminator.
    Killed,
    /// The discriminating test passed under the mutant.
    Survived,
    /// Not a kill, and not a survivor: the run is inconclusive about the mutant.
    NotKilled(NotAKill),
}

impl Observation {
    /// The verdict this observation settles to. Total: every observation classifies,
    /// and only one observation kind kills.
    pub fn verdict(&self) -> KillVerdict {
        match self {
            Self::FailedForStatedReason => KillVerdict::Killed,
            Self::Passed => KillVerdict::Survived,
            Self::WrongFailureReason => KillVerdict::NotKilled(NotAKill::AnotherMutant),
            Self::CompileFailure => KillVerdict::NotKilled(NotAKill::CompileFailure),
            Self::UnrelatedGateFailure => KillVerdict::NotKilled(NotAKill::UnrelatedGateFailure),
            Self::Timeout => KillVerdict::NotKilled(NotAKill::Timeout),
            Self::HarnessFault => KillVerdict::NotKilled(NotAKill::HarnessFault),
        }
    }
}

/// A mutant's standing in the campaign. The exclusions are the denominator law:
/// each carries its evidence, and the constructor refuses an empty one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Disposition {
    /// In the denominator; must be run and accounted for.
    Active,
    /// Provably behavior-identical to the unmutated code. The evidence is the
    /// argument (e.g. the equivalence proof, the review record) — never empty.
    Equivalent { evidence: String },
    /// Cannot be built at all, with the build evidence attached. Distinct from
    /// `NotAKill::CompileFailure`, which is a build failure *observed during a
    /// campaign run* of a mutant expected to build; this disposition is a settled,
    /// evidenced classification made before the campaign.
    Unbuildable { evidence: String },
}

/// The seven binds td9 requires of every mutant: source root, patch digest, build
/// identity, mutant id, production-path target, expected discriminator, and the
/// release-exclusion proof. All fields are validated at construction; a missing or
/// shapeless field is a typed error naming it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MutantBinding {
    /// The mutant's stable id (for a mandated campaign, §18's own name for the defect).
    pub mutant_id: String,
    /// Binds the source root the mutant was built from (a commit digest or tree hash).
    pub source_root_digest: String,
    /// Binds the exact mutation applied (uagk binds path + replaced text).
    pub patch_digest: String,
    /// The toolchain/build the campaign compiled (e.g. the pinned nightly + profile).
    pub build_identity: String,
    /// The production path the mutant touches — reachability into real code, so a
    /// mutant against dead or test-only code cannot dress itself as a production kill.
    pub target_path: String,
    /// The named test and stated reason that must fire (uagk pins the failure message,
    /// not just the test name).
    pub expected_discriminator: String,
    /// The mechanism keeping mutation controls out of release artifacts (e.g.
    /// `test-target-only`: the campaign compiles only into `#[test]` targets, which no
    /// release artifact contains).
    pub release_exclusion_proof: String,
}

/// Every way the ledger can refuse, each naming what it refuses. No stringly-typed
/// errors: a consumer can match on the failure, and a failure message always carries
/// the mutant id or field it is about.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CampaignError {
    /// A binding field was empty, whitespace-only, or (for digests) not hexadecimal.
    BindingFieldInvalid { field: &'static str },
    /// An exclusion was declared without evidence. This is the denominator-drop
    /// refusal: without it, a campaign shrinks its denominator silently.
    ExclusionWithoutEvidence {
        mutant_id: String,
        kind: &'static str,
    },
    /// A mutant id was registered twice.
    DuplicateRegistration { mutant_id: String },
    /// A run was recorded for a mutant the ledger has never registered.
    UnknownMutant { mutant_id: String },
    /// A run was recorded for a mutant already excluded from the denominator. Either
    /// the exclusion or the run is a mistake; the ledger does not guess which.
    RunOnExcludedMutant { mutant_id: String },
    /// A mutant got a second verdict in one campaign. Re-runs are new ledgers, not
    /// overwrites — an overwrite is how a first `Survived` quietly becomes a kill.
    DuplicateRun { mutant_id: String },
    /// An NDJSON row did not parse, carried the wrong schema, or was noncanonical.
    NdjsonInvalid { reason: String },
}

impl fmt::Display for CampaignError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BindingFieldInvalid { field } => {
                write!(
                    f,
                    "mutant binding field `{field}` is empty, blank, or shapeless"
                )
            }
            Self::ExclusionWithoutEvidence { mutant_id, kind } => write!(
                f,
                "mutant `{mutant_id}` is declared {kind} with no evidence: the \
                 denominator may not shrink silently"
            ),
            Self::DuplicateRegistration { mutant_id } => {
                write!(f, "mutant `{mutant_id}` registered twice")
            }
            Self::UnknownMutant { mutant_id } => {
                write!(f, "run recorded for unregistered mutant `{mutant_id}`")
            }
            Self::RunOnExcludedMutant { mutant_id } => write!(
                f,
                "run recorded for excluded mutant `{mutant_id}`: the exclusion and the \
                 run contradict each other"
            ),
            Self::DuplicateRun { mutant_id } => write!(
                f,
                "mutant `{mutant_id}` already has a verdict in this campaign: re-runs \
                 are new ledgers, never overwrites"
            ),
            Self::NdjsonInvalid { reason } => write!(f, "invalid kill-ledger NDJSON: {reason}"),
        }
    }
}

impl std::error::Error for CampaignError {}

fn require_field(value: &str, field: &'static str) -> Result<String, CampaignError> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return Err(CampaignError::BindingFieldInvalid { field });
    }
    Ok(trimmed.to_string())
}

fn require_hex(value: &str, field: &'static str) -> Result<String, CampaignError> {
    let trimmed = require_field(value, field)?;
    // A digest binds bytes; a non-hex token is a label, not a bind. Length is left to
    // the producer (git's 40, fln_hash's 64) — the law is hex, not one digest length.
    if trimmed.len() < 8 || !trimmed.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(CampaignError::BindingFieldInvalid { field });
    }
    Ok(trimmed)
}

impl MutantBinding {
    /// Construct a binding, validating all seven binds. The error names the first
    /// invalid field.
    pub fn new(
        mutant_id: &str,
        source_root_digest: &str,
        patch_digest: &str,
        build_identity: &str,
        target_path: &str,
        expected_discriminator: &str,
        release_exclusion_proof: &str,
    ) -> Result<Self, CampaignError> {
        Ok(Self {
            mutant_id: require_field(mutant_id, "mutant_id")?,
            source_root_digest: require_hex(source_root_digest, "source_root_digest")?,
            patch_digest: require_hex(patch_digest, "patch_digest")?,
            build_identity: require_field(build_identity, "build_identity")?,
            target_path: require_field(target_path, "target_path")?,
            expected_discriminator: require_field(
                expected_discriminator,
                "expected_discriminator",
            )?,
            release_exclusion_proof: require_field(
                release_exclusion_proof,
                "release_exclusion_proof",
            )?,
        })
    }
}

/// One registered mutant: its binding, its disposition, and the verdict of its run
/// (at most one per campaign — see [`CampaignError::DuplicateRun`]).
#[derive(Debug, Clone)]
struct LedgerRow {
    binding: MutantBinding,
    disposition: Disposition,
    verdict: Option<KillVerdict>,
}

/// The per-campaign summary. Every count is exact; there is no rate and no headline
/// percentage, per D6 — aggregation is the consumer's problem and percentages are not
/// evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LedgerSummary {
    /// Every registered mutant, including the excluded.
    pub registered: usize,
    /// The denominator: registered minus evidenced exclusions.
    pub active: usize,
    /// Evidenced equivalent mutants (counted, outside the denominator).
    pub equivalent: usize,
    /// Evidenced unbuildable mutants (counted, outside the denominator).
    pub unbuildable: usize,
    /// Runs that killed for the stated reason.
    pub killed: usize,
    /// Runs the mutant survived.
    pub survived: usize,
    /// Runs that are not kills and not survivals (all five [`NotAKill`] kinds).
    pub not_killed: usize,
}

impl LedgerSummary {
    /// The conservation law: every run is accounted for, and only active mutants run.
    /// `killed + survived + not_killed` is the number of recorded runs, which can never
    /// exceed the denominator. If this ever disagrees with the row vector the ledger
    /// is corrupt; the summary is derived from the rows, so the law holds by
    /// construction — the suite plants against it anyway, because a law nobody tests
    /// is a claim.
    pub fn runs(&self) -> usize {
        self.killed + self.survived + self.not_killed
    }
}

/// The kill ledger: one campaign's registered mutants and their accounted runs.
#[derive(Debug, Default)]
pub struct KillLedger {
    rows: BTreeMap<String, LedgerRow>,
}

impl KillLedger {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a mutant. Exclusions are validated here: evidence or nothing.
    pub fn register(
        &mut self,
        binding: MutantBinding,
        disposition: Disposition,
    ) -> Result<(), CampaignError> {
        let mutant_id = binding.mutant_id.clone();
        match &disposition {
            Disposition::Equivalent { evidence } if evidence.trim().is_empty() => {
                return Err(CampaignError::ExclusionWithoutEvidence {
                    mutant_id,
                    kind: "equivalent",
                });
            }
            Disposition::Unbuildable { evidence } if evidence.trim().is_empty() => {
                return Err(CampaignError::ExclusionWithoutEvidence {
                    mutant_id,
                    kind: "unbuildable",
                });
            }
            _ => {}
        }
        if self.rows.contains_key(&mutant_id) {
            return Err(CampaignError::DuplicateRegistration { mutant_id });
        }
        self.rows.insert(
            mutant_id,
            LedgerRow {
                binding,
                disposition,
                verdict: None,
            },
        );
        Ok(())
    }

    /// Record one run of the discriminating test under a mutant. Returns the settled
    /// verdict so the caller cannot misclassify it afterwards.
    pub fn record(
        &mut self,
        mutant_id: &str,
        observation: Observation,
    ) -> Result<KillVerdict, CampaignError> {
        let row = self
            .rows
            .get_mut(mutant_id)
            .ok_or_else(|| CampaignError::UnknownMutant {
                mutant_id: mutant_id.to_string(),
            })?;
        if !matches!(row.disposition, Disposition::Active) {
            return Err(CampaignError::RunOnExcludedMutant {
                mutant_id: mutant_id.to_string(),
            });
        }
        if row.verdict.is_some() {
            return Err(CampaignError::DuplicateRun {
                mutant_id: mutant_id.to_string(),
            });
        }
        let verdict = observation.verdict();
        row.verdict = Some(verdict);
        Ok(verdict)
    }

    /// Derive the summary. Conservation holds by construction; the suite plants
    /// against it regardless.
    pub fn summary(&self) -> LedgerSummary {
        let mut summary = LedgerSummary {
            registered: self.rows.len(),
            active: 0,
            equivalent: 0,
            unbuildable: 0,
            killed: 0,
            survived: 0,
            not_killed: 0,
        };
        for row in self.rows.values() {
            match &row.disposition {
                Disposition::Active => summary.active += 1,
                Disposition::Equivalent { .. } => summary.equivalent += 1,
                Disposition::Unbuildable { .. } => summary.unbuildable += 1,
            }
            match row.verdict {
                Some(KillVerdict::Killed) => summary.killed += 1,
                Some(KillVerdict::Survived) => summary.survived += 1,
                Some(KillVerdict::NotKilled(_)) => summary.not_killed += 1,
                None => {}
            }
        }
        summary
    }

    /// The completion law: a campaign is complete only when every active mutant has
    /// exactly one verdict. Returns the ids of the unrun mutants, sorted (the map is
    /// ordered), so a short campaign is named rather than averaged away.
    pub fn unrun_mutants(&self) -> Vec<String> {
        self.rows
            .values()
            .filter(|row| matches!(row.disposition, Disposition::Active) && row.verdict.is_none())
            .map(|row| row.binding.mutant_id.clone())
            .collect()
    }

    /// Emit the ledger as schema-versioned NDJSON, one row per mutant, canonical:
    /// keys in fixed order, one line per row, rows ordered by mutant id. This is the
    /// artifact a retention check can later bind to a tree.
    pub fn to_ndjson(&self) -> String {
        let mut out = String::new();
        for row in self.rows.values() {
            let (disposition, exclusion_evidence) = match &row.disposition {
                Disposition::Active => ("active", None),
                Disposition::Equivalent { evidence } => ("equivalent", Some(evidence.as_str())),
                Disposition::Unbuildable { evidence } => ("unbuildable", Some(evidence.as_str())),
            };
            let (verdict, not_a_kill) = match row.verdict {
                Some(KillVerdict::Killed) => ("killed", None),
                Some(KillVerdict::Survived) => ("survived", None),
                Some(KillVerdict::NotKilled(kind)) => ("not_killed", Some(kind.token())),
                None => ("unrun", None),
            };
            out.push_str(&json_row(&[
                ("schema", KILL_LEDGER_SCHEMA),
                ("mutant_id", &row.binding.mutant_id),
                ("source_root_digest", &row.binding.source_root_digest),
                ("patch_digest", &row.binding.patch_digest),
                ("build_identity", &row.binding.build_identity),
                ("target_path", &row.binding.target_path),
                (
                    "expected_discriminator",
                    &row.binding.expected_discriminator,
                ),
                (
                    "release_exclusion_proof",
                    &row.binding.release_exclusion_proof,
                ),
                ("disposition", disposition),
                ("exclusion_evidence", exclusion_evidence.unwrap_or("")),
                ("verdict", verdict),
                ("not_a_kill", not_a_kill.unwrap_or("")),
            ]));
            out.push('\n');
        }
        out
    }

    /// Parse one NDJSON row back into a binding, disposition, and verdict. Strict:
    /// the schema token must match exactly, every field must be present, unknown
    /// verdict and exclusion tokens are refused, and the reconstructed binding goes
    /// through the same validation as a fresh one — a tampered row fails at the same
    /// laws a hand-written one does.
    pub fn row_from_ndjson(
        line: &str,
    ) -> Result<(MutantBinding, Disposition, Option<KillVerdict>), CampaignError> {
        let fields = parse_json_object(line)?;
        let get = |key: &str| -> Result<&str, CampaignError> {
            fields
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v.as_str())
                .ok_or_else(|| CampaignError::NdjsonInvalid {
                    reason: format!("missing field `{key}`"),
                })
        };
        let schema = get("schema")?;
        if schema != KILL_LEDGER_SCHEMA {
            return Err(CampaignError::NdjsonInvalid {
                reason: format!("schema `{schema}` is not `{KILL_LEDGER_SCHEMA}`"),
            });
        }
        let binding = MutantBinding::new(
            get("mutant_id")?,
            get("source_root_digest")?,
            get("patch_digest")?,
            get("build_identity")?,
            get("target_path")?,
            get("expected_discriminator")?,
            get("release_exclusion_proof")?,
        )?;
        let disposition = match get("disposition")? {
            "active" => Disposition::Active,
            "equivalent" => Disposition::Equivalent {
                evidence: get("exclusion_evidence")?.to_string(),
            },
            "unbuildable" => Disposition::Unbuildable {
                evidence: get("exclusion_evidence")?.to_string(),
            },
            other => {
                return Err(CampaignError::NdjsonInvalid {
                    reason: format!("unknown disposition `{other}`"),
                });
            }
        };
        let verdict = match get("verdict")? {
            "unrun" => None,
            "killed" => Some(KillVerdict::Killed),
            "survived" => Some(KillVerdict::Survived),
            "not_killed" => Some(KillVerdict::NotKilled(
                NotAKill::from_token(get("not_a_kill")?).ok_or_else(|| {
                    CampaignError::NdjsonInvalid {
                        reason: "unknown not_a_kill token".to_string(),
                    }
                })?,
            )),
            other => {
                return Err(CampaignError::NdjsonInvalid {
                    reason: format!("unknown verdict `{other}`"),
                });
            }
        };
        Ok((binding, disposition, verdict))
    }
}

/// JSON string quoting, the house convention (cli_lake_census::json_quote): minimal
/// and exact, no serde (D1).
fn json_quote(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_row(fields: &[(&str, &str)]) -> String {
    let mut out = String::from("{");
    for (i, (key, value)) in fields.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&json_quote(key));
        out.push(':');
        out.push_str(&json_quote(value));
    }
    out.push('}');
    out
}

/// A strict little object parser for the emitter's own row shape: flat, string-valued,
/// no nesting. Anything richer is refused rather than misread.
fn parse_json_object(line: &str) -> Result<Vec<(String, String)>, CampaignError> {
    let invalid = |reason: &str| CampaignError::NdjsonInvalid {
        reason: reason.to_string(),
    };
    let body = line
        .trim()
        .strip_prefix('{')
        .and_then(|s| s.strip_suffix('}'))
        .ok_or_else(|| invalid("row is not a flat object"))?;
    let mut fields = Vec::new();
    let mut rest = body;
    while !rest.is_empty() {
        if !rest.starts_with('"') {
            return Err(invalid("key is not a quoted string"));
        }
        let (key, after_key) = parse_json_string(rest)?;
        let after_colon = after_key
            .strip_prefix(':')
            .ok_or_else(|| invalid("missing colon after key"))?;
        if !after_colon.starts_with('"') {
            return Err(invalid("value is not a quoted string"));
        }
        let (value, after_value) = parse_json_string(after_colon)?;
        fields.push((key, value));
        rest = match after_value.strip_prefix(',') {
            Some(next) => next,
            None if after_value.is_empty() => "",
            None => return Err(invalid("trailing garbage after value")),
        };
    }
    Ok(fields)
}

/// Parse one quoted string at the head of `input`, returning the decoded string and
/// the remainder. Handles exactly the escapes the emitter produces.
fn parse_json_string(input: &str) -> Result<(String, &str), CampaignError> {
    let invalid = |reason: &str| CampaignError::NdjsonInvalid {
        reason: reason.to_string(),
    };
    let mut chars = input.char_indices();
    if chars.next().map(|(_, c)| c) != Some('"') {
        return Err(invalid("expected opening quote"));
    }
    let mut out = String::new();
    while let Some((i, c)) = chars.next() {
        match c {
            '"' => return Ok((out, &input[i + 1..])),
            '\\' => match chars.next() {
                Some((_, '"')) => out.push('"'),
                Some((_, '\\')) => out.push('\\'),
                Some((_, 'n')) => out.push('\n'),
                Some((_, 'r')) => out.push('\r'),
                Some((_, 't')) => out.push('\t'),
                Some((_, 'u')) => {
                    let mut code = 0u32;
                    for _ in 0..4 {
                        match chars.next() {
                            Some((_, d)) if d.is_ascii_hexdigit() => {
                                code = code * 16 + d.to_digit(16).unwrap_or(0);
                            }
                            _ => return Err(invalid("bad unicode escape")),
                        }
                    }
                    out.push(char::from_u32(code).ok_or_else(|| invalid("bad codepoint"))?);
                }
                _ => return Err(invalid("unknown escape")),
            },
            c => out.push(c),
        }
    }
    Err(invalid("unterminated string"))
}
