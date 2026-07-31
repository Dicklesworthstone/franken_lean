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

// ---------------------------------------------------------------------------
// Framework 2: the campaign owner matrix (ci/CAMPAIGN_OWNER_MATRIX.txt)
// ---------------------------------------------------------------------------

/// The six reusable campaign families td9 owns. The matrix's adapter rows make each
/// family mandatory on named subsystem owners; a framework existing is never the same
/// thing as its production adapter being active.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CampaignFamily {
    Mutation,
    Fuzz,
    FaultDrill,
    Shrink,
    NoMockAttestation,
    ThreadMatrix,
}

impl CampaignFamily {
    pub fn token(self) -> &'static str {
        match self {
            Self::Mutation => "mutation",
            Self::Fuzz => "fuzz",
            Self::FaultDrill => "fault-drill",
            Self::Shrink => "shrink",
            Self::NoMockAttestation => "no-mock-attestation",
            Self::ThreadMatrix => "thread-matrix",
        }
    }

    fn from_token(token: &str) -> Option<Self> {
        match token {
            "mutation" => Some(Self::Mutation),
            "fuzz" => Some(Self::Fuzz),
            "fault-drill" => Some(Self::FaultDrill),
            "shrink" => Some(Self::Shrink),
            "no-mock-attestation" => Some(Self::NoMockAttestation),
            "thread-matrix" => Some(Self::ThreadMatrix),
            _ => None,
        }
    }
}

/// An adapter's activation state. The gate law is the whole point of the type:
/// only `Green` satisfies a downstream gate, and `Green` is unconstructable at parse
/// time without its run evidence — so a registered-but-inactive adapter cannot
/// satisfy anything, and an evidence-less upgrade cannot be written down.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdapterState {
    /// Declared in the matrix only. Satisfies no gate.
    Registered,
    /// Wired into the owner's rig; the evidence names the wiring.
    Active { evidence: String },
    /// Active and currently passing; the evidence names the run.
    Green { evidence: String },
}

impl AdapterState {
    /// The gate law (td9): "a registered-but-inactive production adapter cannot
    /// satisfy its downstream gate" — and only a green one can.
    pub fn satisfies_gate(&self) -> bool {
        matches!(self, Self::Green { .. })
    }
}

/// One adapter row: a campaign family owed by a subsystem owner on a target domain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdapterRow {
    /// The bead's domains: grammar-source, kernel-terms, olean-read, olean-write,
    /// vm-opcodes, cas-manifest, server-editor.
    pub domain: String,
    pub family: CampaignFamily,
    /// The bead that owns the adapter and cannot close its downstream gate until the
    /// adapter is green.
    pub owner_bead: String,
    pub state: AdapterState,
    /// The 1-based line in the matrix file, so findings name their site.
    pub line: usize,
}

/// One invariant row: a campaign id bound to the FL-INV ids it feeds (td9's design
/// law — e.g. the thread matrix is the standing FL-INV-01 enforcement lane).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvariantRow {
    pub campaign: String,
    pub inv_ids: Vec<String>,
    pub line: usize,
}

/// The parsed matrix.
#[derive(Debug, Clone, Default)]
pub struct OwnerMatrix {
    pub adapters: Vec<AdapterRow>,
    pub invariants: Vec<InvariantRow>,
}

/// The matrix file's schema token.
pub const OWNER_MATRIX_SCHEMA: &str = "fln-campaign-owner-matrix/1";

/// Every way a matrix file can be refused, each naming its line. Validation findings
/// (as opposed to parse refusals) are returned as a list: a broken matrix reports
/// everything wrong with it, not just the first thing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatrixError {
    /// The first non-comment line was not the schema declaration, or carried a
    /// different token.
    Schema { found: String },
    /// A row's shape is wrong; the message says what and the line says where.
    Malformed { line: usize, reason: String },
    /// A family token no campaign owns.
    UnknownFamily { line: usize, token: String },
    /// A state token outside registered/active/green.
    UnknownState { line: usize, token: String },
    /// `active` or `green` written without evidence — the honesty law that makes the
    /// gate ungameable in text.
    StateWithoutEvidence { line: usize, state: &'static str },
    /// An FL-INV id outside the seven the type theory declares.
    UnknownInvariant { line: usize, token: String },
    /// The same (domain, family, owner) adapter declared twice.
    DuplicateAdapter {
        line: usize,
        domain: String,
        family: &'static str,
    },
    /// A domain the bead does not assign to any owner got an adapter row. Validation
    /// (not parse), because the domain set is the bead's own and moves with it.
    UnknownDomain { line: usize, domain: String },
    /// An owner bead that does not exist in the tracker.
    UnknownOwnerBead { line: usize, bead: String },
    /// A declared domain with no adapter rows at all (validation, totality).
    DomainWithoutAdapter { domain: String },
    /// An FL-INV id no invariant row feeds (validation, totality).
    InvariantUnfed { inv_id: String },
}

impl fmt::Display for MatrixError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Schema { found } => write!(
                f,
                "the matrix must open with `schema {OWNER_MATRIX_SCHEMA}`, found `{found}`"
            ),
            Self::Malformed { line, reason } => write!(f, "line {line}: {reason}"),
            Self::UnknownFamily { line, token } => {
                write!(f, "line {line}: unknown campaign family `{token}`")
            }
            Self::UnknownState { line, token } => {
                write!(f, "line {line}: unknown adapter state `{token}`")
            }
            Self::StateWithoutEvidence { line, state } => write!(
                f,
                "line {line}: state `{state}` requires evidence; an evidence-less upgrade \
                 is how a gate gets gamed in text"
            ),
            Self::UnknownInvariant { line, token } => {
                write!(f, "line {line}: `{token}` is not one of FL-INV-01..07")
            }
            Self::DuplicateAdapter {
                line,
                domain,
                family,
            } => write!(
                f,
                "line {line}: adapter ({domain}, {family}) is already declared"
            ),
            Self::UnknownDomain { line, domain } => {
                write!(
                    f,
                    "line {line}: `{domain}` is not a domain the bead assigns"
                )
            }
            Self::UnknownOwnerBead { line, bead } => {
                write!(
                    f,
                    "line {line}: owner bead `{bead}` does not exist in the tracker"
                )
            }
            Self::DomainWithoutAdapter { domain } => {
                write!(f, "domain `{domain}` has no adapter rows")
            }
            Self::InvariantUnfed { inv_id } => {
                write!(f, "{inv_id} is fed by no campaign row")
            }
        }
    }
}

impl std::error::Error for MatrixError {}

/// The domains td9 assigns, in the bead's own words: grammar/source on Vellum, kernel
/// terms on the kernel differential rig, region/OLEAN on the W2 codecs (read and
/// write separately), VM opcodes on Golem/FLBC, CAS/manifest on the W8 Ledger, and
/// server/editor on the replay/protocol rigs.
pub const MATRIX_DOMAINS: [&str; 7] = [
    "grammar-source",
    "kernel-terms",
    "olean-read",
    "olean-write",
    "vm-opcodes",
    "cas-manifest",
    "server-editor",
];

/// The seven invariants, derived from the FL-INV numbering rather than transcribed.
pub fn all_inv_ids() -> Vec<String> {
    (1..=7).map(|n| format!("FL-INV-0{n}")).collect()
}

impl OwnerMatrix {
    /// Parse a matrix file. Structural refusals are returned immediately; semantic
    /// findings (unknown domains, unknown beads, totality) come from [`Self::validate`].
    pub fn parse(text: &str) -> Result<Self, MatrixError> {
        let mut matrix = OwnerMatrix::default();
        let mut schema_seen = false;
        for (index, raw) in text.lines().enumerate() {
            let line = index + 1;
            let trimmed = raw.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            if !schema_seen {
                match trimmed.strip_prefix("schema ") {
                    Some(token) if token.trim() == OWNER_MATRIX_SCHEMA => {
                        schema_seen = true;
                        continue;
                    }
                    _ => {
                        return Err(MatrixError::Schema {
                            found: trimmed.to_string(),
                        });
                    }
                }
            }
            if let Some(rest) = trimmed.strip_prefix("adapter ") {
                matrix.adapters.push(parse_adapter_row(rest, line)?);
            } else if let Some(rest) = trimmed.strip_prefix("invariant ") {
                matrix.invariants.push(parse_invariant_row(rest, line)?);
            } else {
                return Err(MatrixError::Malformed {
                    line,
                    reason: "row kind is neither `adapter` nor `invariant`".to_string(),
                });
            }
        }
        if !schema_seen {
            return Err(MatrixError::Schema {
                found: "<file carried no schema line>".to_string(),
            });
        }
        Ok(matrix)
    }

    /// The semantic laws, as a list of every violation found: totality (every domain
    /// adapted, every invariant fed), real owners (the callback answers whether a bead
    /// exists), declared domains only, no duplicate adapters.
    pub fn validate(&self, bead_exists: impl Fn(&str) -> bool) -> Vec<MatrixError> {
        let mut errors = Vec::new();
        for row in &self.adapters {
            if !MATRIX_DOMAINS.contains(&row.domain.as_str()) {
                errors.push(MatrixError::UnknownDomain {
                    line: row.line,
                    domain: row.domain.clone(),
                });
            }
            if !bead_exists(&row.owner_bead) {
                errors.push(MatrixError::UnknownOwnerBead {
                    line: row.line,
                    bead: row.owner_bead.clone(),
                });
            }
        }
        for domain in MATRIX_DOMAINS {
            if !self.adapters.iter().any(|row| row.domain == domain) {
                errors.push(MatrixError::DomainWithoutAdapter {
                    domain: domain.to_string(),
                });
            }
        }
        let mut seen: BTreeMap<(&str, CampaignFamily, &str), usize> = BTreeMap::new();
        for row in &self.adapters {
            let key = (row.domain.as_str(), row.family, row.owner_bead.as_str());
            if seen.insert(key, row.line).is_some() {
                errors.push(MatrixError::DuplicateAdapter {
                    line: row.line,
                    domain: row.domain.clone(),
                    family: row.family.token(),
                });
            }
        }
        for inv_id in all_inv_ids() {
            if !self
                .invariants
                .iter()
                .any(|row| row.inv_ids.contains(&inv_id))
            {
                errors.push(MatrixError::InvariantUnfed { inv_id });
            }
        }
        errors
    }

    /// The gate law, applied: the adapter for (domain, family) satisfies its
    /// downstream gate only when green. An absent row satisfies nothing — a gate
    /// cannot be satisfied by an adapter nobody declared.
    pub fn satisfies_downstream_gate(&self, domain: &str, family: CampaignFamily) -> bool {
        self.adapters
            .iter()
            .filter(|row| row.domain == domain && row.family == family)
            .any(|row| row.state.satisfies_gate())
    }
}

fn parse_adapter_row(rest: &str, line: usize) -> Result<AdapterRow, MatrixError> {
    let fields: Vec<&str> = rest.split('|').map(str::trim).collect();
    if fields.len() < 4 {
        return Err(MatrixError::Malformed {
            line,
            reason: "an adapter row needs <domain> | <family> | <owner bead> | <state>".to_string(),
        });
    }
    let family =
        CampaignFamily::from_token(fields[1]).ok_or_else(|| MatrixError::UnknownFamily {
            line,
            token: fields[1].to_string(),
        })?;
    let evidence = fields.get(4).copied().unwrap_or("");
    let state = match fields[3] {
        "registered" => AdapterState::Registered,
        "active" => {
            if evidence.is_empty() {
                return Err(MatrixError::StateWithoutEvidence {
                    line,
                    state: "active",
                });
            }
            AdapterState::Active {
                evidence: evidence.to_string(),
            }
        }
        "green" => {
            if evidence.is_empty() {
                return Err(MatrixError::StateWithoutEvidence {
                    line,
                    state: "green",
                });
            }
            AdapterState::Green {
                evidence: evidence.to_string(),
            }
        }
        other => {
            return Err(MatrixError::UnknownState {
                line,
                token: other.to_string(),
            });
        }
    };
    if fields[0].is_empty() || fields[2].is_empty() {
        return Err(MatrixError::Malformed {
            line,
            reason: "domain and owner bead must be non-empty".to_string(),
        });
    }
    Ok(AdapterRow {
        domain: fields[0].to_string(),
        family,
        owner_bead: fields[2].to_string(),
        state,
        line,
    })
}

fn parse_invariant_row(rest: &str, line: usize) -> Result<InvariantRow, MatrixError> {
    let fields: Vec<&str> = rest.split('|').map(str::trim).collect();
    if fields.len() < 2 || fields[0].is_empty() {
        return Err(MatrixError::Malformed {
            line,
            reason: "an invariant row needs <campaign id> | <FL-INV id>...".to_string(),
        });
    }
    let all = all_inv_ids();
    let mut inv_ids = Vec::new();
    for token in &fields[1..] {
        if token.is_empty() {
            continue;
        }
        if !all.iter().any(|id| id == token) {
            return Err(MatrixError::UnknownInvariant {
                line,
                token: token.to_string(),
            });
        }
        inv_ids.push(token.to_string());
    }
    if inv_ids.is_empty() {
        return Err(MatrixError::Malformed {
            line,
            reason: "an invariant row must feed at least one FL-INV id".to_string(),
        });
    }
    Ok(InvariantRow {
        campaign: fields[0].to_string(),
        inv_ids,
        line,
    })
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

// ---------------------------------------------------------------------------
// Framework 3: budgeted fuzz generation and replay
// ---------------------------------------------------------------------------

/// splitmix64 — the same eight lines the per-suite `common` modules carry, chosen
/// because it has no state beyond a `u64` and passes the statistical bar for choosing
/// test inputs. Promoted here so a campaign's seed means the same stream everywhere;
/// the per-crate commons keep their copies until their owners migrate them (td9's
/// adapters are downstream work, not this framework's).
#[derive(Debug, Clone)]
pub struct Splitmix64(u64);

impl Splitmix64 {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..n`, or 0 when `n` is 0.
    pub fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next_u64() % n as u64) as usize
        }
    }

    /// `n` deterministic bytes.
    pub fn bytes(&mut self, n: usize) -> Vec<u8> {
        let mut out = Vec::with_capacity(n);
        while out.len() < n {
            out.extend_from_slice(&self.next_u64().to_le_bytes());
        }
        out.truncate(n);
        out
    }
}

/// The budget a fuzz run answers to (td9: "budgeted fuzz generation/replay"). Every
/// dimension is checked per case; meeting one stops the run and is *reported*, never
/// silently truncated — a budget is an FL-INV-07 resource limit, and exhaustion is a
/// typed answer, not a crash and not a quiet short count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuzzBudget {
    /// The design's case count: reaching it is completion, not exhaustion.
    pub max_cases: u64,
    /// Largest single generated input, in bytes. A generator asking for more is
    /// refused once and the run ends typed.
    pub max_input_bytes: usize,
    /// Wall-clock ceiling. Checked per case; a generator or oracle that hangs is
    /// out of scope for the model (that is what the timeout kill-switch on the
    /// *lane* is for), but a long series of slow cases is caught here.
    pub max_duration: std::time::Duration,
}

/// Why a run stopped. `CasesCompleted` is the only successful end; everything else is
/// a typed non-answer or a finding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FuzzStop {
    /// All `max_cases` cases ran with no failure.
    CasesCompleted,
    /// The wall-clock ceiling was met mid-run. Typed exhaustion (FL-INV-07).
    DurationExhausted,
    /// A generated input exceeded `max_input_bytes`. Typed exhaustion.
    InputBytesExhausted { case_index: u64 },
    /// The oracle failed on this case. The seed plus this index reproduce the
    /// failing input exactly — a fuzz failure nobody can replay is a rumour.
    FailureFound { case_index: u64, detail: String },
}

/// What the oracle says about one input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaseOutcome {
    Pass,
    Fail { detail: String },
}

/// The replay receipt (schema `fln.fuzz-replay/1`): everything a later run needs to
/// reproduce this one — generator, target, build, seed, algorithm, budget, stop —
/// plus the D7 class, which for fuzzing is always `statistical`: a fuzz campaign
/// detects counterexamples and never proves an invariant (td9's D7 law, so a receipt
/// can never be cited as proof of the property it sampled).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuzzReceipt {
    pub generator: String,
    pub target: String,
    pub build: String,
    pub seed: u64,
    pub prng: String,
    pub budget: FuzzBudget,
    pub cases_run: u64,
    pub stop: FuzzStop,
}

/// The receipt schema token.
pub const FUZZ_RECEIPT_SCHEMA: &str = "fln.fuzz-replay/1";

/// The PRNG algorithm id, so a receipt's stream is reproducible under exactly one
/// algorithm — if the workspace ever grows a second generator, old receipts still
/// mean the stream they meant.
pub const FUZZ_PRNG_ID: &str = "splitmix64";

/// The D7 claim class every fuzz receipt carries.
pub const FUZZ_CLAIM_CLASS: &str = "statistical";

impl FuzzReceipt {
    /// Emit the receipt as one canonical NDJSON row (keys in fixed order).
    pub fn to_ndjson(&self) -> String {
        let (stop_token, stop_detail) = match &self.stop {
            FuzzStop::CasesCompleted => ("cases_completed", String::new()),
            FuzzStop::DurationExhausted => ("duration_exhausted", String::new()),
            FuzzStop::InputBytesExhausted { case_index } => {
                ("input_bytes_exhausted", case_index.to_string())
            }
            FuzzStop::FailureFound { case_index, detail } => {
                ("failure_found", format!("{case_index}: {detail}"))
            }
        };
        let mut out = json_row(&[
            ("schema", FUZZ_RECEIPT_SCHEMA),
            ("class", FUZZ_CLAIM_CLASS),
            ("generator", &self.generator),
            ("target", &self.target),
            ("build", &self.build),
            ("seed", &self.seed.to_string()),
            ("prng", &self.prng),
            ("max_cases", &self.budget.max_cases.to_string()),
            ("max_input_bytes", &self.budget.max_input_bytes.to_string()),
            (
                "max_duration_ms",
                &self.budget.max_duration.as_millis().to_string(),
            ),
            ("cases_run", &self.cases_run.to_string()),
            ("stop", stop_token),
            ("stop_detail", &stop_detail),
        ]);
        out.push('\n');
        out
    }

    /// Parse a receipt row back, strictly: the schema token is exact, every field is
    /// present, numbers parse, and the stop token is one of the four.
    pub fn from_ndjson(line: &str) -> Result<Self, CampaignError> {
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
        if get("schema")? != FUZZ_RECEIPT_SCHEMA {
            return Err(CampaignError::NdjsonInvalid {
                reason: format!("schema is not `{FUZZ_RECEIPT_SCHEMA}`"),
            });
        }
        let number = |key: &str| -> Result<u64, CampaignError> {
            get(key)?
                .parse::<u64>()
                .map_err(|_| CampaignError::NdjsonInvalid {
                    reason: format!("field `{key}` is not a u64"),
                })
        };
        let stop = match get("stop")? {
            "cases_completed" => FuzzStop::CasesCompleted,
            "duration_exhausted" => FuzzStop::DurationExhausted,
            "input_bytes_exhausted" => FuzzStop::InputBytesExhausted {
                case_index: get("stop_detail")?.parse::<u64>().map_err(|_| {
                    CampaignError::NdjsonInvalid {
                        reason: "stop_detail is not a case index".to_string(),
                    }
                })?,
            },
            "failure_found" => {
                let detail = get("stop_detail")?;
                let (index, text) =
                    detail
                        .split_once(": ")
                        .ok_or_else(|| CampaignError::NdjsonInvalid {
                            reason: "failure stop_detail does not carry `<index>: <detail>`"
                                .to_string(),
                        })?;
                FuzzStop::FailureFound {
                    case_index: index
                        .parse::<u64>()
                        .map_err(|_| CampaignError::NdjsonInvalid {
                            reason: "failure case index is not a u64".to_string(),
                        })?,
                    detail: text.to_string(),
                }
            }
            other => {
                return Err(CampaignError::NdjsonInvalid {
                    reason: format!("unknown stop token `{other}`"),
                });
            }
        };
        Ok(Self {
            generator: get("generator")?.to_string(),
            target: get("target")?.to_string(),
            build: get("build")?.to_string(),
            seed: number("seed")?,
            prng: get("prng")?.to_string(),
            budget: FuzzBudget {
                max_cases: number("max_cases")?,
                max_input_bytes: number("max_input_bytes")? as usize,
                max_duration: std::time::Duration::from_millis(number("max_duration_ms")?),
            },
            cases_run: number("cases_run")?,
            stop,
        })
    }
}

/// The runner. Given a deterministic generator and an oracle, execute cases within
/// the budget and return the receipt. The runner never writes anything — artifacts
/// are the caller's explicit choice (td9: campaigns leave no automatic workspace
/// edits), so the model carries no path at all.
pub struct FuzzRunner {
    pub generator: String,
    pub target: String,
    pub build: String,
    pub budget: FuzzBudget,
    pub seed: u64,
}

impl FuzzRunner {
    /// Run the campaign. The generator receives the PRNG and the case index; the
    /// oracle judges each input; `measure` reports an input's size for the byte
    /// budget (a generic input carries no length of its own — `size_of_val` would
    /// measure the type, which is a bug, not a budget). Deterministic by
    /// construction: the same seed, generator, and oracle produce the same receipt
    /// modulo `cases_run` under a duration stop (wall time is the one
    /// non-reproducible dimension, and the receipt records it as what it is).
    pub fn run<I>(
        &self,
        mut generate: impl FnMut(&mut Splitmix64, u64) -> I,
        mut measure: impl FnMut(&I) -> usize,
        mut oracle: impl FnMut(&I) -> CaseOutcome,
    ) -> FuzzReceipt {
        let mut rng = Splitmix64::new(self.seed);
        let started = std::time::Instant::now();
        let mut cases_run = 0u64;
        let mut stop = FuzzStop::CasesCompleted;
        for case_index in 0..self.budget.max_cases {
            if started.elapsed() > self.budget.max_duration {
                stop = FuzzStop::DurationExhausted;
                break;
            }
            let input = generate(&mut rng, case_index);
            if measure(&input) > self.budget.max_input_bytes {
                stop = FuzzStop::InputBytesExhausted { case_index };
                break;
            }
            cases_run += 1;
            if let CaseOutcome::Fail { detail } = oracle(&input) {
                stop = FuzzStop::FailureFound { case_index, detail };
                break;
            }
        }
        FuzzReceipt {
            generator: self.generator.clone(),
            target: self.target.clone(),
            build: self.build.clone(),
            seed: self.seed,
            prng: FUZZ_PRNG_ID.to_string(),
            budget: self.budget,
            cases_run,
            stop,
        }
    }

    /// Reproduce one case's input from a receipt: the same seed, advanced to the
    /// case's index. This is the replay law made a function — the caller compares
    /// the replayed input against what the original run saw, and the campaign's
    /// claim that the failure is reproducible is checked rather than believed.
    pub fn replay_input<I>(
        receipt: &FuzzReceipt,
        case_index: u64,
        mut generate: impl FnMut(&mut Splitmix64, u64) -> I,
    ) -> I {
        let mut rng = Splitmix64::new(receipt.seed);
        let mut input = generate(&mut rng, 0);
        for index in 1..=case_index {
            input = generate(&mut rng, index);
        }
        input
    }
}

// ---------------------------------------------------------------------------
// Framework 4: the fault boundary registry
// ---------------------------------------------------------------------------

/// The platform-neutral fault capabilities (td9: "abrupt termination uses a
/// platform-neutral semantic capability with platform-specific rows rather than
/// projecting Unix signals onto Windows"). A drill declares one of these; the
/// platform row is chosen by `target_os`, never by name, so a Unix signal number
/// cannot be projected onto a platform that does not have it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum FaultCapability {
    /// Kill the process tree with no cleanup opportunity (SIGKILL row on Unix,
    /// TerminateProcess row on Windows).
    AbruptTermination,
    /// Corrupt a byte range of a durable store beneath a reader.
    CorruptStore,
    /// Fill the filesystem beneath a writer mid-append.
    DiskFull,
    /// Crash the far side of a plugin/native boundary.
    BoundaryCrash,
}

impl FaultCapability {
    pub fn token(self) -> &'static str {
        match self {
            Self::AbruptTermination => "abrupt-termination",
            Self::CorruptStore => "corrupt-store",
            Self::DiskFull => "disk-full",
            Self::BoundaryCrash => "boundary-crash",
        }
    }

    fn from_token(token: &str) -> Option<Self> {
        match token {
            "abrupt-termination" => Some(Self::AbruptTermination),
            "corrupt-store" => Some(Self::CorruptStore),
            "disk-full" => Some(Self::DiskFull),
            "boundary-crash" => Some(Self::BoundaryCrash),
            _ => None,
        }
    }

    /// The platform row realizing this capability on the running platform. The row
    /// is chosen by `target_os` at compile time — the type system, not a string
    /// comparison — so porting the drill is extending this function, never
    /// re-interpreting a Unix row somewhere else.
    pub fn platform_row(self) -> &'static str {
        #[cfg(target_os = "linux")]
        {
            match self {
                Self::AbruptTermination => "unix:SIGKILL",
                Self::CorruptStore => "unix:write-range",
                Self::DiskFull => "unix:ENOSPC",
                Self::BoundaryCrash => "unix:SIGSEGV-child",
            }
        }
        #[cfg(target_os = "macos")]
        {
            match self {
                Self::AbruptTermination => "unix:SIGKILL",
                Self::CorruptStore => "unix:write-range",
                Self::DiskFull => "unix:ENOSPC",
                Self::BoundaryCrash => "unix:SIGSEGV-child",
            }
        }
        #[cfg(target_os = "windows")]
        {
            match self {
                Self::AbruptTermination => "windows:TerminateProcess",
                Self::CorruptStore => "windows:WriteFile-range",
                Self::DiskFull => "windows:ERROR_DISK_FULL",
                Self::BoundaryCrash => "windows:child-access-violation",
            }
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
        {
            match self {
                Self::AbruptTermination => "unsupported-platform",
                Self::CorruptStore => "unsupported-platform",
                Self::DiskFull => "unsupported-platform",
                Self::BoundaryCrash => "unsupported-platform",
            }
        }
    }
}

/// One registered faultpoint: a boundary, a capability, and the product-by-product
/// expected final state vector. The expected vector is the whole point of the type:
/// td9's law is "expected final state is a product-by-product vector; restart alone
/// never passes" — a faultpoint that cannot say what the world looks like
/// afterwards is restart-as-pass in waiting, and the constructor refuses it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FaultPoint {
    /// The boundary under test (e.g. `cas-promotion`, `session-store`,
    /// `plugin-door`, `evidence-finalization`).
    pub boundary: String,
    /// The faultpoint's id within its boundary (e.g. `kill-mid-rename`).
    pub id: String,
    pub capability: FaultCapability,
    /// product -> expected final state token (e.g. `cas -> old-or-new-never-torn`).
    pub expected: BTreeMap<String, String>,
}

/// Every way a registry or a drill can be refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FaultError {
    /// A faultpoint was registered twice under one id.
    DuplicateFaultPoint { id: String },
    /// A faultpoint with no expected final state. This is the restart-as-pass
    /// refusal: without a vector, "the process restarted" would pass.
    MissingExpectedState { id: String },
    /// A drill claimed a faultpoint the census never registered — the census is
    /// frozen before the drill, so a claimed-but-unregistered point is the drill
    /// exceeding its own census.
    UnregisteredClaim { id: String },
    /// A drill claimed coverage of a boundary while registered faultpoints of that
    /// boundary stayed unclaimed — td9's "freeze a complete census before claiming
    /// every step" law, so a subset cannot read as the whole.
    IncompleteBoundaryClaim {
        boundary: String,
        unclaimed: Vec<String>,
    },
    /// An observed final state disagreed with the expected vector, per product.
    UnexpectedFinalState {
        id: String,
        mismatches: Vec<StateMismatch>,
    },
}

impl fmt::Display for FaultError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateFaultPoint { id } => write!(f, "faultpoint `{id}` registered twice"),
            Self::MissingExpectedState { id } => write!(
                f,
                "faultpoint `{id}` declares no expected final state: without a vector, \
                 restart alone would pass"
            ),
            Self::UnregisteredClaim { id } => write!(
                f,
                "drill claimed unregistered faultpoint `{id}`: the census is frozen \
                 before the drill, not after it"
            ),
            Self::IncompleteBoundaryClaim {
                boundary,
                unclaimed,
            } => write!(
                f,
                "boundary `{boundary}` claimed with registered faultpoints unclaimed: \
                 {unclaimed:?}"
            ),
            Self::UnexpectedFinalState { id, mismatches } => write!(
                f,
                "faultpoint `{id}` ended in an unexpected state: {mismatches:?}"
            ),
        }
    }
}

impl std::error::Error for FaultError {}

/// One product's final-state disagreement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateMismatch {
    pub product: String,
    pub expected: String,
    pub observed: Option<String>,
}

/// The frozen census. The registry is built once, before any drill; a drill then
/// claims against it (td9: the census is frozen before the campaign claims every
/// step, and an incomplete census cannot claim coverage).
#[derive(Debug, Default)]
pub struct FaultRegistry {
    points: BTreeMap<String, FaultPoint>,
}

impl FaultRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a faultpoint. The expected vector must be non-empty and carry no
    /// blank states — restart-as-pass is refused at the door.
    pub fn register(&mut self, point: FaultPoint) -> Result<(), FaultError> {
        if point.expected.is_empty() || point.expected.values().any(|state| state.trim().is_empty())
        {
            return Err(FaultError::MissingExpectedState { id: point.id });
        }
        if self.points.contains_key(&point.id) {
            return Err(FaultError::DuplicateFaultPoint { id: point.id });
        }
        self.points.insert(point.id.clone(), point);
        Ok(())
    }

    /// Judge a drill's claim: every claimed faultpoint must be registered, and a
    /// claimed boundary must include every registered faultpoint of that boundary.
    /// Returns every violation found, not the first.
    pub fn judge_claim(&self, boundary: &str, claimed: &BTreeMap<String, ()>) -> Vec<FaultError> {
        let mut errors = Vec::new();
        for id in claimed.keys() {
            if !self.points.contains_key(id) {
                errors.push(FaultError::UnregisteredClaim { id: id.clone() });
            }
        }
        let unclaimed: Vec<String> = self
            .points
            .values()
            .filter(|point| point.boundary == boundary && !claimed.contains_key(&point.id))
            .map(|point| point.id.clone())
            .collect();
        if !unclaimed.is_empty() {
            errors.push(FaultError::IncompleteBoundaryClaim {
                boundary: boundary.to_string(),
                unclaimed,
            });
        }
        errors
    }

    /// The final-state law: the observed vector must match the expected vector
    /// product-for-product. A product missing from the observation is a mismatch
    /// with `observed: None` — "the process restarted" answers no product's
    /// expected state, and the absence is named rather than averaged.
    pub fn judge_final_state(
        &self,
        id: &str,
        observed: &BTreeMap<String, String>,
    ) -> Result<(), FaultError> {
        let point = self
            .points
            .get(id)
            .ok_or_else(|| FaultError::UnregisteredClaim { id: id.to_string() })?;
        let mut mismatches = Vec::new();
        for (product, expected) in &point.expected {
            match observed.get(product) {
                Some(actual) if actual == expected => {}
                Some(actual) => mismatches.push(StateMismatch {
                    product: product.clone(),
                    expected: expected.clone(),
                    observed: Some(actual.clone()),
                }),
                None => mismatches.push(StateMismatch {
                    product: product.clone(),
                    expected: expected.clone(),
                    observed: None,
                }),
            }
        }
        if mismatches.is_empty() {
            Ok(())
        } else {
            Err(FaultError::UnexpectedFinalState {
                id: id.to_string(),
                mismatches,
            })
        }
    }

    /// The registered faultpoints of one boundary, in id order (the map is ordered).
    pub fn boundary_points(&self, boundary: &str) -> Vec<&FaultPoint> {
        self.points
            .values()
            .filter(|point| point.boundary == boundary)
            .collect()
    }
}

/// The fault registry file's schema token.
pub const FAULT_REGISTRY_SCHEMA: &str = "fln-fault-boundary-registry/1";

impl FaultRegistry {
    /// Parse a registry file: `schema` first, then
    /// `fault <boundary> | <id> | <capability> | <product>=<state>[,<product>=<state>...]`
    /// rows. Structural refusals name their line; the same registration laws as the
    /// in-memory API apply (no duplicates, no missing or blank expected states).
    pub fn parse(text: &str) -> Result<Self, FaultError> {
        let mut registry = Self::new();
        let mut schema_seen = false;
        for (index, raw) in text.lines().enumerate() {
            let trimmed = raw.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            if !schema_seen {
                match trimmed.strip_prefix("schema ") {
                    Some(token) if token.trim() == FAULT_REGISTRY_SCHEMA => {
                        schema_seen = true;
                        continue;
                    }
                    _ => {
                        return Err(FaultError::UnregisteredClaim {
                            id: format!(
                                "line {}: the registry must open with `schema {FAULT_REGISTRY_SCHEMA}`, found `{trimmed}`",
                                index + 1
                            ),
                        });
                    }
                }
            }
            let Some(rest) = trimmed.strip_prefix("fault ") else {
                return Err(FaultError::UnregisteredClaim {
                    id: format!("line {}: row kind is not `fault`", index + 1),
                });
            };
            let fields: Vec<&str> = rest.split('|').map(str::trim).collect();
            if fields.len() != 4 || fields[0].is_empty() || fields[1].is_empty() {
                return Err(FaultError::UnregisteredClaim {
                    id: format!(
                        "line {}: a fault row needs <boundary> | <id> | <capability> | <product>=<state>...",
                        index + 1
                    ),
                });
            }
            let capability = FaultCapability::from_token(fields[2]).ok_or_else(|| {
                FaultError::UnregisteredClaim {
                    id: format!("line {}: unknown capability `{}`", index + 1, fields[2]),
                }
            })?;
            let mut expected = BTreeMap::new();
            for pair in fields[3].split(',') {
                let Some((product, state)) = pair.trim().split_once('=') else {
                    return Err(FaultError::UnregisteredClaim {
                        id: format!(
                            "line {}: expected vector entries are <product>=<state>",
                            index + 1
                        ),
                    });
                };
                expected.insert(product.trim().to_string(), state.trim().to_string());
            }
            registry.register(FaultPoint {
                boundary: fields[0].to_string(),
                id: fields[1].to_string(),
                capability,
                expected,
            })?;
        }
        if !schema_seen {
            return Err(FaultError::UnregisteredClaim {
                id: "the registry carried no schema line".to_string(),
            });
        }
        Ok(registry)
    }

    /// How many faultpoints are registered.
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// True when the registry is empty — which a guard should read as a broken
    /// scan, never a clean tree.
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Framework 5: failure-signature-preserving shrink
// ---------------------------------------------------------------------------

/// The resource class of a failure (td9: shrinking preserves the resource class).
/// A shrink that moves a failure from one class to another has found a different
/// bug, which is a finding to record separately — never the same bug shrunk.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ResourceClass {
    /// The target rejected the input (a parse/shape refusal).
    ShapeRefusal,
    /// The target stopped on a budget (time/memory/fuel) — FL-INV-07 territory.
    ResourceStop,
    /// The target crashed or faulted.
    TargetFault,
}

impl ResourceClass {
    pub fn token(self) -> &'static str {
        match self {
            Self::ShapeRefusal => "shape-refusal",
            Self::ResourceStop => "resource-stop",
            Self::TargetFault => "target-fault",
        }
    }
}

/// The failure signature a shrink must preserve exactly (td9: "shrinking preserves
/// original failure signature, oracle authority/comparison, resource class, and
/// reproduction"). The class token is the oracle's own (a verdict kind, an error
/// variant) — free text, because the oracle is the authority and the model does
/// not second-guess its vocabulary; the resource class is the model's own taxonomy
/// and is checked separately.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FailureSignature {
    pub class: String,
    pub resource: ResourceClass,
}

/// What the oracle says about one candidate. The oracle is the named authority
/// (td9: "oracle authority/comparison" is preserved): it is one closure for the
/// whole shrink, so the comparison cannot be swapped mid-run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ShrinkVerdict {
    /// The candidate does not fail. It is never an acceptable shrink: shrinking
    /// past the failure boundary loses the failure.
    NotAFailure,
    /// The candidate fails with this signature.
    Failure(FailureSignature),
}

/// The shrink report — the candidate artifact td9 names. Emitted, never committed:
/// checking a shrunk fixture into the repository is a separate reviewed action,
/// so the report carries everything that review needs and the framework carries
/// no path at all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShrinkReport {
    /// The signature preserved through every accepted step.
    pub signature: FailureSignature,
    /// The original input's measure.
    pub original_measure: usize,
    /// The shrunk candidate's measure.
    pub final_measure: usize,
    /// Every accepted reduction's measure, in order — the lineage a reviewer
    /// replays to see the shrink rather than trust it.
    pub lineage: Vec<usize>,
    /// True when no candidate of the final input was accepted: the shrink stopped
    /// at a local minimum rather than at the round budget.
    pub local_minimum: bool,
}

/// The shrinker. Greedy: at each round, the first candidate that (a) fails and
/// (b) fails with the *preserved* signature is accepted; rounds continue until no
/// candidate is accepted (local minimum) or the round budget is met (typed stop —
/// a shrink that ran out of rounds says so rather than calling its last
/// intermediate state minimal).
pub struct Shrinker {
    /// How many candidate rounds the shrink may take before it must stop typed.
    pub max_rounds: u64,
}

impl Shrinker {
    /// Run the shrink. `candidates` produces a candidate's reductions (each strictly
    /// smaller by `measure`); `oracle` is the single named authority; `measure` is
    /// the input's size. The original input must fail, and its signature is the one
    /// preserved — a shrink over a non-failing input is refused with `None`, because
    /// there is nothing to preserve.
    pub fn shrink<I>(
        &self,
        original: I,
        measure: impl Fn(&I) -> usize,
        mut candidates: impl FnMut(&I) -> Vec<I>,
        mut oracle: impl FnMut(&I) -> ShrinkVerdict,
    ) -> Option<ShrinkReport> {
        let signature = match oracle(&original) {
            ShrinkVerdict::NotAFailure => return None,
            ShrinkVerdict::Failure(signature) => signature,
        };
        let mut current = original;
        let mut lineage = vec![measure(&current)];
        let mut local_minimum = false;
        for _ in 0..self.max_rounds {
            let mut accepted = false;
            for candidate in candidates(&current) {
                if measure(&candidate) >= measure(&current) {
                    // Not a reduction. A candidate generator offering a non-shrinking
                    // step is skipped rather than trusted: the shrink's monotonicity
                    // is a law of the model, not of the generator.
                    continue;
                }
                match oracle(&candidate) {
                    ShrinkVerdict::NotAFailure => {}
                    ShrinkVerdict::Failure(candidate_signature) => {
                        if candidate_signature == signature {
                            lineage.push(measure(&candidate));
                            current = candidate;
                            accepted = true;
                            break;
                        }
                        // Signature drift: the candidate fails *differently*. That is
                        // a new finding, not a shrink — recorded by refusal here, and
                        // the drift never enters the lineage.
                    }
                }
            }
            if !accepted {
                local_minimum = true;
                break;
            }
        }
        let final_measure = measure(&current);
        Some(ShrinkReport {
            signature,
            original_measure: lineage[0],
            final_measure,
            lineage,
            local_minimum,
        })
    }
}
