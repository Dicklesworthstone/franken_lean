//! `G0SpikeDecisionV1` — one row per G0 spike, and no way to talk past the gate
//! (bead `franken_lean-869w`, carved out of `fln-euo`; plan §22.1).
//!
//! # What this schema is for
//!
//! G0 exists so that no W2–W12 workstream freezes an interface on top of an
//! unpriced bet. **A gate whose decisions can be paraphrased, aggregated, or
//! quietly amended is not a gate.** Each of the ten §22.1 spikes emits exactly
//! one [`Decision`], and every way a decision could be softened is a typed
//! refusal rather than a judgement call.
//!
//! # Absence versus deferral — the boundary, and why it is drawn twice
//!
//! A spike may resolve to [`Resolution::Blocked`]: a schema that cannot say "we
//! have not answered this yet" forces the honest answer to be indistinguishable
//! from silence.
//!
//! But absence of a row is a hard [`Block::MissingDecision`], because tolerating
//! it would just move the silence up one level — a spike nobody ever thought
//! about would look exactly like one deliberately deferred. **Not answering is
//! a disposition you record, never one you achieve by staying quiet.** That is
//! the same law [`crate::corpus`] applies to the C1 inventory, stated twice
//! because it is the same failure twice.
//!
//! [`Resolution::Blocked`] is deliberately **not** a fourth [`Outcome`].
//! `Outcome` stays exactly Ratified / Amended / NoGo; folding Blocked into it
//! would conflate "a decision was reached" with "no decision was reached".
//!
//! # The two laundering rules
//!
//! **Amended is expensive or it is not an amendment.** [`Amendment`] requires
//! the exact §25 wording, a rationale, the blast radius, owners, dependency
//! updates, and *green* acceptance tests. Every field is checked non-empty and
//! the tests are checked actually green.
//!
//! **Non-evidence never becomes evidence.** [`WitnessRoot`] is typed Recorded /
//! Absent / Failed / Unresolved, and a Ratified or Amended outcome requires
//! every root to be `Recorded`. The refusal is on the root's *type*, not on
//! anybody's characterisation of it, so failed or absent evidence cannot be
//! narrated into an amendment.
//!
//! # No aggregate green
//!
//! [`verify`] computes over the **roster**, never over the rows that happen to
//! be present. There is no aggregate that can be green while a decision is
//! absent.

use crate::corpus::CorpusFamily;
use crate::oracle::{ClaimType, ComparisonClass, EvidenceState, Mode, OracleKind, Platform};
use std::collections::BTreeMap;

/// Schema line for a G0 decision ledger.
pub const G0_SCHEMA: &str = "fln-g0-spike-decision/1";

/// One roster entry: a spike id and the exact §22.1 question it must answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RosterSpike {
    pub id: String,
    /// The bolded spike name as §22.1 states it.
    pub name: String,
    /// The question, verbatim from §22.1.
    pub question: String,
}

// The transcribed `G0_ROSTER` constant that used to live here has been REMOVED
// (bead `fln-8fwh`). It was hand-copied from §22.1, and deriving the roster
// from the plan proved that **all ten** of its questions differed from the
// plan's — so the verbatim-question check below was enforcing a paraphrase with
// full confidence, which is precisely the failure this schema exists to
// prevent. A roster is now obtained from
// [`crate::derive::derive_g0_roster`], which reads the plan.

/// A witness root, with its status in the type rather than in a comment.
///
/// Closed: there is no `Other`, and no `Partial`. The three non-Recorded arms
/// are exactly the words the epic uses — failed, absent, unresolved — because
/// those are the three ways a missing result gets narrated into a present one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WitnessRoot {
    /// A real digest of a real artifact.
    Recorded(String),
    /// Never run.
    Absent,
    /// Ran and failed.
    Failed,
    /// Ran, and the outcome was never classified.
    Unresolved,
}

impl WitnessRoot {
    pub fn is_recorded(&self) -> bool {
        matches!(self, WitnessRoot::Recorded(_))
    }
    pub fn status(&self) -> &'static str {
        match self {
            WitnessRoot::Recorded(_) => "recorded",
            WitnessRoot::Absent => "absent",
            WitnessRoot::Failed => "failed",
            WitnessRoot::Unresolved => "unresolved",
        }
    }
}

/// The evidence a spike produced.
///
/// `evidence_state` is the WITNESS's state and is deliberately a separate field
/// from [`Decision::claim`], which is the D7 type of what the row asserts.
/// Neither is derived from the other — that separation is the same one the
/// Parity Ledger enforces, and it is here for the same reason.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Witness {
    pub evidence_state: EvidenceState,
    pub fixture_root: WitnessRoot,
    pub generated_contract_root: WitnessRoot,
    pub implementation_root: WitnessRoot,
    pub mutation_root: WitnessRoot,
    /// The REAL no-mock end-to-end root. A mock may support a unit test and may
    /// not close a gate.
    pub no_mock_e2e_root: WitnessRoot,
    pub oracle: OracleKind,
    pub comparison: ComparisonClass,
}

impl Witness {
    /// Every root paired with its field name, for reporting which one failed.
    pub fn roots(&self) -> [(&'static str, &WitnessRoot); 5] {
        [
            ("fixture", &self.fixture_root),
            ("generated_contract", &self.generated_contract_root),
            ("implementation", &self.implementation_root),
            ("mutation", &self.mutation_root),
            ("no_mock_e2e", &self.no_mock_e2e_root),
        ]
    }
}

/// The exact scope a decision is valid within. A decision outside its scope is
/// not a weaker decision; it is a different question.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scope {
    pub epoch: String,
    pub corpus: CorpusFamily,
    pub platform: Platform,
    pub mode: Mode,
}

/// A resource contract and what was actually used against it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Resources {
    pub contract_wall_ms: u64,
    pub contract_rss_bytes: u64,
    pub used_wall_ms: u64,
    pub used_rss_bytes: u64,
}

impl Resources {
    /// Whether usage stayed inside the contract it declared.
    ///
    /// A spike that blew its budget did not prove the thing could be done
    /// inside the budget, and the budget is usually the whole question.
    pub fn within_contract(&self) -> bool {
        self.used_wall_ms <= self.contract_wall_ms && self.used_rss_bytes <= self.contract_rss_bytes
    }
}

/// Everything an amendment must carry. All of it, or it is not an amendment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Amendment {
    /// The exact §25 wording the amendment installs. Not a summary of it.
    pub section_25_wording: String,
    pub rationale: String,
    /// Every downstream interface the amendment moves.
    pub blast_radius: Vec<String>,
    pub owners: Vec<String>,
    pub dependency_updates: Vec<String>,
    /// The amended acceptance tests, which must be green.
    pub acceptance_suite: String,
    pub acceptance_green: bool,
    pub acceptance_root: WitnessRoot,
}

/// Why a spike says no.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoGo {
    pub rationale: String,
    /// What must change instead. A NoGo with no consequence is a shrug.
    pub affected_interfaces: Vec<String>,
}

/// The three decisions a spike can reach. Exactly three — Blocked is not one of
/// them, because "no decision" is not a decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Ratified,
    Amended(Amendment),
    NoGo(NoGo),
}

impl Outcome {
    pub fn as_str(&self) -> &'static str {
        match self {
            Outcome::Ratified => "ratified",
            Outcome::Amended(_) => "amended",
            Outcome::NoGo(_) => "no-go",
        }
    }
}

/// Why a spike has not been decided. Closed; no `Other`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockedReason {
    /// Waiting on a prerequisite spike or workstream.
    AwaitingDependency,
    /// The apparatus to answer it does not exist yet.
    ApparatusMissing,
    /// Needs a platform this lab has not run on.
    PlatformUnavailable,
    /// Deliberately deferred with an owner.
    DeferredByOwner,
}

impl BlockedReason {
    pub fn as_str(self) -> &'static str {
        match self {
            BlockedReason::AwaitingDependency => "awaiting-dependency",
            BlockedReason::ApparatusMissing => "apparatus-missing",
            BlockedReason::PlatformUnavailable => "platform-unavailable",
            BlockedReason::DeferredByOwner => "deferred-by-owner",
        }
    }
}

/// Decided, or explicitly not yet. "Neither" is not representable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    Decided(Outcome),
    /// We have not answered this. Written down, with an owner, so that it is
    /// visible rather than silent.
    Blocked {
        reason: BlockedReason,
        owner: String,
        note: String,
    },
}

/// One G0 spike decision row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decision {
    pub spike: String,
    /// The exact §22.1 question. Checked against the roster verbatim: a row
    /// that paraphrases the question is answering a different one, which is
    /// precisely how a gate gets talked past.
    pub question: String,
    pub resolution: Resolution,
    /// D7 claim type of what this row asserts. Separate from
    /// `witness.evidence_state`, always.
    pub claim: ClaimType,
    pub witness: Witness,
    pub scope: Scope,
    pub resources: Resources,
    /// Known limitations. Required and non-empty; a row with none must say so.
    pub limitations: String,
    /// Downstream interfaces this decision affects.
    pub affected_interfaces: Vec<String>,
}

/// A way a G0 ledger fails. Every variant blocks; there is no warning level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Block {
    /// A roster spike with no row at all. The hard failure half of the boundary.
    MissingDecision { spike: String },
    /// More than one row for a spike. "Exactly one row" means exactly one.
    DuplicateDecision { spike: String },
    /// A row for a spike that is not on the §22.1 roster.
    UnknownSpike { spike: String },
    /// The row's question is not the roster's question, verbatim.
    QuestionMismatch { spike: String },
    /// A Ratified or Amended outcome resting on a root that is not Recorded.
    /// Failed, absent and unresolved evidence cannot become evidence.
    LaunderedNonEvidence {
        spike: String,
        root: &'static str,
        status: &'static str,
    },
    /// An amendment missing one of its mandatory parts.
    IncompleteAmendment {
        spike: String,
        missing: &'static str,
    },
    /// An amendment whose acceptance tests are not green.
    AmendmentNotGreen { spike: String },
    /// A NoGo with no rationale or no consequence.
    HollowNoGo {
        spike: String,
        missing: &'static str,
    },
    /// A Blocked row with no owner or no note.
    UnownedBlock {
        spike: String,
        missing: &'static str,
    },
    /// Usage exceeded the contract it declared.
    ResourceContractExceeded { spike: String },
    /// A row with no stated limitations.
    NoLimitationsStated { spike: String },
}

impl Block {
    pub fn reason(&self) -> &'static str {
        match self {
            Block::MissingDecision { .. } => "missing-decision",
            Block::DuplicateDecision { .. } => "duplicate-decision",
            Block::UnknownSpike { .. } => "unknown-spike",
            Block::QuestionMismatch { .. } => "question-mismatch",
            Block::LaunderedNonEvidence { .. } => "laundered-non-evidence",
            Block::IncompleteAmendment { .. } => "incomplete-amendment",
            Block::AmendmentNotGreen { .. } => "amendment-not-green",
            Block::HollowNoGo { .. } => "hollow-no-go",
            Block::UnownedBlock { .. } => "unowned-block",
            Block::ResourceContractExceeded { .. } => "resource-contract-exceeded",
            Block::NoLimitationsStated { .. } => "no-limitations-stated",
        }
    }
}

/// What a G0 ledger amounts to.
///
/// Three states, and `clears_g0` is the only one that lets a workstream freeze
/// an interface. Note there is no score, no percentage, and no "9 of 10" —
/// [`Gate::blocked`] and [`Gate::no_go`] name the spikes, because an aggregate
/// is exactly what this schema exists to refuse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Gate {
    pub roster_size: usize,
    pub ratified: Vec<String>,
    pub amended: Vec<String>,
    pub no_go: Vec<String>,
    pub blocked: Vec<String>,
    pub blocks: Vec<Block>,
}

impl Gate {
    /// Does this ledger clear G0?
    ///
    /// Every roster spike must be Decided, every decision must be well-formed,
    /// and no spike may be NoGo or Blocked. A NoGo is a real decision — the bet
    /// was priced and the answer was no — but it does not license the dependent
    /// workstream to freeze the interface it was going to freeze.
    pub fn clears(&self) -> bool {
        // Stated ONCE, positively. Every roster spike lands in exactly one of
        // the four buckets, so `ratified + amended == roster_size` already
        // means no spike is NoGo, Blocked or missing — adding
        // `no_go.is_empty() && blocked.is_empty()` would restate the same
        // predicate over the same data in the same function.
        //
        // That redundancy was here and a mutation campaign proved it dead:
        // deleting `blocked.is_empty()` changed no observable behaviour and the
        // mutant SURVIVED. It is the `poison::scan` lesson in a second
        // disguise — indistinguishable redundancy is not defence in depth, it
        // is dead code that no campaign can see. Unlike the scan's second
        // budget guard, which buys termination, these clauses bought nothing,
        // so the fix is deletion rather than differentiation.
        self.blocks.is_empty() && self.ratified.len() + self.amended.len() == self.roster_size
    }
}

fn check_amendment(spike: &str, a: &Amendment, blocks: &mut Vec<Block>) {
    for (missing, empty) in [
        ("section_25_wording", a.section_25_wording.trim().is_empty()),
        ("rationale", a.rationale.trim().is_empty()),
        ("blast_radius", a.blast_radius.is_empty()),
        ("owners", a.owners.is_empty()),
        ("dependency_updates", a.dependency_updates.is_empty()),
        ("acceptance_suite", a.acceptance_suite.trim().is_empty()),
        ("acceptance_root", !a.acceptance_root.is_recorded()),
    ] {
        if empty {
            blocks.push(Block::IncompleteAmendment {
                spike: spike.to_string(),
                missing,
            });
        }
    }
    if !a.acceptance_green {
        blocks.push(Block::AmendmentNotGreen {
            spike: spike.to_string(),
        });
    }
}

/// Verify a set of decisions against the roster.
///
/// Iterates the ROSTER, not the rows. That is what makes an absent decision
/// visible: a verifier that walked the rows would report nothing at all for a
/// spike nobody filed, and the aggregate would look green.
pub fn verify(decisions: &[Decision], roster: &[RosterSpike]) -> Gate {
    let mut blocks = Vec::new();
    let mut by_spike: BTreeMap<&str, Vec<&Decision>> = BTreeMap::new();
    for d in decisions {
        by_spike.entry(d.spike.as_str()).or_default().push(d);
    }

    // UNKNOWN. A row for a spike not on the roster is answering a question G0
    // did not ask.
    for spike in by_spike.keys() {
        if !roster.iter().any(|r| r.id == *spike) {
            blocks.push(Block::UnknownSpike {
                spike: (*spike).to_string(),
            });
        }
    }

    let mut ratified = Vec::new();
    let mut amended = Vec::new();
    let mut no_go = Vec::new();
    let mut blocked = Vec::new();

    for r in roster {
        let rows = by_spike
            .get(r.id.as_str())
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        // MISSING. The hard-failure half of the boundary: you must WRITE the
        // Blocked row, you cannot achieve deferral by staying quiet.
        if rows.is_empty() {
            blocks.push(Block::MissingDecision {
                spike: r.id.clone(),
            });
            continue;
        }
        if rows.len() > 1 {
            blocks.push(Block::DuplicateDecision {
                spike: r.id.clone(),
            });
        }
        let d = rows[0];

        // The exact question, verbatim. A paraphrase is a different question.
        if d.question != r.question {
            blocks.push(Block::QuestionMismatch {
                spike: r.id.clone(),
            });
        }

        if d.limitations.trim().is_empty() {
            blocks.push(Block::NoLimitationsStated {
                spike: r.id.clone(),
            });
        }
        if !d.resources.within_contract() {
            blocks.push(Block::ResourceContractExceeded {
                spike: r.id.clone(),
            });
        }

        match &d.resolution {
            Resolution::Decided(outcome) => {
                match outcome {
                    Outcome::Ratified => ratified.push(r.id.to_string()),
                    Outcome::Amended(a) => {
                        amended.push(r.id.to_string());
                        check_amendment(&r.id, a, &mut blocks);
                    }
                    Outcome::NoGo(n) => {
                        no_go.push(r.id.to_string());
                        if n.rationale.trim().is_empty() {
                            blocks.push(Block::HollowNoGo {
                                spike: r.id.clone(),
                                missing: "rationale",
                            });
                        }
                        if n.affected_interfaces.is_empty() {
                            blocks.push(Block::HollowNoGo {
                                spike: r.id.clone(),
                                missing: "affected_interfaces",
                            });
                        }
                    }
                }

                // THE LAUNDERING RULE. A positive decision rests on recorded
                // evidence or it does not rest on anything. The check is on the
                // root's TYPE, so no amount of narration converts a Failed root
                // into support for an amendment.
                if matches!(outcome, Outcome::Ratified | Outcome::Amended(_)) {
                    for (name, root) in d.witness.roots() {
                        if !root.is_recorded() {
                            blocks.push(Block::LaunderedNonEvidence {
                                spike: r.id.clone(),
                                root: name,
                                status: root.status(),
                            });
                        }
                    }
                }
            }
            Resolution::Blocked { owner, note, .. } => {
                blocked.push(r.id.to_string());
                if owner.trim().is_empty() {
                    blocks.push(Block::UnownedBlock {
                        spike: r.id.clone(),
                        missing: "owner",
                    });
                }
                if note.trim().is_empty() {
                    blocks.push(Block::UnownedBlock {
                        spike: r.id.clone(),
                        missing: "note",
                    });
                }
            }
        }
    }

    Gate {
        roster_size: roster.len(),
        ratified,
        amended,
        no_go,
        blocked,
        blocks,
    }
}

/// Line-oriented report. Names every spike in every non-clearing state.
///
/// Emits no score and no ratio. "9 of 10 ratified" is the aggregate this schema
/// exists to refuse: it reads as almost-done and hides which bet is unpriced.
pub fn report(g: &Gate) -> String {
    let mut out = String::new();
    for b in &g.blocks {
        out.push_str(&format!("g0: block reason={} {b:?}\n", b.reason()));
    }
    for s in &g.no_go {
        out.push_str(&format!("g0: no-go spike={s}\n"));
    }
    for s in &g.blocked {
        out.push_str(&format!("g0: blocked spike={s}\n"));
    }
    out.push_str(&format!(
        "g0: verdict={} roster={} ratified={} amended={} no_go={} blocked={} blocks={}\n",
        if g.clears() { "clear" } else { "not-clear" },
        g.roster_size,
        g.ratified.len(),
        g.amended.len(),
        g.no_go.len(),
        g.blocked.len(),
        g.blocks.len()
    ));
    out
}

// ---------------------------------------------------------------------------
// The ledger — real rows. One function per decided spike; the schema above is
// the law and this section is the record. The FIRST real row is G0-9's, and the
// evidence is injected rather than embedded so the verifying test computes every
// digest from the committed artifacts at run time — a row whose digests were
// pasted in would rot silently, which is the line-citation lesson applied to
// evidence roots.
// ---------------------------------------------------------------------------

/// The measured evidence behind the G0-9 row. Every digest is computed by the
/// caller from a real committed artifact; an empty string is demoted to
/// [`WitnessRoot::Absent`] rather than laundered into a `Recorded("")`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct G09Evidence {
    /// Content digest over the six committed fixture files (three `.lean`
    /// pilots and their three pinned-binary traces).
    pub fixture_root: String,
    /// Digest over the versioned replay schema id plus the pinned censuses —
    /// the contract this spike generated.
    pub generated_contract_root: String,
    /// The implementation's BEHAVIORAL identity: digest over what the rig
    /// computes (censuses, replay report, family roots), not over its source
    /// bytes — a refactor that preserves behavior keeps it, a behavior change
    /// moves it.
    pub implementation_root: String,
    /// Digest over the committed mutation-campaign receipt
    /// (`evidence/g09_trace_replay/mutation_campaign_<pin>.jsonl`).
    pub mutation_root: String,
    /// Digest over the committed no-mock regeneration receipt
    /// (`evidence/g09_trace_replay/regen_<pin>.jsonl`), produced by
    /// `scripts/tribunal/g09_trace_regen.sh` against the real pinned binary.
    pub no_mock_e2e_root: String,
    /// Digest over the acceptance run's own outputs.
    pub acceptance_root: String,
    /// Computed by the verifying test EXECUTING the acceptance checks, never
    /// asserted.
    pub acceptance_green: bool,
    pub used_wall_ms: u64,
    pub used_rss_bytes: u64,
}

fn recorded_or_absent(digest: &str) -> WitnessRoot {
    if digest.trim().is_empty() {
        WitnessRoot::Absent
    } else {
        WitnessRoot::Recorded(digest.to_string())
    }
}

/// The measured evidence behind the G0-4 row. The caller computes every root
/// from committed artifacts and executes the acceptance apparatus; this type
/// carries no pasted green defaults.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct G04Evidence {
    /// Digest over the closed C0-C2 manifest and the executable Reference
    /// fixture that supplies the observations.
    pub fixture_root: String,
    /// Behavioral identity of the generated grammar-epoch, trace, and budget
    /// contracts.
    pub generated_contract_root: String,
    /// Root of the canonical semantic comparison stream.
    pub implementation_root: String,
    /// Digest over the committed planted-cell campaign.
    pub mutation_root: String,
    /// Digest over the committed two-process pinned-Reference receipt.
    pub no_mock_e2e_root: String,
    /// Digest over the acceptance run's semantic and model outputs.
    pub acceptance_root: String,
    /// Computed by executing every named acceptance surface.
    pub acceptance_green: bool,
    /// Byte-identical production rows in the manifest-complete comparison.
    pub exact_rows: usize,
    /// Explicit, stable production-contract gaps.
    pub contract_gaps: usize,
    /// Any row neither exact nor one of the declared gaps.
    pub unclassified_rows: usize,
    pub used_wall_ms: u64,
    pub used_rss_bytes: u64,
}

/// The G0-4 decision row: **Amended**.
///
/// The complete C0-C2 manifest proves two things at once. First, the existing
/// production lexer, attachment builder, and Pratt parser are byte-identical
/// to the pinned Reference for the two accepted C0 rows, including Unicode byte
/// positions, nested trivia, terminal comments, and the final newline. Second,
/// a lexical success or a bounded hygiene/quotation model is not macro
/// expansion fidelity: the other eight rows remain named gaps spanning
/// diagnostic rendering, builtin application adaptation, dynamic productions,
/// recovery, macro expansion, `pp` separators, nested antiquotation, and macro
/// diagnostic source maps. Ratifying one undifferentiated syntax/hygiene
/// identity would therefore launder the model into a production claim.
///
/// The amendment separates syntax identity from expansion identity, preserves
/// the exact C0 result, and makes the eight gaps acceptance obligations for the
/// downstream macro transaction lane. Returns `None` when G0-4 is absent from
/// the roster.
pub fn g04_decision(roster: &[RosterSpike], evidence: &G04Evidence) -> Option<Decision> {
    let spike = roster.iter().find(|r| r.id == "G0-4")?;
    Some(Decision {
        spike: spike.id.clone(),
        question: spike.question.clone(),
        resolution: Resolution::Decided(Outcome::Amended(Amendment {
            section_25_wording: "AmendSyntaxOrExpansionIdentity: syntax identity and \
                expansion identity are separate compatibility axes. G0-4 ratifies \
                byte-exact C0 token, tree, SourceInfo, trivia, position, and \
                grammar-epoch apparatus at the pinned epoch. C1/C2 dynamic grammar, \
                macro expansion, hygiene, quotation/antiquotation/splice, generated \
                identity, recovery, and diagnostic source-map identity remain named \
                W4 acceptance gates. A bounded Name or quotation model, lexical \
                success, or an unclassified omission cannot satisfy expansion identity."
                .to_string(),
            rationale: "The manifest-complete real-Reference comparison has exactly \
                two byte-identical production C0 rows, eight explicit contract-gap \
                rows, and zero unclassified rows. It also exposed and repaired a real \
                terminal-trivia defect: the final newline belongs to the terminal \
                token's SourceInfo rather than an epilogue. The dynamic production \
                and macro-expansion paths do not yet exist, so \
                RatifyVellumSyntaxAndHygieneContracts would overstate the implementation."
                .to_string(),
            blast_radius: vec![
                "fln-syntax terminal-trivia attachment and SourceInfo identity".to_string(),
                "fln-parse dynamic grammar registration and recovery".to_string(),
                "franken_lean-4nv downstream macro transaction and expansion lane".to_string(),
                "W4 parser/macro interface freeze and faithful compatibility claims".to_string(),
            ],
            owners: vec![
                "FoggyForge".to_string(),
                "bead:franken_lean-4nv".to_string(),
            ],
            dependency_updates: vec![
                "franken_lean-4nv must close the eight committed G0-4 contract-gap \
                 codes before any C1/C2 expansion-identity claim"
                    .to_string(),
                "W4 must retain the G0-4 manifest, stock TraceContractV1 binding, \
                 resource/cancellation matrix, and pinned no-mock comparator as \
                 permanent acceptance inputs"
                    .to_string(),
            ],
            acceptance_suite: "syntax_fixture_manifest; pratt_precedence_model; \
                hygiene_scope_capture_model; quotation_splice_model; \
                grammar_epoch_transition_model; syntax_budget_matrix; \
                g0_4_no_mock_e2e"
                .to_string(),
            acceptance_green: evidence.acceptance_green
                && evidence.exact_rows == 2
                && evidence.contract_gaps == 8
                && evidence.unclassified_rows == 0,
            acceptance_root: recorded_or_absent(&evidence.acceptance_root),
        })),
        claim: ClaimType::BoundedModel,
        witness: Witness {
            evidence_state: EvidenceState::Observed,
            fixture_root: recorded_or_absent(&evidence.fixture_root),
            generated_contract_root: recorded_or_absent(&evidence.generated_contract_root),
            implementation_root: recorded_or_absent(&evidence.implementation_root),
            mutation_root: recorded_or_absent(&evidence.mutation_root),
            no_mock_e2e_root: recorded_or_absent(&evidence.no_mock_e2e_root),
            oracle: OracleKind::ReferenceBinary,
            comparison: ComparisonClass::ByteIdentical,
        },
        scope: Scope {
            epoch: "v4.32.0".to_string(),
            corpus: CorpusFamily::C2,
            platform: Platform::LinuxX86_64,
            mode: Mode::Faithful,
        },
        resources: Resources {
            contract_wall_ms: 600_000,
            contract_rss_bytes: 4 << 30,
            used_wall_ms: evidence.used_wall_ms,
            used_rss_bytes: evidence.used_rss_bytes,
        },
        limitations: "One Linux x86_64 host, one Reference pin (v4.32.0), one \
            mathlib pin, and ten manifest rows; claim class bounded_model. \
            ByteIdentical applies only to the two exact C0 production rows. The \
            other eight rows are explicit contract gaps, not failures, rejects, \
            matches, or sampled coverage. Hygiene and quotation results are \
            bounded models over the production Name representation, not a \
            production macro engine. RSS is sampled from Linux /proc while both \
            Reference children execute; it is an observed run fact, not an SLO."
            .to_string(),
        affected_interfaces: vec![
            "fln-syntax token attachment and SourceInfo".to_string(),
            "fln-parse grammar epochs and Pratt precedence".to_string(),
            "Vellum C1/C2 macro parsing and expansion".to_string(),
            "Tribunal syntax/hygiene parity rows".to_string(),
        ],
    })
}

/// The G0-9 decision row: **Amended**, not Ratified, because the spike's own
/// measurements moved the contract it was asked to ratify.
///
/// The spike question assumes the decision traces require PATCHING the
/// Reference. Increments 1–7 on bead `franken_lean-foo` priced that assumption
/// by measurement: six of seven TraceContractV1 event families flow from the
/// STOCK pinned binary (five verified firing by execution, `--json` envelopes
/// carrying deterministic source anchors), and the seventh — heartbeat — is
/// exactly derivable at declaration granularity from the stock binary alone
/// (`maxHeartbeats` bisection: a sharp deterministic flip, byte-identical edge
/// cells, the binary itself labelling the timeout deterministic). Per-EVENT
/// tick stamps are the one thing no stock surface offers at any price. So the
/// amendment rewrites the per-event exact-resource-facts clause to
/// per-declaration exact facts plus per-event ordinals, which zeroes the
/// Reference patch, makes noninterference trivial (the clean binary IS the
/// traced binary), and erases the per-epoch patch-maintenance burden. The
/// patched build stays available behind the D8 wall for the day a consumer
/// demonstrates a per-event-tick need that declaration granularity cannot
/// satisfy — and none does today.
///
/// Returns `None` when the roster has no G0-9, which the verifying test treats
/// as its own failure: a ledger row must never be emitted against a roster
/// that did not ask its question.
pub fn g09_decision(roster: &[RosterSpike], evidence: &G09Evidence) -> Option<Decision> {
    let spike = roster.iter().find(|r| r.id == "G0-9")?;
    Some(Decision {
        spike: spike.id.clone(),
        question: spike.question.clone(),
        resolution: Resolution::Decided(Outcome::Amended(Amendment {
            section_25_wording: "TraceContractV1 resource facts are bound at two \
                granularities: every event carries a deterministic stream ordinal and \
                causal depth; exact heartbeat and reduction/instance counter facts \
                are bound per DECLARATION, derived from the stock pinned Reference \
                (maxHeartbeats bisection to 1000-tick granularity; `diagnostics` \
                counter blocks), both measured byte-deterministic. Per-event tick \
                stamps are required only if a consumer demonstrates a need that \
                declaration granularity cannot satisfy, and then only via the \
                sandboxed build-time-only patched Reference behind the D8 wall."
                .to_string(),
            rationale: "Measured at the pin (bead franken_lean-foo, comments \
                1654-1660): zero of the 399 registered trace classes emit per-event \
                ticks, while declaration-granular heartbeat consumption is exactly \
                stock-derivable (sharp deterministic 25k/26k maxHeartbeats flip, \
                byte-identical edges) and diagnostics counters are byte-deterministic. \
                Amending the granularity zeroes the Reference patch, its epoch-bump \
                maintenance, and the noninterference prerequisite for stock families."
                .to_string(),
            blast_radius: vec![
                "TraceContractV1 (§18.3 golden decision traces)".to_string(),
                "fln-trace (consumes declaration-granular resource facts)".to_string(),
                "G0-4 macro-engine spike (consumes stock Elab.step traces)".to_string(),
            ],
            owners: vec!["CobaltLantern".to_string()],
            dependency_updates: vec![
                "§18.3 instrumented-oracle scope shrinks to heartbeat-conditional; \
                 the build recipe of acceptance (a) activates only on a demonstrated \
                 per-event-tick need"
                    .to_string(),
            ],
            acceptance_suite: "fln-conformance --lib trace_replay (12 tests: parse \
                totality, family checkers, planted omission/reordering/payload/outcome \
                divergences, thread matrix {1,8,32})"
                .to_string(),
            acceptance_green: evidence.acceptance_green,
            acceptance_root: recorded_or_absent(&evidence.acceptance_root),
        })),
        claim: ClaimType::BoundedModel,
        witness: Witness {
            evidence_state: EvidenceState::Observed,
            fixture_root: recorded_or_absent(&evidence.fixture_root),
            generated_contract_root: recorded_or_absent(&evidence.generated_contract_root),
            implementation_root: recorded_or_absent(&evidence.implementation_root),
            mutation_root: recorded_or_absent(&evidence.mutation_root),
            no_mock_e2e_root: recorded_or_absent(&evidence.no_mock_e2e_root),
            oracle: OracleKind::ReferenceBinary,
            comparison: ComparisonClass::ByteIdentical,
        },
        scope: Scope {
            epoch: "v4.32.0".to_string(),
            corpus: CorpusFamily::C1,
            platform: Platform::LinuxX86_64,
            mode: Mode::Faithful,
        },
        resources: Resources {
            contract_wall_ms: 600_000,
            contract_rss_bytes: 4 << 30,
            used_wall_ms: evidence.used_wall_ms,
            used_rss_bytes: evidence.used_rss_bytes,
        },
        limitations: "One host, one pin (v4.32.0), class bounded_model throughout. \
            constApprox is source-verified only (config-gated at ExprDefEq.lean:1266; \
            never toy-fired). Heartbeat derivation is exact to 1000-tick granularity \
            and costs O(log N) elaborations per declaration — a calibration tool, not \
            a Corpus-scale extraction. The text-form parser cannot distinguish a \
            wrapped term opening `[` from an event; the production parser must read \
            --json envelopes. Volume measured at pilot scale; Corpus projection is \
            quantile-based, not measured."
            .to_string(),
        affected_interfaces: vec![
            "TraceContractV1".to_string(),
            "fln-trace".to_string(),
            "tribunal golden-trace replay lanes (§18.3)".to_string(),
        ],
    })
}

/// The measured evidence behind the G0-6 row, injected exactly as
/// [`G09Evidence`] is: every digest computed by the verifying test from a real
/// committed artifact, empty demoted to Absent, the acceptance green executed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct G06Evidence {
    /// Content digests over the sixteen pinned corpus input files, folded — the
    /// pilot slice the thresholds were bisected on.
    pub fixture_root: String,
    /// The versioned fuel-model schema plus its source-cited constants.
    pub generated_contract_root: String,
    /// The model's behavioral identity: the replayed verdict table.
    pub implementation_root: String,
    /// Digest over `evidence/g06_fuel_parity/mutation_campaign_<pin>.jsonl`.
    pub mutation_root: String,
    /// Digest over `evidence/g06_fuel_parity/thresholds_<pin>.jsonl` — the
    /// receipt `scripts/tribunal/g06_fuel_probe.sh` writes against the REAL
    /// pinned binary with negative controls in both directions.
    pub no_mock_e2e_root: String,
    pub acceptance_green: bool,
    pub used_wall_ms: u64,
    pub used_rss_bytes: u64,
}

/// The G0-6 decision row: **Ratified** — the fuel law is calibrated and the
/// declared tolerance class is EXACT at the observable granularity.
///
/// The law, extracted from the pin's source and validated by measurement (bead
/// `franken_lean-7zr`, comments 1663–1666): one tick per small allocation
/// (`alloc.cpp:391`), user budgets in thousands (`CoreM.lean:176`), a
/// per-command delta (`:441`), a STRICT boundary (`:490` — exactly-at-budget
/// completes), zero disabling the limit. Verdict parity holds on every measured
/// cell — 56 of 56 across declaration and file granularity, every threshold
/// deterministic on re-bisection, context drift bounded below one user unit —
/// and rejects are budget-independent on the pilot slice, so a fuel mismatch
/// cannot mask a reject there. Depth accounting is three distinct regimes
/// (~2.015 frames per step on meta-level paths, ~zero on flattened binop
/// chains, exempt on compiled evaluation), which downstream allocator/kernel/VM
/// owners inherit as requirements. OQ-2 closes with tolerance class EXACT for
/// timeout/no-timeout verdicts at the pin's own 1000-tick user granularity;
/// sub-unit drift is unobservable through the pinned user surface and is a
/// stated limitation, not a divergence class.
pub fn g06_decision(roster: &[RosterSpike], evidence: &G06Evidence) -> Option<Decision> {
    let spike = roster.iter().find(|r| r.id == "G0-6")?;
    Some(Decision {
        spike: spike.id.clone(),
        question: spike.question.clone(),
        resolution: Resolution::Decided(Outcome::Ratified),
        claim: ClaimType::BoundedModel,
        witness: Witness {
            evidence_state: EvidenceState::Observed,
            fixture_root: recorded_or_absent(&evidence.fixture_root),
            generated_contract_root: recorded_or_absent(&evidence.generated_contract_root),
            implementation_root: recorded_or_absent(&evidence.implementation_root),
            mutation_root: recorded_or_absent(&evidence.mutation_root),
            no_mock_e2e_root: recorded_or_absent(&evidence.no_mock_e2e_root),
            oracle: OracleKind::ReferenceBinary,
            comparison: ComparisonClass::ByteIdentical,
        },
        scope: Scope {
            epoch: "v4.32.0".to_string(),
            corpus: CorpusFamily::C1,
            platform: Platform::LinuxX86_64,
            mode: Mode::Faithful,
        },
        resources: Resources {
            contract_wall_ms: 600_000,
            contract_rss_bytes: 4 << 30,
            used_wall_ms: evidence.used_wall_ms,
            used_rss_bytes: evidence.used_rss_bytes,
        },
        limitations: "One host, one pin (v4.32.0), class bounded_model. The tolerance \
            class is EXACT for VERDICTS at 1000-tick user granularity on the measured \
            slice; sub-unit tick drift is not excluded by measurement and cannot be \
            expressed through the pinned user surface. Context independence is bounded \
            below one user unit on the probed cells, not proven globally. The prototype \
            is a spike model replaying measured intervals, not the production \
            allocator; the production counting seam must keep the committed edge \
            fixtures green under scripts/tribunal/g06_fuel_probe.sh. Recursion-shape \
            coverage: application chains, binop chains, structural recursion under \
            reduce/eval/decide — match/mutual/well-founded shapes are future cells."
            .to_string(),
        affected_interfaces: vec![
            "fln-rt allocator counting seam (§6.3)".to_string(),
            "fln-kernel fuel accounting (§8.5)".to_string(),
            "faithful-mode timeout parity claims (§4.2, BN-08)".to_string(),
        ],
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct G01Evidence {
    /// Digest over the C3 and real-mathlib fixture manifests and their
    /// manifest-bound bytes.
    pub fixture_root: String,
    /// The canonical OLEAN inventory root every decoded field maps to.
    pub generated_contract_root: String,
    /// Behavioral identity of the contract-driven reader: the replayed walk
    /// table (per-fixture objects/imports/constants/extension census plus the
    /// full-stdlib sweep totals).
    pub implementation_root: String,
    /// Digest over the committed corruption-control evidence: the region-read
    /// hostile sweep and the receipt's flipped-byte kill.
    pub mutation_root: String,
    /// Digest over
    /// `crates/fln-conformance/evidence/g01_abi_resurrection/resurrection_<pin>.jsonl`
    /// — the receipt `scripts/tribunal/g01_resurrection_probe.sh` writes
    /// against the REAL pinned artifacts with negative controls in both
    /// directions.
    pub no_mock_e2e_root: String,
    pub acceptance_green: bool,
    pub used_wall_ms: u64,
    pub used_rss_bytes: u64,
}

/// The G0-1 decision row: **Ratified** — the extracted-contract layout method
/// resurrects real pinned artifacts end to end.
///
/// The spike asked for a real mathlib `.olean` parsed at the pin with every
/// constant and extension entry walked and object-graph integrity validated
/// against the extracted contract tables (bead `franken_lean-y24`). Measured:
/// the full pinned stdlib (2433 of 2433 modules, 9,562,406 objects, 158,608
/// constants, zero faults) and the manifest-complete real-mathlib set (six
/// modules spanning the order/algebra/analysis/tactic cones, 67,389 objects,
/// 1,352 constants, 5,377 extension entries — including simp-set payloads up
/// to 44 blocks / 1591 entries — zero faults), every decoded import row
/// byte-equal to the pinned oracle manifest, opaque extension payloads
/// preserved losslessly and flagged rather than guessed, and a flipped byte
/// in a copied fixture killed typed — never a panic, never an accept
/// (FL-INV-07). Every decoded field maps to a canonical ContractInventory
/// row: the OLEAN domain root of the W1 terminal join.
pub fn g01_decision(roster: &[RosterSpike], evidence: &G01Evidence) -> Option<Decision> {
    let spike = roster.iter().find(|r| r.id == "G0-1")?;
    Some(Decision {
        spike: spike.id.clone(),
        question: spike.question.clone(),
        resolution: Resolution::Decided(Outcome::Ratified),
        claim: ClaimType::BoundedModel,
        witness: Witness {
            evidence_state: EvidenceState::Observed,
            fixture_root: recorded_or_absent(&evidence.fixture_root),
            generated_contract_root: recorded_or_absent(&evidence.generated_contract_root),
            implementation_root: recorded_or_absent(&evidence.implementation_root),
            mutation_root: recorded_or_absent(&evidence.mutation_root),
            no_mock_e2e_root: recorded_or_absent(&evidence.no_mock_e2e_root),
            oracle: OracleKind::PinnedArtifact,
            comparison: ComparisonClass::ByteIdentical,
        },
        scope: Scope {
            epoch: "v4.32.0".to_string(),
            corpus: CorpusFamily::C2,
            platform: Platform::LinuxX86_64,
            mode: Mode::Faithful,
        },
        resources: Resources {
            contract_wall_ms: 600_000,
            contract_rss_bytes: 4 << 30,
            used_wall_ms: evidence.used_wall_ms,
            used_rss_bytes: evidence.used_rss_bytes,
        },
        limitations: "One host, one pin (v4.32.0), one corpus commit (81a5d257), class \
            bounded_model. The real-mathlib set is six of 8639 published modules, chosen \
            by the recorded selection rationale and manifest-bound byte-for-byte; a \
            whole-corpus walk is an on-demand sweep, not a fixture obligation. The v3 \
            closure-payload traversal carries the 2026-07-22 typed limitation recorded \
            on the bead and does not affect any measured row here. Corruption coverage \
            is a deterministic 300-flip sweep plus the receipt's flipped-byte kill, not \
            a fuzz campaign. The reader is the spike prototype: production codec \
            conformance is W2's (fln-20n, fln-lld), and this row claims nothing about \
            olean WRITE, which is G0-5's question."
            .to_string(),
        affected_interfaces: vec![
            "fln-olean region reader and OleanView walk budget (§7.2)".to_string(),
            "fln-rt object model contract tables (§6)".to_string(),
            "fln-20n olean codec read acceptance inputs (W2)".to_string(),
            "tribunal C2/C3 fixture families (§18.6)".to_string(),
        ],
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct G02Evidence {
    /// Digest over the C3 fixtures, the real-mathlib fixture set, and the
    /// judgment-inventory coverage publication.
    pub fixture_root: String,
    /// Digest over `KERNEL_CONTRACT.md` — the rule-anchored inventory the
    /// replays are scored against.
    pub generated_contract_root: String,
    /// Behavioral identity of the replay: the census (accepted/rejected
    /// families/inconclusive/artifact-incomplete) across the three legs plus
    /// the witness agreements.
    pub implementation_root: String,
    /// Digest over the hostile-input evidence: the region corruption sweep
    /// and the witness's anti-rubber-stamp control.
    pub mutation_root: String,
    /// Digest over
    /// `crates/fln-conformance/evidence/g02_kernel_verdict/chosen_set_<pin>.jsonl`
    /// and the leanchecker witness lane, the no-mock differential legs.
    pub no_mock_e2e_root: String,
    pub acceptance_green: bool,
    pub used_wall_ms: u64,
    pub used_rss_bytes: u64,
}

/// The G0-2 decision row: **Ratified** — the kernel's judgment inventory met
/// reality and agreed with a foreign witness on real modules.
///
/// The spike asked for a prototype Crucible checking a nontrivial upstream
/// module from its olean — statements AND proofs — with verdicts diffed
/// against lean4checker (bead `franken_lean-z6c`). Measured at the pin:
/// Init.Prelude 2198/2198 accepted (0 rejected, 6 typed artifact-incomplete
/// per FL-INV-07), the Std leg Std.Data.HashMap.Basic 92/92 over a
/// 165-module closure, and the defeq-heavy mathlib leg Mathlib.Order.Basic
/// 376/376 over a 1286-module closure — 2,666 accepted declarations with
/// zero rejected, and the pinned leanchecker independently accepting every
/// chosen module as ReferenceKernelOracle (the review amendment's authority
/// class: it embeds the Reference C++ kernel, never a foreign-independent
/// one). Every rejection along the way was triaged to a named reduction-gap
/// family and converted by named follow-ups (fln-5p2, fln-d4x, fln-irm):
/// the triage is machine-checked in `kernel_replay.rs`, total, and currently
/// empty. The row-per-Appendix-A inventory is published with two explicit
/// blockers visible (KR-318 native hooks unexercised; the quarantine rules
/// oracle-unscorable by design). Soundness runs one way only: the Reference
/// accepted every replayed declaration when it wrote them, so any K1
/// rejection is a false-reject by construction — never a false-accept.
pub fn g02_decision(roster: &[RosterSpike], evidence: &G02Evidence) -> Option<Decision> {
    let spike = roster.iter().find(|r| r.id == "G0-2")?;
    Some(Decision {
        spike: spike.id.clone(),
        question: spike.question.clone(),
        resolution: Resolution::Decided(Outcome::Ratified),
        claim: ClaimType::BoundedModel,
        witness: Witness {
            evidence_state: EvidenceState::Observed,
            fixture_root: recorded_or_absent(&evidence.fixture_root),
            generated_contract_root: recorded_or_absent(&evidence.generated_contract_root),
            implementation_root: recorded_or_absent(&evidence.implementation_root),
            mutation_root: recorded_or_absent(&evidence.mutation_root),
            no_mock_e2e_root: recorded_or_absent(&evidence.no_mock_e2e_root),
            oracle: OracleKind::ReferenceChecker,
            comparison: ComparisonClass::ByteIdentical,
        },
        scope: Scope {
            epoch: "v4.32.0".to_string(),
            corpus: CorpusFamily::C2,
            platform: Platform::LinuxX86_64,
            mode: Mode::Faithful,
        },
        resources: Resources {
            contract_wall_ms: 1_200_000,
            contract_rss_bytes: 6 << 30,
            used_wall_ms: evidence.used_wall_ms,
            used_rss_bytes: evidence.used_rss_bytes,
        },
        limitations: "One host, one pin (v4.32.0), one corpus commit (81a5d257), class \
            bounded_model. The chosen set is three real modules plus their closures, not \
            the corpus: acceptance (a) says 'chosen module set' and is satisfied at that \
            bound; a whole-corpus differential is the standing rig's business (§8.7), \
            seeded here as `chosen_set_replays_and_witnesses`. The two published blockers \
            are load-bearing: KR-318 native reduction hooks are unexercised, and \
            partial/unsafe quarantine rows are oracle-unscorable by design — nothing in \
            this row reads past either. K2 is out of scope by the spike's own text: this \
            row says the rules are correctly understood, nothing about speed. The 6 typed \
            artifact-incomplete declarations on the Init.Prelude leg are FL-INV-07 \
            outcomes — counted, never accepted, never rejected."
            .to_string(),
        affected_interfaces: vec![
            "fln-kernel K1 judgment paths (§8, Appendix A)".to_string(),
            "fln-conformance standing kernel differential rig (§8.7)".to_string(),
            "fln-env declaration-closure admission (FL-INV-07 counting)".to_string(),
            "G1 Independent Judge gate inputs (§22.2 W3)".to_string(),
        ],
    })
}

/// The measured evidence behind the G0-5 row, injected exactly as its four
/// siblings are: every digest computed by the verifying test from committed
/// artifacts, the acceptance EXECUTED.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct G05Evidence {
    /// Content digests of the committed pilot pair (source + pinned-binary
    /// emission), folded.
    pub fixture_root: String,
    /// The generated olean contract digest plus the versioned freedom table.
    pub generated_contract_root: String,
    /// The rebuilder's behavioral identity: the executed accounting report.
    pub implementation_root: String,
    /// Digest over `crates/fln-olean/evidence/g05_rebuild_mutation_<pin>.jsonl`.
    pub mutation_root: String,
    /// Digest over `crates/fln-olean/evidence/g05_reemit_probe_<pin>.jsonl` —
    /// the real-binary determinism/provenance/async cells with their negative
    /// control, written by `scripts/tribunal/g05_reemit_probe.sh`.
    pub no_mock_e2e_root: String,
    pub acceptance_green: bool,
    pub used_wall_ms: u64,
    pub used_rss_bytes: u64,
}

/// The G0-5 decision row: **Ratified** — FL-INV-04's byte law stands as stated
/// for the read->rebuild direction, and the serialization-freedom enumeration
/// is measured-exhaustive.
///
/// The spike's evidence (bead `franken_lean-0vf`, comments 1707-1713): six
/// emission-determinism cells against the real pinned binary, all in the good
/// direction (fresh-emission, cross-directory and async-elaboration byte
/// identity; import emission deterministic and mtime-independent); ONE real
/// serialization freedom found and policy-pinned per direction (`base_addr`,
/// per-emission mmap placement rebasing every absolute pointer — reproduced
/// from the file's own header on rebuild, R3 fallback shape reserved for fresh
/// emission only); the rebuilder re-deriving every understood byte class from
/// parsed semantics with pilot byte-identity under exact accounting pins AND
/// the ENTIRE 2,433-file shipped corpus byte-identical with zero findings; a
/// 9/9 killed-by-name mutation campaign whose padding plant found a live
/// FL-INV-07 panic before the campaign ran. The fresh-emission direction is
/// the stated residue: it awaits Athanor, and its R3 choice is written in the
/// freedom table rather than deferred silently.
pub fn g05_decision(roster: &[RosterSpike], evidence: &G05Evidence) -> Option<Decision> {
    let spike = roster.iter().find(|r| r.id == "G0-5")?;
    Some(Decision {
        spike: spike.id.clone(),
        question: spike.question.clone(),
        resolution: Resolution::Decided(Outcome::Ratified),
        claim: ClaimType::BoundedModel,
        witness: Witness {
            evidence_state: EvidenceState::Observed,
            fixture_root: recorded_or_absent(&evidence.fixture_root),
            generated_contract_root: recorded_or_absent(&evidence.generated_contract_root),
            implementation_root: recorded_or_absent(&evidence.implementation_root),
            mutation_root: recorded_or_absent(&evidence.mutation_root),
            no_mock_e2e_root: recorded_or_absent(&evidence.no_mock_e2e_root),
            oracle: OracleKind::ReferenceBinary,
            comparison: ComparisonClass::ByteIdentical,
        },
        scope: Scope {
            epoch: "v4.32.0".to_string(),
            corpus: CorpusFamily::C1,
            platform: Platform::LinuxX86_64,
            mode: Mode::Faithful,
        },
        resources: Resources {
            contract_wall_ms: 600_000,
            contract_rss_bytes: 4 << 30,
            used_wall_ms: evidence.used_wall_ms,
            used_rss_bytes: evidence.used_rss_bytes,
        },
        limitations: "One host, one pin (v4.32.0), class bounded_model. The byte law is \
            ratified for READ->REBUILD: pilot plus all 2,433 shipped stdlib oleans, \
            re-derivation not copying, zero findings. FRESH EMISSION is not exercised: \
            it awaits Athanor, and its base_addr choice is the R3 fallback shape \
            written in the freedom table (fln_olean::rebuild::SERIALIZATION_FREEDOMS), \
            reserved for that direction only. Emission-determinism cells are \
            pilot-scale (six cells); corpus-scale emission determinism is untested \
            because re-elaborating the stdlib is a build-system act, not a spike act. \
            The corpus sweep is env-gated on the installed pin and typed-skips \
            elsewhere."
            .to_string(),
        affected_interfaces: vec![
            "FL-INV-04 (codec fidelity: stands as stated for read->rebuild)".to_string(),
            "fln-olean writer (Grimoire, seeded by fln_olean::rebuild)".to_string(),
            "the standing codec rig (plan section 18.2, PG-8)".to_string(),
        ],
    })
}

#[cfg(test)]
mod structural {
    use super::*;

    #[test]
    fn blocked_is_not_an_outcome() {
        // The vocabulary check that keeps "no decision" out of the decision
        // vocabulary. Outcome has exactly three constructors; a fourth called
        // Blocked would let a Blocked row be counted among the decided.
        let tokens = [
            Outcome::Ratified.as_str(),
            Outcome::Amended(Amendment {
                section_25_wording: String::new(),
                rationale: String::new(),
                blast_radius: vec![],
                owners: vec![],
                dependency_updates: vec![],
                acceptance_suite: String::new(),
                acceptance_green: false,
                acceptance_root: WitnessRoot::Absent,
            })
            .as_str(),
            Outcome::NoGo(NoGo {
                rationale: String::new(),
                affected_interfaces: vec![],
            })
            .as_str(),
        ];
        assert_eq!(tokens.len(), 3);
        for t in tokens {
            assert!(t != "blocked", "Blocked leaked into the Outcome vocabulary");
        }
    }

    #[test]
    fn every_block_variant_has_its_own_reason_token() {
        let all = [
            Block::MissingDecision {
                spike: String::new(),
            },
            Block::DuplicateDecision {
                spike: String::new(),
            },
            Block::UnknownSpike {
                spike: String::new(),
            },
            Block::QuestionMismatch {
                spike: String::new(),
            },
            Block::LaunderedNonEvidence {
                spike: String::new(),
                root: "fixture",
                status: "absent",
            },
            Block::IncompleteAmendment {
                spike: String::new(),
                missing: "owners",
            },
            Block::AmendmentNotGreen {
                spike: String::new(),
            },
            Block::HollowNoGo {
                spike: String::new(),
                missing: "rationale",
            },
            Block::UnownedBlock {
                spike: String::new(),
                missing: "owner",
            },
            Block::ResourceContractExceeded {
                spike: String::new(),
            },
            Block::NoLimitationsStated {
                spike: String::new(),
            },
        ];
        let mut t: Vec<&str> = all.iter().map(Block::reason).collect();
        let before = t.len();
        t.sort_unstable();
        t.dedup();
        assert_eq!(before, t.len(), "two Block variants share a reason token");
    }

    #[test]
    fn the_report_names_spikes_and_emits_no_score() {
        let g = Gate {
            roster_size: 10,
            ratified: (1..=9).map(|i| format!("G0-{i}")).collect(),
            amended: vec![],
            no_go: vec![],
            blocked: vec!["G0-10".to_string()],
            blocks: vec![],
        };
        let text = report(&g);
        assert!(!text.contains('%'));
        for w in ["score", "9/10", "9 of 10", "percent"] {
            assert!(!text.contains(w), "the report emitted {w:?}");
        }
        // The blocked spike is NAMED, because "9 ratified" reads as almost-done
        // and hides which bet is still unpriced.
        assert!(text.contains("blocked spike=G0-10"));
        assert!(text.contains("verdict=not-clear"));
    }
}
