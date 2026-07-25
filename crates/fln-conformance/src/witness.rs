//! **Witness** — the claim matrix and its documentation gate (bead
//! `franken_lean-claim-matrix-doc-ci-mhew`; plan §20.4, Bet B8).
//!
//! B8 promises that "every public claim is a row in a machine-checked claim matrix
//! (OBSERVED/TARGETED/HYPOTHESIS/PROVEN/BLOCKED)" and that "documentation CI rejects wording
//! stronger than the matrix permits". Until this module existed, that promise was itself an
//! unenforced claim. The full mechanism is `franken_lean-1gf` (the Witness epic) and its P0
//! child `franken_lean-n8hw`; this is the enforcing slice that exists today.
//!
//! ## A ratchet, not a linter
//!
//! A linter asks "does this sentence look overconfident?" and is unfalsifiable. This asks a
//! decidable question per site: **is this exact text present, and should it be?**
//!
//! * [`Enforcement::Enforced`] — the wording was corrected. Every site **must be absent**;
//!   a return is [`WitnessFault::Regressed`].
//! * [`Enforcement::Acknowledged`] — a measured overclaim still standing. Every site **must
//!   be present**. It does not fail the build, because a gate that cannot be green is a gate
//!   people learn to bypass — the `franken_lean-e5k7` lesson. But a site going *absent* is
//!   [`WitnessFault::StaleAcknowledgement`]: someone repaired it and the matrix did not
//!   follow.
//! * [`Enforcement::Supported`] — the claim is asserted **and the evidence backs it**. Every
//!   site must be present; its disappearance is [`WitnessFault::SupportedClaimVanished`].
//!   Without this mode a true claim has nowhere to live, and a compound sentence whose
//!   clauses differ (§8 below) gets flattened into one wrong verdict.
//!
//! The join runs in every direction on every row, so the boundary can only move one way:
//! silent progress fails as loudly as regression.
//!
//! ## One claim, many sites
//!
//! A [`ClaimRow`] carries a slice of [`ClaimSite`]s, because the same claim is asserted in
//! many places and a per-site row can drift. "Disagreement halts, never outvotes" is stated
//! **seven times in four phrasings across three documents**; a repair that fixes six of them
//! must not pass. Promotion moves every site together or fails.
//!
//! ## The census: repetition cannot hide
//!
//! Multi-site rows without [`CONCEPT_CENSUS`] would be a trap — each row would *look*
//! comprehensive without proving it enumerated every site. So for each governed concept the
//! census counts assertions of a keyword across the governed documents and requires exact
//! **conservation**:
//!
//! ```text
//! occurrences in documents == occurrences inside governed sites + declared ungoverned allowance
//! ```
//!
//! An equality, not an inequality. A new assertion added anywhere, or an existing one
//! deleted, moves the count and must be accounted for deliberately. This is the same
//! count-conservation discipline `fln_env::decl_closure` uses (`checked + artifact_incomplete
//! == decls_total`), applied to prose: it is what stops the matrix from reading as full
//! coverage while ten of eleven `dual-engine` assertions go unwatched.
//!
//! ## Scope — read this before treating a green run as "the documentation is verified"
//!
//! See [`GOVERNED_SCOPE`]. A passing scan means no row and no census is violated. It never
//! means the documentation is accurate.

use std::collections::BTreeSet;
use std::fmt;

/// D7's six claim types (plan §3, Rule D7). A weaker class may never enforce or justify a
/// stronger one; this enum exists so a row cannot leave the type implicit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClaimType {
    Invariant,
    Proof,
    BoundedModel,
    Statistical,
    Slo,
    Benchmark,
}

impl ClaimType {
    pub const fn as_str(self) -> &'static str {
        match self {
            ClaimType::Invariant => "invariant",
            ClaimType::Proof => "proof",
            ClaimType::BoundedModel => "bounded_model",
            ClaimType::Statistical => "statistical",
            ClaimType::Slo => "slo",
            ClaimType::Benchmark => "benchmark",
        }
    }
}

/// B8's evidence states. Deliberately distinct from [`ClaimType`]: the type says what kind of
/// statement it is, the state says how well established it is, and they are orthogonal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClaimState {
    Observed,
    Targeted,
    Hypothesis,
    Proven,
    Blocked,
}

impl ClaimState {
    pub const fn as_str(self) -> &'static str {
        match self {
            ClaimState::Observed => "OBSERVED",
            ClaimState::Targeted => "TARGETED",
            ClaimState::Hypothesis => "HYPOTHESIS",
            ClaimState::Proven => "PROVEN",
            ClaimState::Blocked => "BLOCKED",
        }
    }
}

/// Which direction a row is checked in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Enforcement {
    /// Corrected. Every site must be **absent**; a return fails the build.
    Enforced,
    /// A standing overclaim, recorded rather than failing. Every site must be **present**;
    /// disappearance means the row is stale and should be promoted to `Enforced`.
    Acknowledged,
    /// Asserted **and** supported by evidence. Every site must be **present**; its
    /// disappearance means a true claim was dropped, or the capability regressed and the
    /// state is now wrong.
    Supported,
}

/// One place a claim is asserted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClaimSite {
    /// Repo-relative path of the governed document.
    pub document: &'static str,
    /// The exact text that makes the claim. Verbatim, not paraphrased.
    pub text: &'static str,
}

/// One governed claim, wherever it is asserted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClaimRow {
    /// Stable id. Never reused, never renumbered — it is how a row is cited from a bead.
    pub id: &'static str,
    /// Every place this claim is made. Checked together, so a partial repair cannot pass.
    pub sites: &'static [ClaimSite],
    pub claim_type: ClaimType,
    /// The honest state of the claim, independent of what the wording implies.
    pub state: ClaimState,
    /// What the tree actually supports — the reviewable half of the row.
    pub evidence: &'static str,
    pub enforcement: Enforcement,
}

/// A conservation law over one concept's assertions.
///
/// `governed` is not stored: it is computed from the matrix, so it cannot drift from reality.
/// Only the deliberate `ungoverned_allowance` is declared.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConceptCensus {
    /// Human name of the concept, for the failure message.
    pub concept: &'static str,
    /// The substring whose occurrences count as an assertion of this concept.
    pub keyword: &'static str,
    /// Documents searched.
    pub documents: &'static [&'static str],
    /// Assertions deliberately left ungoverned, declared so the total is conserved.
    pub ungoverned_allowance: usize,
    /// Why those are not governed yet — a reviewable statement, not a silent remainder.
    pub allowance_reason: &'static str,
}

/// What this matrix does and does not govern. Data, not a doc comment, so it is printable at
/// failure time.
pub const GOVERNED_SCOPE: &str = "\
Fifteen rows over three documents (README.md, AGENTS.md, crates/fln-olean/src/lib.rs) plus \
three concept censuses over README.md, AGENTS.md and \
COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md, seeded from a measured read-only review \
(bead franken_lean-claim-matrix-doc-ci-mhew). NOT covered: the overwhelming majority of \
README.md (~41 KB) and the plan (~195 KB), every claim in every other crate header, and all \
generated contracts. Only three concepts have a conservation census; every other repeated \
claim in these documents is unwatched. A passing scan means no row and no census is violated. \
It does not mean the documentation is accurate.";

const fn site(document: &'static str, text: &'static str) -> ClaimSite {
    ClaimSite { document, text }
}

const README: &str = "README.md";
const AGENTS: &str = "AGENTS.md";
const PLAN: &str = "COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md";

// ---------------------------------------------------------------------------
// Site tables — separate consts because a ClaimRow borrows its sites.
// ---------------------------------------------------------------------------

const SITES_LOC_COVENANT: [ClaimSite; 1] = [site(AGENTS, "`fln-kernel` is ≤ 12 KLOC")];
const SITES_DUAL_ENGINE: [ClaimSite; 5] = [
    site(README, "dual-engine trusted checker"),
    site(README, "≤ 12 KLOC `forbid(unsafe)` dual-engine checker"),
    site(README, "dual-engine kernel that ships receipts"),
    site(
        AGENTS,
        "certified small-step + NbE accelerator, cross-checked",
    ),
    site(
        PLAN,
        "certified small-step + NbE accelerator, cross-checked",
    ),
];
const SITES_K2_LIVE: [ClaimSite; 1] = [site(README, "K2 is the NbE accelerator that makes")];
const SITES_CONSENSUS_HALTS: [ClaimSite; 5] = [
    site(README, "Disagreement halts; it never outvotes."),
    site(README, "disagreement halts, never outvotes"),
    site(AGENTS, "disagreement halts, never outvotes"),
    site(PLAN, "disagreement halts, never outvotes"),
    site(PLAN, "disagreement halts and never votes"),
];
const SITES_INDEPENDENT_CHECKER: [ClaimSite; 2] = [
    site(
        README,
        "plus an independent in-repo checker and foreign witnesses",
    ),
    site(
        AGENTS,
        "consensus receipts with an independent in-repo checker plus external witnesses",
    ),
];
const SITES_RECEIPTS: [ClaimSite; 1] = [site(
    README,
    "proof certificate; attested checks append to a transparency log",
)];
const SITES_DOCS_CI: [ClaimSite; 1] = [site(
    README,
    "documentation CI that rejects wording stronger than the evidence permits",
)];
const SITES_TOOLCHAIN_BINARIES: [ClaimSite; 1] = [site(
    AGENTS,
    "`lean`, `leanc`, `lake` drop-in binaries plus the `fln` multiplexer",
)];
const SITES_INSTALL_ONELINER: [ClaimSite; 1] = [site(
    README,
    "curl -fsSL https://raw.githubusercontent.com/Dicklesworthstone/franken_lean/main/scripts/install.sh | bash",
)];
const SITES_OLEAN_README: [ClaimSite; 1] = [site(README, "(read *and* byte-compatible write)")];
const SITES_OLEAN_HEADER: [ClaimSite; 1] = [site(
    "crates/fln-olean/src/lib.rs",
    "byte-compatible `.olean` read and write",
)];
const SITES_SUITE: [ClaimSite; 1] = [site(
    AGENTS,
    "FrankenLean is a prover written in the asupersync programming model",
)];
const SITES_WARM_ATTACH: [ClaimSite; 1] = [site(README, "warm attach ≤ 2 s")];
const SITES_THREAD_MATRIX: [ClaimSite; 1] =
    [site(README, "tested at {1, 8, 32} threads on every commit")];
const SITES_GOLEM: [ClaimSite; 1] = [site(README, "runs unmodified on Golem")];

/// **The claim matrix.**
///
/// B3 is decomposed rather than carried as one row: its sentence asserts seven sub-claims
/// whose honest states differ, and a single verdict over it would be wrong in both
/// directions. Two of those sub-claims are `Supported` — the ≤ 12 KLOC covenant is real and
/// CI-enforced, and the foreign-kernel witness genuinely runs — so the matrix does not imply
/// the whole B3 sentence is unsupported.
pub const CLAIM_MATRIX: [ClaimRow; 15] = [
    // ---- B3, decomposed -------------------------------------------------------------
    ClaimRow {
        id: "B3-KERNEL-LOC-COVENANT",
        sites: &SITES_LOC_COVENANT,
        claim_type: ClaimType::Invariant,
        state: ClaimState::Observed,
        evidence: "fln-kernel is 6,535 lines across 5 files, under the 12,000 bound declared \
                   as `covenant fln-kernel max-loc=12000` in ci/WORKSPACE_GRAPH.txt and \
                   enforced on every run by structure-guard FLN-STRUCT-015. This clause of B3 \
                   is earned; it is Supported so the matrix does not imply otherwise.",
        enforcement: Enforcement::Supported,
    },
    ClaimRow {
        id: "B3-DUAL-ENGINE",
        sites: &SITES_DUAL_ENGINE,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "There is ONE engine, the small-step checker in crates/fln-kernel/src/tc.rs, \
                   and ZERO normalization-by-evaluation code anywhere in the workspace. The \
                   `cross-check` sites in admit.rs are decoded-row-versus-regenerated-recursor \
                   checks — valuable, and not engine-versus-engine.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "B3-K2-ENGINE-NAMED-AS-LIVE",
        sites: &SITES_K2_LIVE,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "The Crucible subsystem entry names K2 as an existing engine in the present \
                   indicative. No such engine exists. This is a sharper form than the B3 \
                   summary rows: a subsystem description reads as an inventory of what is \
                   there.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "B3-CONSENSUS-HALTS",
        sites: &SITES_CONSENSUS_HALTS,
        claim_type: ClaimType::Invariant,
        state: ClaimState::Targeted,
        evidence: "There is no council to disagree. The word `consensus` occurs exactly once \
                   across fln-kernel and fln-checker combined, in the 6-line stub's charter. \
                   No vote, no halt path, and no canonical Judgment type — plan §8.3c \
                   specifies `Judgment { input_digest, env_logical_root, verdict, engine_id, \
                   fuel_profile }` as the substrate of consensus and no such type exists in \
                   any crate. Note the plan states a STRONGER variant, 'never votes', whose \
                   neighbouring clause about fln-checker non-sharing IS structurally proven \
                   today by the WORKSPACE_GRAPH prohibitions.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "B3-INDEPENDENT-CHECKER",
        sites: &SITES_INDEPENDENT_CHECKER,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "crates/fln-checker/src/lib.rs is a 6-line charter stub. Its INDEPENDENCE is \
                   already enforced — structure-guard walks the prohibitions fln-checker ->* \
                   fln-kernel, ->* fln-olean, ->* fln-rt, ->* fln-unsafe-* — so the layering \
                   for a second engine is real before the engine is. The foreign-witness half \
                   is a separate, Supported row.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "B3-RECEIPTS-BY-DEFAULT",
        sites: &SITES_RECEIPTS,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "crates/fln-kernel/src/verdict.rs:10 states receipts are a follow-up slice, \
                   and :273 repeats it at the admission site. There is no transparency log \
                   anywhere in the workspace.",
        enforcement: Enforcement::Acknowledged,
    },
    // ---- the rest of the seeded corpus ----------------------------------------------
    ClaimRow {
        id: "B8-DOCS-CI-ENFORCES-WORDING",
        sites: &SITES_DOCS_CI,
        claim_type: ClaimType::Invariant,
        state: ClaimState::Targeted,
        evidence: "This module is the enforcing slice and governs fifteen rows over three \
                   documents plus three censuses. The claim as written implies coverage of all \
                   documentation, which is not true and is why GOVERNED_SCOPE exists. Promote \
                   only when franken_lean-n8hw delivers the full matrix.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "PRODUCT-TOOLCHAIN-BINARIES",
        sites: &SITES_TOOLCHAIN_BINARIES,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "The workspace produces no product binary. Exactly two main.rs files exist, \
                   both dev apparatus (tools/structure-guard and its \
                   kernel-ownership-publisher); no crate manifest declares a [[bin]]; \
                   crates/fln-cli and crates/fln are 6-line charter stubs.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "INSTALL-ONELINER-RUNNABLE",
        sites: &SITES_INSTALL_ONELINER,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "REPAIRED by commit a368ea0b (bead \
                   franken_lean-readme-install-oneliner-wao6). scripts/install.sh does not \
                   exist and there are no release binaries to install. The command appeared \
                   TWICE — the hero block and the Installation section — so this row fails if \
                   either site returns.",
        enforcement: Enforcement::Enforced,
    },
    ClaimRow {
        id: "OLEAN-WRITE-README",
        sites: &SITES_OLEAN_README,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "fln-olean is read-only: decl.rs decode_expr is its only Expr-facing entry \
                   point and no encoder exists in the crate or anywhere in the workspace. \
                   Blocks FL-INV-04 codec fidelity and the mixed-producer codec rig. \
                   Capability record on bead franken_lean-oh1j.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "OLEAN-WRITE-CRATE-HEADER",
        sites: &SITES_OLEAN_HEADER,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "REPAIRED by commit 86035037 (bead fln-olean-doc-self-contradiction-myri). \
                   The header asserted read AND write on line 1 and deferred writing on line \
                   6, naming no bead. It now leads with the read-only reality and cites \
                   franken_lean-oh1j for the absent writer.",
        enforcement: Enforcement::Enforced,
    },
    ClaimRow {
        id: "SUITE-INTEGRATION",
        sites: &SITES_SUITE,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "Cargo.lock holds 33 packages with zero external source entries — every one \
                   is a workspace member. No FrankenSuite crate is wired in as a path or git \
                   dependency. The PROHIBITION half of D1 (no serde, no tokio, no LLVM) is \
                   OBSERVED and stronger than claimed: there are no external dependencies at \
                   all. Only the integration half is unsupported.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "DAEMON-WARM-ATTACH-SLO",
        sites: &SITES_WARM_ATTACH,
        claim_type: ClaimType::Slo,
        state: ClaimState::Hypothesis,
        evidence: "crates/fln-server is a 6-line charter stub; there is no daemon to attach \
                   to. AGENTS.md D7 item 10 already forbids this shape: no benchmark claim \
                   without corpus, machine, and claim state.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "DETERMINISM-THREAD-MATRIX",
        sites: &SITES_THREAD_MATRIX,
        claim_type: ClaimType::Invariant,
        state: ClaimState::Targeted,
        evidence: "The thread matrix genuinely runs (fln-syntax lexer_thread_matrix, \
                   env_snapshots.sh, kernel_replay.sh, verdict_schema.sh) — but the claim's \
                   SUBJECT does not exist: 'same environment' needs an elaborator \
                   (crates/fln-elab is a stub) and 'same artifacts' needs a writer. OBSERVED \
                   for the four tested subsystems, TARGETED as written.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "TACTICS-ON-GOLEM",
        sites: &SITES_GOLEM,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Hypothesis,
        evidence: "crates/fln-vm and crates/fln-elab are 6-line charter stubs. The Parity \
                   Ledger's 94 rows are term-plane observables (Lean.Name.hash, \
                   Lean.Level.normalize, Lean.Expr.data) against the pinned binary — the \
                   right shape of evidence, and not tactic execution.",
        enforcement: Enforcement::Acknowledged,
    },
];

const CENSUS_DOCS: [&str; 3] = [README, AGENTS, PLAN];

/// **Conservation laws over repeated claims.**
///
/// Each allowance is a declared remainder, not a silent one. If an assertion is added or
/// deleted anywhere in the searched documents, the equality breaks and somebody has to say
/// which it was.
pub const CONCEPT_CENSUS: [ConceptCensus; 3] = [
    ConceptCensus {
        concept: "the dual-engine kernel",
        keyword: "dual-engine",
        documents: &CENSUS_DOCS,
        ungoverned_allowance: 8,
        allowance_reason: "Eleven assertions exist (README 5, AGENTS 1, plan 5); three are \
                           governed by B3-DUAL-ENGINE. The remaining eight are two further \
                           README mentions and every plan mention — the plan is not yet in \
                           row scope at all, which is the largest single gap in this matrix.",
    },
    ConceptCensus {
        concept: "consensus halting",
        keyword: "isagreement halts",
        documents: &CENSUS_DOCS,
        ungoverned_allowance: 2,
        allowance_reason: "Seven assertions in four phrasings; five are governed by \
                           B3-CONSENSUS-HALTS. The two remaining are the Crucible subsystem \
                           entry in README and plan §8.3c, both of which restate the property \
                           in prose that needs its own anchors.",
    },
    ConceptCensus {
        concept: "the NbE accelerator",
        keyword: "NbE",
        documents: &CENSUS_DOCS,
        ungoverned_allowance: 2,
        allowance_reason: "Five assertions; three are governed (two by B3-DUAL-ENGINE, one by \
                           B3-K2-ENGINE-NAMED-AS-LIVE). The two remaining are plan-internal \
                           design prose describing the intended K2 engine.",
    },
];

/// A way the documentation and the matrix disagree.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum WitnessFault {
    /// An `Enforced` claim's wording came back.
    Regressed {
        id: String,
        document: String,
        occurrences: usize,
    },
    /// An `Acknowledged` claim's wording is gone — the repair happened and the row did not
    /// follow. Reported so progress cannot be silent.
    StaleAcknowledgement { id: String, document: String },
    /// A `Supported` claim's wording is gone: either a true claim was dropped, or the
    /// capability regressed and the row's state is now a lie.
    SupportedClaimVanished { id: String, document: String },
    /// A concept's assertions no longer balance against what the matrix governs.
    CensusDrift {
        concept: String,
        counted: usize,
        governed: usize,
        allowance: usize,
    },
    /// A governed document could not be read. **Never a pass**: the rows it carries were not
    /// established, so authority over them is inconclusive rather than clean (FL-INV-07).
    UnreadableDocument { document: String, detail: String },
    /// Two rows share an id, so one would shadow the other in any citation.
    DuplicateClaimId { id: String },
    /// A row with no sites decides nothing and would inflate the row count.
    EmptyClaimRow { id: String },
}

impl fmt::Display for WitnessFault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WitnessFault::Regressed {
                id,
                document,
                occurrences,
            } => write!(
                f,
                "{id}: wording this project already repaired is back in {document} \
                 ({occurrences} occurrence(s)).\n\
                 If the capability now genuinely exists, move the row's state and evidence \
                 first and only then restore the wording — in that order, so the claim is \
                 never ahead of the proof."
            ),
            WitnessFault::StaleAcknowledgement { id, document } => write!(
                f,
                "{id}: the acknowledged wording is no longer in {document}.\n\
                 Someone repaired it and the matrix did not follow. Promote the row to \
                 Enforcement::Enforced so the repair is protected, and update its evidence. \
                 This is a good failure — it is what stops the acknowledged set from quietly \
                 becoming fiction."
            ),
            WitnessFault::SupportedClaimVanished { id, document } => write!(
                f,
                "{id}: a SUPPORTED claim's wording is no longer in {document}.\n\
                 Either a true claim was dropped from the documentation, or the capability \
                 regressed and this row's state is now wrong. Decide which and say so in the \
                 row; do not delete the row to make this pass."
            ),
            WitnessFault::CensusDrift {
                concept,
                counted,
                governed,
                allowance,
            } => write!(
                f,
                "census for {concept} no longer balances: the documents assert it {counted} \
                 time(s), the matrix governs {governed}, and {allowance} are declared \
                 ungoverned ({governed} + {allowance} = {}).\n\
                 An assertion was added or removed. If added, either govern it with a site on \
                 the owning row or raise the allowance and say why. If removed, lower the \
                 allowance. Do not adjust the number without deciding which happened — the \
                 whole point of the equality is that a silent change is impossible.",
                governed + allowance
            ),
            WitnessFault::UnreadableDocument { document, detail } => write!(
                f,
                "{document} could not be read ({detail}), so the claims it carries were \
                 neither confirmed nor refuted. That is inconclusive, never a pass."
            ),
            WitnessFault::DuplicateClaimId { id } => write!(
                f,
                "two rows share the claim id {id}; one would shadow the other wherever a bead \
                 cites it."
            ),
            WitnessFault::EmptyClaimRow { id } => write!(
                f,
                "{id} has no sites, so it decides nothing while counting as coverage."
            ),
        }
    }
}

/// What a clean scan established.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WitnessReport {
    /// Rows whose repaired wording is confirmed absent.
    pub enforced: usize,
    /// Rows whose overclaim is confirmed still standing.
    pub acknowledged: usize,
    /// Rows whose supported claim is confirmed present.
    pub supported: usize,
    /// Individual (document, text) sites checked.
    pub sites: usize,
    /// Concept censuses that balanced.
    pub censuses: usize,
    /// Governed documents actually read.
    pub documents: BTreeSet<String>,
}

impl WitnessReport {
    pub fn rows(&self) -> usize {
        self.enforced + self.acknowledged + self.supported
    }
}

/// Scan a claim matrix and its censuses against documents supplied by `read`.
///
/// Takes the tables and a reader rather than touching the filesystem, so the planted cases in
/// the suite drive **this** function over synthetic documents. A mutation harness that
/// exercises a re-implementation of the thing it mutates can report a false green.
///
/// Faults come back sorted, so the report is a diffable artifact rather than a set that
/// reshuffles per run (FL-INV-01).
pub fn scan(
    rows: &[ClaimRow],
    censuses: &[ConceptCensus],
    mut read: impl FnMut(&str) -> Result<String, String>,
) -> Result<WitnessReport, Vec<WitnessFault>> {
    let mut faults: Vec<WitnessFault> = Vec::new();
    let mut report = WitnessReport::default();
    // Read each document once; a scan must not depend on how many rows cite it.
    let mut cache: Vec<(String, Result<String, String>)> = Vec::new();
    let mut load = |document: &str, cache: &mut Vec<(String, Result<String, String>)>| {
        if let Some(index) = cache.iter().position(|(name, _)| name == document) {
            return index;
        }
        cache.push((document.to_string(), read(document)));
        cache.len() - 1
    };

    for (index, row) in rows.iter().enumerate() {
        if rows[..index].iter().any(|prior| prior.id == row.id) {
            faults.push(WitnessFault::DuplicateClaimId {
                id: row.id.to_string(),
            });
        }
        if row.sites.is_empty() {
            faults.push(WitnessFault::EmptyClaimRow {
                id: row.id.to_string(),
            });
        }
    }

    for row in rows {
        let mut decided = true;
        for claim_site in row.sites {
            let index = load(claim_site.document, &mut cache);
            let text = match &cache[index].1 {
                Ok(text) => text,
                Err(detail) => {
                    faults.push(WitnessFault::UnreadableDocument {
                        document: claim_site.document.to_string(),
                        detail: detail.clone(),
                    });
                    decided = false;
                    continue;
                }
            };
            report.documents.insert(claim_site.document.to_string());
            report.sites += 1;
            let occurrences = text.matches(claim_site.text).count();
            match (row.enforcement, occurrences) {
                (Enforcement::Enforced, 0) => {}
                (Enforcement::Enforced, occurrences) => {
                    faults.push(WitnessFault::Regressed {
                        id: row.id.to_string(),
                        document: claim_site.document.to_string(),
                        occurrences,
                    });
                    decided = false;
                }
                (Enforcement::Acknowledged, 0) => {
                    faults.push(WitnessFault::StaleAcknowledgement {
                        id: row.id.to_string(),
                        document: claim_site.document.to_string(),
                    });
                    decided = false;
                }
                (Enforcement::Supported, 0) => {
                    faults.push(WitnessFault::SupportedClaimVanished {
                        id: row.id.to_string(),
                        document: claim_site.document.to_string(),
                    });
                    decided = false;
                }
                _ => {}
            }
        }
        if decided {
            match row.enforcement {
                Enforcement::Enforced => report.enforced += 1,
                Enforcement::Acknowledged => report.acknowledged += 1,
                Enforcement::Supported => report.supported += 1,
            }
        }
    }

    for census in censuses {
        let mut counted = 0usize;
        let mut readable = true;
        for document in census.documents {
            let index = load(document, &mut cache);
            match &cache[index].1 {
                Ok(text) => counted += text.matches(census.keyword).count(),
                Err(detail) => {
                    faults.push(WitnessFault::UnreadableDocument {
                        document: (*document).to_string(),
                        detail: detail.clone(),
                    });
                    readable = false;
                }
            }
        }
        if !readable {
            continue;
        }
        let governed = governed_occurrences(rows, census.keyword);
        if counted != governed + census.ungoverned_allowance {
            faults.push(WitnessFault::CensusDrift {
                concept: census.concept.to_string(),
                counted,
                governed,
                allowance: census.ungoverned_allowance,
            });
        } else {
            report.censuses += 1;
        }
    }

    if faults.is_empty() {
        Ok(report)
    } else {
        faults.sort();
        faults.dedup();
        Err(faults)
    }
}

/// How many occurrences of `keyword` the matrix's own site texts account for.
///
/// Computed from the rows rather than declared, so the governed half of the conservation law
/// cannot drift from the matrix it describes.
pub fn governed_occurrences(rows: &[ClaimRow], keyword: &str) -> usize {
    rows.iter()
        .flat_map(|row| row.sites.iter())
        .map(|site| site.text.matches(keyword).count())
        .sum()
}
