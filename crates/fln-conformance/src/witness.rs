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

/// A machine-checkable fact that a row's `evidence` prose asserts.
///
/// **Why this exists.** Slice 2 checked anchors and conservation and never checked the
/// *evidence*. Within hours of being written, two rows in this matrix were factually false
/// — `B3-INDEPENDENT-CHECKER` said `fln-checker` was "a 6-line charter stub" when it had
/// grown to 149 lines, and `B3-CONSENSUS-HALTS` said "there is no council to disagree"
/// after `crates/fln-kernel/src/council.rs` landed. The gate was green throughout.
///
/// That is this matrix's own defect one level up: a row that reads as verified while its
/// evidence describes a world that no longer exists. A claim matrix whose evidence rots
/// silently is exactly the thing it was built to prevent, so the load-bearing facts are now
/// cited and the citations are checked.
///
/// The direction matters. A citation should fail **when the fact changes**, which is when
/// the row needs a human — not when it stays true.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Citation {
    /// "still a stub": the file is at most this many lines. Fails once it is implemented,
    /// which is precisely when a row calling it a stub has become a lie.
    FileAtMostLines {
        path: &'static str,
        max_lines: usize,
    },
    /// "no longer a stub": the file is at least this many lines. Fails if it is reverted or
    /// emptied, which would make a row describing a real implementation wrong.
    FileAtLeastLines {
        path: &'static str,
        min_lines: usize,
    },
    /// A named construct occurs exactly this many times in the cited file.
    OccursExactly {
        path: &'static str,
        needle: &'static str,
        count: usize,
    },
}

impl Citation {
    pub const fn path(&self) -> &'static str {
        match self {
            Citation::FileAtMostLines { path, .. }
            | Citation::FileAtLeastLines { path, .. }
            | Citation::OccursExactly { path, .. } => path,
        }
    }

    /// `None` when the cited fact still holds; otherwise why it no longer does.
    fn check(&self, text: &str) -> Option<String> {
        match self {
            Citation::FileAtMostLines { path, max_lines } => {
                let lines = text.lines().count();
                (lines > *max_lines).then(|| {
                    format!(
                        "{path} is {lines} lines, over the cited maximum of {max_lines} — it is \
                         no longer the stub this row's evidence describes"
                    )
                })
            }
            Citation::FileAtLeastLines { path, min_lines } => {
                let lines = text.lines().count();
                (lines < *min_lines).then(|| {
                    format!(
                        "{path} is {lines} lines, under the cited minimum of {min_lines} — the \
                         implementation this row's evidence describes has shrunk or gone"
                    )
                })
            }
            Citation::OccursExactly {
                path,
                needle,
                count,
            } => {
                let found = text.matches(needle).count();
                (found != *count).then(|| {
                    format!(
                        "{path} contains `{needle}` {found} time(s), not the cited {count} — the \
                         construct this row's evidence relies on has moved"
                    )
                })
            }
        }
    }
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
Eighteen rows over five documents (README.md, AGENTS.md, \
COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md, crates/fln-olean/src/lib.rs, \
ci/PARITY_LEDGER.txt) plus \
three concept censuses over README.md, AGENTS.md and \
COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md, seeded from a measured read-only review \
(bead franken_lean-claim-matrix-doc-ci-mhew). The document list is a correction: it said THREE \
documents and omitted the plan while three row sites already pointed at it \
(franken_lean-4o3n, 2026-07-25) — a scope statement that understates itself is the same defect \
class as one that overstates. NOT covered: the overwhelming majority of \
README.md (~41 KB) and the plan (~195 KB), every claim in every other crate header, and all \
generated contracts. Only three concepts have a conservation census; every other repeated \
claim in these documents is unwatched. Every row now cites at least one checkable fact \
(nineteen citations over eighteen rows) — but that is a FLOOR, NOT COVERAGE: a citation catches \
only rot someone anticipated well enough to cite, and it protects one clause of a \
multi-clause evidence paragraph. B3-CONSENSUS-HALTS has nine factual clauses and one is \
cited, and it is not the clause its state depends on. Both rows that actually rotted on \
2026-07-25 rotted in ways nobody anticipated and were found by re-reading prose, not by any \
check; catching UNANTICIPATED rot needs a freshness predicate, which franken_lean-1gf \
specifies and this does not implement. A passing scan means no row, no census and no citation \
is violated. It does not mean the documentation is accurate, and it does not mean the \
evidence is current.";

const fn site(document: &'static str, text: &'static str) -> ClaimSite {
    ClaimSite { document, text }
}

const README: &str = "README.md";
const AGENTS: &str = "AGENTS.md";
const PLAN: &str = "COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md";
const LEDGER: &str = "ci/PARITY_LEDGER.txt";

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
/// The two places the SAME symbol is given two meanings. Unlike every other row here,
/// these sites are not where a claim is asserted — they are where the term the claim is
/// made in is DEFINED. That is the point: the disputed thing is the meaning, the 85
/// assertions that depend on it are counted by this row's citation instead, and neither
/// definition can be edited (including to resolve the split) without this row going red.
const SITES_L2_DEFINITION: [ClaimSite; 2] = [
    site(
        PLAN,
        "**L2 behavioral** (gated corpus passes; exclusions explicit)",
    ),
    site(
        LEDGER,
        "the pinned Reference binary produced the expected value",
    ),
];
const SITES_FUEL_PARITY: [ClaimSite; 5] = [
    site(README, "deterministic fuel parity"),
    site(AGENTS, "deterministic fuel parity"),
    site(
        AGENTS,
        "bug-for-bug observational parity with the pin, including fuel parity",
    ),
    site(PLAN, "deterministic fuel parity with the Reference"),
    site(
        PLAN,
        "the heartbeat-counting law is replicated at its allocation-linked granularity",
    ),
];
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
const SITES_BENCH_APPARATUS: [ClaimSite; 1] = [site(
    README,
    "Every gate has a bench binary, a committed baseline, a variance budget, and a flame \
     artifact on regression",
)];

/// **The claim matrix.**
///
/// B3 is decomposed rather than carried as one row: its sentence asserts sub-claims whose
/// honest states differ, and a single verdict over it would be wrong in both directions.
/// Seven of them have rows below. Exactly one is `Supported` — the ≤ 12 KLOC covenant is
/// real and CI-enforced — so the matrix does not imply the whole B3 sentence is unsupported.
///
/// Corrected 2026-07-25 (bead `franken_lean-4o3n`): this note said TWO sub-claims were
/// `Supported`, counting the foreign-kernel witness. That witness genuinely runs
/// (`scripts/tribunal/leanchecker_witness.sh`, wired into `scripts/check.sh`) — and it has no
/// row here, so it is UNGOVERNED, not supported. A true clause with no row is exactly what a
/// decomposition is supposed to make visible, and calling it supported hid it.
pub const CLAIM_MATRIX: [ClaimRow; 18] = [
    // ---- the term itself, before any row that uses it -------------------------------
    ClaimRow {
        id: "PARITY-LEDGER-L2-MEANS-TWO-THINGS",
        sites: &SITES_L2_DEFINITION,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "Added 2026-07-25 (bead \
                   franken_lean-parity-ledger-l2-definition-split-kl4h). L2 is defined twice, \
                   differently, and each document is internally consistent — which is why no \
                   single-document check can see it. The plan (§4.2) says L2 is `behavioral \
                   (gated corpus passes; exclusions explicit)'. ci/PARITY_LEDGER.txt's header \
                   says L2 is `the pinned Reference binary produced the expected value, and \
                   ... compares ours to it on every run', with L1 for source-read evidence. \
                   RE-MEASURED AT HEAD BY cc_2 ON 2026-07-27 AND CORRECTED. This sentence read \
                   `All 94 rows were earned against the SECOND'. It conflated the row count \
                   with the L2 population: the file holds 94 rows of which 85 are L2, and this \
                   row's OWN citation has asserted 85 since it was written — the prose and the \
                   tripwire beneath it disagreed from day one and nothing compares the two, \
                   which is this matrix's own defect arriving inside a row about that defect. \
                   Of those 85, seventy-nine were earned against the SECOND definition; under \
                   the first, ZERO are, because no row in the file was compared on a corpus \
                   pass of any kind — the ledger's whole fixture evidence is 687 lines, while \
                   the one corpus-scale rig (kernel_replay.rs, 157,183 declarations against \
                   the pin's own oleans) is cited by no row at all. SIX MEET NEITHER \
                   DEFINITION, named here because a declared population with no members is the \
                   empty-referent shape: BLAKE3.hash, BLAKE3.keyed_hash, BLAKE3.derive_key and \
                   BLAKE3.finalize_xof (oracle `spec-vectors'), plus \
                   Domain.vectors.multi-host-identity and LogicalRoot.multi-host-identity \
                   (oracle `multi-host-attestation'). All six sit on the `hash' surface, which \
                   is FrankenLean's own hashing rather than a Lean compatibility surface, so \
                   the pinned Reference — having no BLAKE3 — CANNOT have produced their values \
                   even in principle, and no gated corpus pass applies to them either. For \
                   those six the ladder has no rung at all, which is a CATEGORY ERROR IN THE \
                   LADDER rather than a collision between two definitions of one rung, and is \
                   a strictly larger claim than the bead states. DELIBERATELY NOT RESOLVED: \
                   inventing a third classification for rows whose author cannot be asked is \
                   choosing the answer. The population is declared and its members named; the \
                   axis is NOT built. The three figures above are re-derived from \
                   ci/PARITY_LEDGER.txt on every run and compared against this sentence in \
                   both directions by \
                   `the_l2_split_disclosure_matches_the_measured_ledger', so neither the file \
                   nor this prose can move without the other — the join that was missing when \
                   the description said 94 and the citation beneath it said 85. The canonical \
                   form it parses, which is why these are digits and not words: \
                   MEASURED-SPLIT l2=85 ledger-earned=79 neither=6 END-MEASURED-SPLIT. \
                   Readers resolve the first: README.md:42 and :94 advertise L0-L4 with \
                   no local gloss, and the plan gates releases on it (R4 requires `all \
                   mandatory rows L4'). THIS ROW DOES NOT DECIDE WHICH DEFINITION WINS — that \
                   is a doctrine call above this matrix, and the bead states the cost of each \
                   direction. What it does is make the split impossible to carry silently: \
                   both definitions are governed sites, so editing either one — including to \
                   resolve the split — fails this row until someone answers it. WHAT THE \
                   2026-07-27 CORRECTION DOES NOT CHANGE, stated because it is the load-bearing \
                   half: this edits the row's DESCRIPTION, never its enforcement. The state \
                   stays Acknowledged, so the row still CANNOT redden while the contradiction \
                   stands — deliberately, per the `franken_lean-e5k7' lesson that a gate which \
                   cannot go green is one people learn to bypass. Movement is watched and the \
                   standing contradiction is not, and making the description true does not make \
                   it reddenable. A contradiction that can never fail the build remains the \
                   actual defect here; nothing in this correction is a substitute for deciding \
                   it.",
        enforcement: Enforcement::Acknowledged,
    },
    // ---- B3, decomposed -------------------------------------------------------------
    ClaimRow {
        id: "B3-KERNEL-LOC-COVENANT",
        sites: &SITES_LOC_COVENANT,
        claim_type: ClaimType::Invariant,
        state: ClaimState::Observed,
        evidence: "The bound is real and enforced: `covenant fln-kernel max-loc=12000` in \
                   ci/WORKSPACE_GRAPH.txt, checked on every structure-guard run as \
                   FLN-STRUCT-015, with FLN-STRUCT-024 refusing a larger declared limit. This \
                   clause of B3 is earned; it is Supported so the matrix does not imply \
                   otherwise. The trusted closure is 6 files under crates/fln-kernel/src, and \
                   that cardinality is bound in both directions by \
                   `the_kernel_covenant_disclosure_matches_the_measured_closure` — a module \
                   entering or leaving the TCB is precisely the growth D6 requires be \
                   disclosed first, and it can no longer happen silently. CORRECTED at \
                   fbb9de1b: from its authoring commit e1623223 this row read `6,535 lines \
                   across 5 files', and that figure never came from the covenant's counter. \
                   6,535 is every line of those files; count_loc \
                   (tools/structure-guard/src/checks.rs) counts non-blank lines that do not \
                   begin with a comment marker, and said 5,416 that day. The matrix's only \
                   Supported row was therefore wrong by 1,119 lines on the day it was \
                   written — in the safe direction for a ceiling, and invisible either way, \
                   because nothing joined the disclosure to the counter that enforces the \
                   covenant. The live line count is deliberately NOT transcribed here: it \
                   moves on every kernel edit, so a figure in this row is either a nag or a \
                   rot, and re-deriving it would plant the second copy of count_loc's \
                   predicate that caused this. Measured once for the record at fbb9de1b with \
                   that predicate: 6,112 lines, 50.9% of the bound, 5,888 of headroom. \
                   Publishing the current value where it is measured, in the guard's own \
                   robot line, is bead franken_lean-kernel-loc-covenant-not-disclosed-t0g7, \
                   open.",
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
        evidence: "SUPERSEDED EVIDENCE, corrected 2026-07-25: this row previously said 'there \
                   is no council to disagree'. That became false when bead fln-uc44 landed \
                   crates/fln-kernel/src/council.rs (commit 10c9a2e3), and the matrix did not \
                   notice — which is why Citation exists. The seat is real and well made: \
                   `convene` CONSUMES the Admitted capability and on a halt simply never hands \
                   the non-Clone CheckedDecl back, so halting is not a flag anyone can ignore; \
                   and there is no quorum, no tally and no seat count anywhere in the module, \
                   so agreement is required rather than counted. What the sentence still \
                   promises beyond the tree: `convene` now has one bounded production caller, \
                   fln-elab's seed environment builder, where it admits the opaque Nat fixture \
                   before the first literal-definition test. That proves the capability route \
                   executes, but it is not an elaboration transaction, carries no independent \
                   witness seat, and never publishes the user declaration. The mechanism and \
                   one bring-up caller exist; the running consensus behaviour the wording \
                   describes does not. Also still absent: the canonical Judgment type plan \
                   §8.3c specifies as the substrate of consensus.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "B3-INDEPENDENT-CHECKER",
        sites: &SITES_INDEPENDENT_CHECKER,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "SUPERSEDED EVIDENCE, corrected 2026-07-25: this row said \
                   crates/fln-checker/src/lib.rs was 'a 6-line charter stub'. It is 149 lines \
                   — the independence-boundary work (franken_lean-r0xu) filled it in while the \
                   matrix went on asserting the stub, green. Its INDEPENDENCE has been enforced \
                   throughout: structure-guard walks fln-checker ->* fln-kernel, ->* fln-olean, \
                   ->* fln-rt, ->* fln-unsafe-*. What the claim still promises beyond the tree \
                   is a second CHECKING ENGINE: what exists is the independence boundary and \
                   the data schema, not an implementation that decides verdicts. The \
                   foreign-witness half genuinely runs \
                   (scripts/tribunal/leanchecker_witness.sh, called from scripts/check.sh) and \
                   has NO row in this matrix. Corrected 2026-07-25 (franken_lean-4o3n) from \
                   'a separate, Supported row', which named a row that has never existed: \
                   B3-KERNEL-LOC-COVENANT is the only Supported row here.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "B3-RECEIPTS-BY-DEFAULT",
        sites: &SITES_RECEIPTS,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "`crates/fln-kernel/src/verdict.rs`'s module header states receipts are a \
                   follow-up slice — \"Bootstrap slice: receipts and the full typestate \
                   envelope (§8.2b) are follow-up slices recorded on the bead\" — and the \
                   admitted variant repeats it as \"(Receipts: follow-up slice.)\". There is no \
                   transparency log anywhere in the workspace. QUOTED, NOT LINE-CITED, and \
                   re-derived at `a025c3cb`: this row said `verdict.rs:10` and `:273`, and both \
                   had drifted onto unrelated code — :10 onto a blank `//!` (the sentence moved \
                   to 11) and :273 onto `StackMeasurement`'s fields (the admission-site repeat \
                   moved to 974), each by an insertion above it. A line number is a claim with \
                   an expiry; a quoted construct is one a reader can still find.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "B3-FUEL-PARITY",
        sites: &SITES_FUEL_PARITY,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "Added 2026-07-25 (bead franken_lean-4o3n). The sentence asserts a RELATION \
                   between two fuel counters, and neither side of it is measured. In-repo there \
                   is one engine, so there is nothing to be at parity WITH (B3-DUAL-ENGINE). \
                   Against the pin the corpus differential's oracle axis is a CONSTANT: \
                   crates/fln-conformance/tests/kernel_replay.rs scores every corpus \
                   declaration against CorpusAxisVerdict::Accepted, inferred from the \
                   declaration being present in the pinned .olean — so no Reference fuel is \
                   ever observed in our process, and the faithful-mode wording ('the \
                   heartbeat-counting law is replicated ... so maxHeartbeats timeouts fire on \
                   the same inputs') has no measurement anywhere in the tree. What DOES exist: \
                   a typed fuel budget whose exhaustion is a typed Inconclusive (FL-INV-07), \
                   and ci/PARITY_LEDGER.txt rows 204/206 for the maxHeartbeats OPTION surface \
                   — the option exists and its default matches the pin, which says nothing \
                   about consumption and is the row most likely to be quoted as if it did. The \
                   kernel and Golem now classify their native work counters as \
                   ResourceReason::ExecutionSteps rather than borrowing the allocation-linked \
                   heartbeat name. That repairs the typed cause, not fuel parity: neither \
                   counter measures allocator ticks and no relationship to the pin has been \
                   established.",
        enforcement: Enforcement::Acknowledged,
    },
    // ---- the rest of the seeded corpus ----------------------------------------------
    ClaimRow {
        id: "B8-DOCS-CI-ENFORCES-WORDING",
        sites: &SITES_DOCS_CI,
        claim_type: ClaimType::Invariant,
        state: ClaimState::Targeted,
        evidence: "This module is the enforcing slice and governs seventeen rows over five \
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
        evidence: "The product workspace produces no toolchain binary. Its two main.rs files \
                   are dev apparatus (tools/structure-guard and its \
                   kernel-ownership-publisher); the third repository main.rs belongs to the \
                   Tribunal's separate nested epoch-lab workspace; no crate manifest declares \
                   a [[bin]]. crates/fln-cli and crates/fln now expose W1 diagnostic-projection \
                   library adapters, not executable product surfaces.",
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
        evidence: "crates/fln-server now owns W1's deterministic LSP diagnostic projection, \
                   but it still exposes no listener, session lifecycle, daemon entry point or \
                   product binary to attach to. No warm-attach benchmark records corpus, \
                   machine or claim state, as AGENTS.md D7 item 10 requires.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "DETERMINISM-THREAD-MATRIX",
        sites: &SITES_THREAD_MATRIX,
        claim_type: ClaimType::Invariant,
        state: ClaimState::Targeted,
        evidence: "The thread matrix genuinely runs (fln-syntax lexer_thread_matrix, \
                   env_snapshots.sh, kernel_replay.sh, verdict_schema.sh). fln-elab now has one \
                   bounded, single-threaded source-to-kernel seam for a natural-literal \
                   definition, but neither that seam nor an artifact writer participates in a \
                   schedule matrix. OBSERVED for the four tested subsystems and the seed's \
                   sequential result only; TARGETED as written for elaborated environments and \
                   artifacts.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "TACTICS-ON-GOLEM",
        sites: &SITES_GOLEM,
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Hypothesis,
        evidence: "A retained G0-3 prototype now provides a versioned whole-program FLBC \
                   validator in fln-comp and an ABI-valued interpreter in fln-vm. fln-elab now \
                   parses and kernel-checks one natural-literal definition, but that declaration \
                   is not lowered to FIR/FLBC and the seed exposes no term elaboration, tactic \
                   state, Meta API, or Native Mirror calls. The VM component tests still execute \
                   validated hand-built bytecode over real Marrow objects rather than compiled \
                   Lean tactics, so the user-visible claim remains a hypothesis.",
        enforcement: Enforcement::Acknowledged,
    },
    // ---- the empty-referent shape ---------------------------------------------------
    ClaimRow {
        id: "PERF-GATE-BENCH-APPARATUS",
        sites: &SITES_BENCH_APPARATUS,
        claim_type: ClaimType::Benchmark,
        state: ClaimState::Targeted,
        evidence: "REPAIRED 2026-07-26 (bead fln-bench-apparatus-empty-referent-bkw6). The \
                   sentence under the fifteen-gate table asserted that every gate HAS a bench \
                   binary, a committed baseline, a variance budget and a flame artifact. All \
                   four conjuncts were false for all fifteen gates. Re-measured at HEAD \
                   86b36e21: ZERO bench targets across the 33 workspace packages (from cargo \
                   metadata, so a benches/ directory cargo auto-discovers without a [[bench]] \
                   section could not hide in the count), zero benches/ directories, zero \
                   criterion dependencies, and zero committed baseline artifacts outside \
                   vendor/lean4-src, which is the Reference's own tree. The plan states the \
                   rule correctly at §19.2 as a constraint on benchmark BUNDLES; only this \
                   README restatement turned a rule about how to benchmark into an inventory \
                   of containers that exist. THE SHAPE, which is why the row is worth reading: \
                   every instance in AGENTS.md item 7 is a claim whose evidence EXISTS with \
                   the join to it unwatched. This one had no join to watch, because the far \
                   end was empty — so every technique item 7 recommends is structurally blind \
                   to it, and the repair had to bind the claim to the CARDINALITY of the thing \
                   it asserts instead. NOT a defect in crates/fln-bench: that crate is a \
                   4281-line evidence substrate whose own module doc opens by saying it does \
                   not run a product benchmark and owns no target threshold. It is correct and \
                   unused, which is the right order to build one in.",
        enforcement: Enforcement::Enforced,
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
                           README mentions and every plan mention — no plan occurrence of this \
                           keyword is governed by any row, which is the largest single gap in \
                           this matrix. Corrected 2026-07-25 (franken_lean-4o3n) from 'the plan \
                           is not yet in row scope at all': rows DO cite plan sites (dual-engine, \
                           consensus-halts, fuel-parity) in other phrasings, and only this \
                           keyword's plan occurrences are ungoverned.",
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

/// **The load-bearing facts each row's evidence asserts, made checkable.**
///
/// Kept as a side table joined by claim id rather than a field on [`ClaimRow`], so a citation
/// naming no row is itself a fault and the two tables cannot drift apart silently — the same
/// bidirectional discipline the corpus projection uses.
///
/// This is a seed, not coverage: the first six entries below are the seeded citations over
/// five rows, and the rest are the one-per-row ratchet. Most evidence prose here is still
/// unchecked, and [`GOVERNED_SCOPE`] says so.
/// Every row must carry at least one citation ([`every_row_cites_a_checkable_fact`] in the
/// suite). That is a **ratchet, not coverage**: it guarantees each row has *a* tripwire, which
/// is emphatically not the same as the row being current. A citation only catches rot someone
/// anticipated well enough to cite, and both rows that actually rotted on 2026-07-25 rotted in
/// ways nobody anticipated — they were found by re-reading prose, not by a check. The general
/// property needs a freshness predicate (`franken_lean-1gf` specifies one); this is the cheap
/// floor under it.
///
/// [`every_row_cites_a_checkable_fact`]: ../../tests/witness_claim_matrix.rs
pub const EVIDENCE_CITATIONS: [(&str, Citation); 19] = [
    // How many rows depend on the disputed definition. The sites pin the two definitions;
    // this pins the population, and it fires the moment ANY row's level moves — which is
    // exactly when "85 of 94, and zero under the plan's reading" stops being true.
    (
        "PARITY-LEDGER-L2-MEANS-TWO-THINGS",
        Citation::OccursExactly {
            path: "ci/PARITY_LEDGER.txt",
            needle: "| L2 |",
            count: 85,
        },
    ),
    // Corrected 2026-07-25 after this row asserted a stub that had grown to 149 lines.
    (
        "B3-INDEPENDENT-CHECKER",
        Citation::FileAtLeastLines {
            path: "crates/fln-checker/src/lib.rs",
            min_lines: 100,
        },
    ),
    // The seat this row's corrected evidence describes must still exist.
    (
        "B3-CONSENSUS-HALTS",
        Citation::OccursExactly {
            path: "crates/fln-kernel/src/council.rs",
            needle: "pub fn convene",
            count: 1,
        },
    ),
    (
        "DAEMON-WARM-ATTACH-SLO",
        Citation::FileAtLeastLines {
            path: "crates/fln-server/src/lib.rs",
            min_lines: 300,
        },
    ),
    (
        "TACTICS-ON-GOLEM",
        Citation::OccursExactly {
            path: "crates/fln-vm/src/interpreter.rs",
            needle: "pub fn execute(",
            count: 1,
        },
    ),
    (
        "TACTICS-ON-GOLEM",
        Citation::OccursExactly {
            path: "crates/fln-elab/src/lib.rs",
            needle: "pub fn check_nat_definition_source",
            count: 1,
        },
    ),
    (
        "PRODUCT-TOOLCHAIN-BINARIES",
        Citation::FileAtLeastLines {
            path: "crates/fln-cli/src/lib.rs",
            min_lines: 400,
        },
    ),
    // ---- the ratchet: one citation for every previously-uncited row ------------------
    (
        "B3-KERNEL-LOC-COVENANT",
        Citation::OccursExactly {
            path: "ci/WORKSPACE_GRAPH.txt",
            needle: "covenant fln-kernel max-loc=12000",
            count: 1,
        },
    ),
    // Count zero is a citation too, and the sharpest kind: it fires the moment the thing
    // this row says does not exist starts to.
    (
        "B3-DUAL-ENGINE",
        Citation::OccursExactly {
            path: "crates/fln-kernel/src/lib.rs",
            needle: "pub mod nbe",
            count: 0,
        },
    ),
    (
        "B3-K2-ENGINE-NAMED-AS-LIVE",
        Citation::OccursExactly {
            path: "crates/fln-kernel/src/lib.rs",
            needle: "pub mod nbe",
            count: 0,
        },
    ),
    // The load-bearing half of this row: the only heartbeat evidence that exists is the
    // OPTION surface — two rows, both `option` kind, asserting the option exists and its
    // default matches the pin. A third occurrence means somebody started recording
    // heartbeat CONSUMPTION, which is the moment "fuel parity" stops being ungoverned
    // prose and this row needs a human. Anchored in the generated ledger rather than in
    // fln-kernel, whose fuel labelling is under active revision on franken_lean-4o3n:
    // a tripwire in front of a change already in flight fires as noise, not as a finding.
    (
        "B3-FUEL-PARITY",
        Citation::OccursExactly {
            path: "ci/PARITY_LEDGER.txt",
            needle: "maxHeartbeats",
            count: 2,
        },
    ),
    (
        "B3-RECEIPTS-BY-DEFAULT",
        Citation::OccursExactly {
            path: "crates/fln-kernel/src/verdict.rs",
            needle: "receipts and the full typestate envelope",
            count: 1,
        },
    ),
    // This row's evidence says the matrix governs seventeen rows, so the citation tracks the
    // row count — but it must live in a DIFFERENT file than the needle describes. Citing
    // `witness.rs` for a literal inside `witness.rs` counts the citation itself: the first
    // attempt used `pub const CLAIM_MATRIX: [ClaimRow; 15]` and found it twice, once as the
    // declaration and once as its own needle. The mechanism caught that on its first run,
    // which is a small proof it discriminates. The suite's expectation moves whenever the
    // matrix does, so anchoring there tracks the same fact without self-reference.
    (
        "B8-DOCS-CI-ENFORCES-WORDING",
        Citation::OccursExactly {
            path: "crates/fln-conformance/tests/witness_claim_matrix.rs",
            needle: "report.acknowledged, 14",
            count: 1,
        },
    ),
    (
        "INSTALL-ONELINER-RUNNABLE",
        Citation::OccursExactly {
            path: "README.md",
            needle: "Install script — *not yet available*",
            count: 1,
        },
    ),
    (
        "OLEAN-WRITE-README",
        Citation::OccursExactly {
            path: "crates/fln-olean/src/lib.rs",
            needle: "Today this crate reads",
            count: 1,
        },
    ),
    (
        "OLEAN-WRITE-CRATE-HEADER",
        Citation::OccursExactly {
            path: "crates/fln-olean/src/decl.rs",
            needle: "pub fn decode_expr",
            count: 1,
        },
    ),
    // The strongest citation in the table: D1's prohibition is that the lock carries no
    // external package. One dependency edge and this fires.
    (
        "SUITE-INTEGRATION",
        Citation::OccursExactly {
            path: "Cargo.lock",
            needle: "source = ",
            count: 0,
        },
    ),
    (
        "DETERMINISM-THREAD-MATRIX",
        Citation::OccursExactly {
            path: "crates/fln-syntax/tests/lexer_thread_matrix.rs",
            needle: "const THREAD_COUNTS: [usize; 3] = [1, 8, 32];",
            count: 1,
        },
    ),
    // The repaired sentence must not merely stay repaired — the disclosure that replaced it
    // must stay PRESENT. The site above fires if the overclaim returns; this fires if the
    // replacement is quietly deleted, which would leave the fifteen gate numbers standing with
    // nothing next to them saying none has been measured. The tree-side half of the join — the
    // measured bench-target count actually matching the disclosed one — needs to enumerate the
    // workspace and so lives in the suite, not here.
    (
        "PERF-GATE-BENCH-APPARATUS",
        Citation::OccursExactly {
            path: "README.md",
            needle: "0 bench targets, 0 committed baselines and 0 flame artifacts",
            count: 1,
        },
    ),
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
    /// A fact a row's evidence asserts is no longer true. The row still passes its anchor
    /// checks, which is exactly why this is needed: the wording is stable and the world moved.
    StaleEvidence { id: String, detail: String },
    /// A citation naming a row that does not exist, so it checks nothing.
    CitationForUnknownRow { id: String },
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
            WitnessFault::StaleEvidence { id, detail } => write!(
                f,
                "{id}: this row's EVIDENCE is out of date — {detail}.\n\
                 The anchors still match, so nothing else would have caught this: the wording \
                 in the documents did not change, the tree did. Re-read what the row claims \
                 the tree supports, rewrite the evidence to what is true now, and move the \
                 state if the claim is now earned or newly unsupported. Do not adjust the \
                 citation to match reality and leave the prose alone — the citation exists to \
                 force the prose to be re-read."
            ),
            WitnessFault::CitationForUnknownRow { id } => write!(
                f,
                "a citation names claim row {id}, which does not exist; it checks nothing."
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
    /// Evidence citations whose cited fact still holds.
    pub citations: usize,
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
    citations: &[(&str, Citation)],
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

    for (id, citation) in citations {
        if !rows.iter().any(|row| row.id == *id) {
            faults.push(WitnessFault::CitationForUnknownRow {
                id: (*id).to_string(),
            });
            continue;
        }
        let index = load(citation.path(), &mut cache);
        match &cache[index].1 {
            Ok(text) => match citation.check(text) {
                Some(detail) => faults.push(WitnessFault::StaleEvidence {
                    id: (*id).to_string(),
                    detail,
                }),
                None => report.citations += 1,
            },
            Err(detail) => faults.push(WitnessFault::UnreadableDocument {
                document: citation.path().to_string(),
                detail: detail.clone(),
            }),
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
