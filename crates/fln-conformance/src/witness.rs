//! **Witness** — the claim matrix and its documentation gate (bead
//! `franken_lean-claim-matrix-doc-ci-mhew`; plan §20.4, Bet B8).
//!
//! B8 promises that "every public claim is a row in a machine-checked claim matrix
//! (OBSERVED/TARGETED/HYPOTHESIS/PROVEN/BLOCKED)" and that "documentation CI rejects wording
//! stronger than the matrix permits". Until this module existed, that promise was itself an
//! unenforced claim — which is the sharpest possible version of the problem it exists to
//! solve. The full mechanism is `franken_lean-1gf` (the Witness epic) and its P0 child
//! `franken_lean-n8hw`; this is the first enforcing slice, seeded from a measured review.
//!
//! ## A ratchet, not a linter
//!
//! A linter asks "does this sentence look overconfident?" and is unfalsifiable. This asks a
//! decidable question per row: **is this exact text present, and should it be?**
//!
//! * [`Enforcement::Enforced`] — the wording has been corrected. The text **must be absent**;
//!   its return is [`WitnessFault::Regressed`].
//! * [`Enforcement::Acknowledged`] — a measured overclaim still standing in the tree. The
//!   text **must be present**. It does not fail the build today, because a gate that cannot
//!   be green is a gate people learn to bypass — the `franken_lean-e5k7` lesson, where an
//!   obligation enforced only by an expensive lane silently reached 93 unmet rows. But if the
//!   text goes *absent* while the row still says `Acknowledged`, that is
//!   [`WitnessFault::StaleAcknowledgement`]: someone repaired the wording and the matrix did
//!   not notice.
//!
//! So the join runs in **both directions on every row**, and the boundary can only move one
//! way. Silent progress fails as loudly as regression, which is what stops an adoption
//! boundary from quietly becoming fiction.
//!
//! ## Why the anchor is exact text and not a pattern
//!
//! A regex over prose drifts into style policing and produces findings nobody can act on. An
//! exact anchor is a claim someone reviewed, and its presence or absence is a fact. It also
//! catches the failure that actually happened here: the install one-liner occurred **twice**
//! in `README.md`, and a fix that repaired one site would leave the other. An `Enforced` row
//! fails if its text appears *anywhere* in the document, so a partial repair cannot pass.
//!
//! ## Scope — read this before treating a green run as "the documentation is verified"
//!
//! See [`GOVERNED_SCOPE`]. Ten rows over three documents. `README.md` is ~41 KB and the plan
//! is ~195 KB; the overwhelming majority of their claims are **not** governed here. A passing
//! scan means "no row in this matrix is violated", never "the documentation is accurate".
//! Partial coverage that is honest about its edges beats total coverage that is asserted.

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
    /// Corrected. The anchor must be **absent**; its return fails the build.
    Enforced,
    /// A standing overclaim, recorded rather than failing. The anchor must be **present**;
    /// its disappearance means the row is stale and should be promoted to `Enforced`.
    Acknowledged,
}

/// One governed claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClaimRow {
    /// Stable id. Never reused, never renumbered — it is how a row is cited from a bead.
    pub id: &'static str,
    /// Repo-relative path of the document that asserts the claim.
    pub document: &'static str,
    /// The exact text that makes the claim. Verbatim, not paraphrased.
    pub anchor: &'static str,
    pub claim_type: ClaimType,
    /// The honest state of the claim, independent of what the wording implies.
    pub state: ClaimState,
    /// What the tree actually supports — the reviewable half of the row.
    pub evidence: &'static str,
    pub enforcement: Enforcement,
}

/// What this matrix does and does not govern. Stated as data so it can be printed by the
/// suite rather than living only in a doc comment nobody reads at failure time.
pub const GOVERNED_SCOPE: &str = "\
Ten rows over three documents (README.md, AGENTS.md, crates/fln-olean/src/lib.rs), seeded \
from a measured read-only review on 2026-07-25 (bead franken_lean-claim-matrix-doc-ci-mhew). \
NOT covered: the overwhelming majority of README.md (~41 KB) and \
COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md (~195 KB), every claim in every other \
crate header, and all generated contracts. A passing scan means no row here is violated. It \
does not mean the documentation is accurate.";

/// **The claim matrix.**
///
/// Seeded from the eight findings of the reality check on bead
/// `franken_lean-claim-matrix-doc-ci-mhew`. Two rows are `Enforced` because the wording was
/// repaired by commits `86035037` and `a368ea0b`; those are the regression corpus, and they
/// are real repairs rather than fixtures written to make a test pass.
pub const CLAIM_MATRIX: [ClaimRow; 10] = [
    ClaimRow {
        id: "B3-KERNEL-DUAL-ENGINE",
        document: "README.md",
        anchor: "dual-engine trusted checker",
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "fln-kernel is one engine (tc.rs); there is no NbE code anywhere in the \
                   workspace and crates/fln-checker/src/lib.rs is a 6-line charter stub, so \
                   there is no second engine and no consensus council. The <= 12 KLOC \
                   covenant and the lean4checker foreign witness ARE observed; they are \
                   separate claims and are not covered by this row.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "B8-DOCS-CI-ENFORCES-WORDING",
        document: "README.md",
        anchor: "documentation CI that rejects wording stronger than the evidence permits",
        claim_type: ClaimType::Invariant,
        state: ClaimState::Targeted,
        evidence: "This module is the first enforcing slice and governs ten rows over three \
                   documents. The claim as written implies coverage of all documentation, \
                   which is not true and is why GOVERNED_SCOPE exists. Promote this row only \
                   when franken_lean-n8hw delivers the full matrix.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "PRODUCT-TOOLCHAIN-BINARIES",
        document: "AGENTS.md",
        anchor: "`lean`, `leanc`, `lake` drop-in binaries plus the `fln` multiplexer",
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
        document: "README.md",
        anchor: "curl -fsSL https://raw.githubusercontent.com/Dicklesworthstone/franken_lean/main/scripts/install.sh | bash",
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "REPAIRED by commit a368ea0b (bead \
                   franken_lean-readme-install-oneliner-wao6). scripts/install.sh does not \
                   exist and there are no release binaries to install. The command appeared \
                   TWICE -- the hero block and the Installation section -- so this row fails \
                   if either site returns.",
        enforcement: Enforcement::Enforced,
    },
    ClaimRow {
        id: "OLEAN-WRITE-README",
        document: "README.md",
        anchor: "(read *and* byte-compatible write)",
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
        document: "crates/fln-olean/src/lib.rs",
        anchor: "byte-compatible `.olean` read and write",
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
        document: "AGENTS.md",
        anchor: "FrankenLean is a prover written in the asupersync programming model",
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Targeted,
        evidence: "Cargo.lock holds 33 packages with zero external source entries -- every one \
                   is a workspace member. No FrankenSuite crate is wired in as a path or git \
                   dependency. Note the PROHIBITION half of D1 (no serde, no tokio, no LLVM) \
                   is OBSERVED and stronger than claimed: there are no external dependencies \
                   at all. Only the integration half is unsupported.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "DAEMON-WARM-ATTACH-SLO",
        document: "README.md",
        anchor: "warm attach ≤ 2 s",
        claim_type: ClaimType::Slo,
        state: ClaimState::Hypothesis,
        evidence: "crates/fln-server is a 6-line charter stub; there is no daemon to attach \
                   to. AGENTS.md D7 item 10 already forbids this shape: no benchmark claim \
                   without corpus, machine, and claim state.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "DETERMINISM-THREAD-MATRIX",
        document: "README.md",
        anchor: "tested at {1, 8, 32} threads on every commit",
        claim_type: ClaimType::Invariant,
        state: ClaimState::Targeted,
        evidence: "The thread matrix genuinely runs (fln-syntax lexer_thread_matrix, \
                   env_snapshots.sh, kernel_replay.sh, verdict_schema.sh) -- but the claim's \
                   SUBJECT does not exist: 'same environment' needs an elaborator \
                   (crates/fln-elab is a stub) and 'same artifacts' needs a writer. OBSERVED \
                   for the four tested subsystems, TARGETED as written.",
        enforcement: Enforcement::Acknowledged,
    },
    ClaimRow {
        id: "TACTICS-ON-GOLEM",
        document: "README.md",
        anchor: "runs unmodified on Golem",
        claim_type: ClaimType::BoundedModel,
        state: ClaimState::Hypothesis,
        evidence: "crates/fln-vm and crates/fln-elab are 6-line charter stubs. The Parity \
                   Ledger's 94 rows are term-plane observables (Lean.Name.hash, \
                   Lean.Level.normalize, Lean.Expr.data) against the pinned binary -- the \
                   right shape of evidence, and not tactic execution.",
        enforcement: Enforcement::Acknowledged,
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
    /// A governed document could not be read. **Never a pass**: the rows it carries were not
    /// established, so authority over them is inconclusive rather than clean (FL-INV-07).
    UnreadableDocument { document: String, detail: String },
    /// Two rows share an id, so one would shadow the other in any citation.
    DuplicateClaimId { id: String },
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
                 The claim matrix records this text as an overclaim that was fixed. If the \
                 capability now genuinely exists, move the row's state and evidence first and \
                 only then restore the wording — in that order, so the claim is never ahead \
                 of the proof."
            ),
            WitnessFault::StaleAcknowledgement { id, document } => write!(
                f,
                "{id}: the acknowledged wording is no longer in {document}.\n\
                 Someone repaired it and the matrix did not follow. Promote the row to \
                 Enforcement::Enforced so the repair is protected, and update its evidence to \
                 say what is true now. This is a good failure — it is what stops the \
                 acknowledged set from quietly becoming fiction."
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
    /// Governed documents actually read.
    pub documents: BTreeSet<String>,
}

impl WitnessReport {
    pub fn rows(&self) -> usize {
        self.enforced + self.acknowledged
    }
}

/// Scan a claim matrix against documents supplied by `read`.
///
/// Takes the rows and a reader rather than touching the filesystem, so the planted cases in
/// the suite drive **this** function over synthetic documents. A mutation harness that
/// exercises a re-implementation of the thing it mutates can report a false green — the
/// lesson is already recorded in `fln-hash`'s registry suite and it applies unchanged.
///
/// Faults come back sorted, so the report is a diffable artifact rather than a set that
/// reshuffles per run (FL-INV-01).
pub fn scan(
    rows: &[ClaimRow],
    mut read: impl FnMut(&str) -> Result<String, String>,
) -> Result<WitnessReport, Vec<WitnessFault>> {
    let mut faults: Vec<WitnessFault> = Vec::new();
    let mut report = WitnessReport::default();

    for (index, row) in rows.iter().enumerate() {
        if rows[..index].iter().any(|prior| prior.id == row.id) {
            faults.push(WitnessFault::DuplicateClaimId {
                id: row.id.to_string(),
            });
        }
    }

    for row in rows {
        let text = match read(row.document) {
            Ok(text) => text,
            Err(detail) => {
                faults.push(WitnessFault::UnreadableDocument {
                    document: row.document.to_string(),
                    detail,
                });
                continue;
            }
        };
        report.documents.insert(row.document.to_string());
        let occurrences = text.matches(row.anchor).count();
        match row.enforcement {
            Enforcement::Enforced => {
                if occurrences > 0 {
                    faults.push(WitnessFault::Regressed {
                        id: row.id.to_string(),
                        document: row.document.to_string(),
                        occurrences,
                    });
                } else {
                    report.enforced += 1;
                }
            }
            Enforcement::Acknowledged => {
                if occurrences == 0 {
                    faults.push(WitnessFault::StaleAcknowledgement {
                        id: row.id.to_string(),
                        document: row.document.to_string(),
                    });
                } else {
                    report.acknowledged += 1;
                }
            }
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
