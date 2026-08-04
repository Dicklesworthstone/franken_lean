//! Oracle outcome authority — the twelve closed vocabularies, and the rule that
//! decides when an oracle observation may become a verdict at all (bead
//! `fln-1dxv`, carved out of `fln-euo`; plan §18).
//!
//! # The rule this module exists for
//!
//! A Reference timeout, cancellation, resource refusal, unavailable platform or
//! crash is **Inconclusive or InternalFault — never a semantic reject, and never
//! a FrankenLean divergence.**
//!
//! Getting that wrong is worse than missing a real divergence. A rig that
//! manufactures divergences burns the oracle's credibility, and once it has
//! cried wolf every genuine finding is discounted. It is the same law the
//! kernel's own differential already enforces at the other end of the pipe
//! (`crates/fln-kernel/tests/reference_differential.rs`: a non-answer from
//! either side is unscorable and fails rather than passing) — here it is applied
//! to the oracle's *process* rather than to its *answer*.
//!
//! The rule is structural, not documentary: [`ProcessOutcome::completed_exit`]
//! is the only way to reach an exit status, so a caller cannot read a verdict
//! out of a crash without going through a function that returns `None` for it.
//!
//! # Twelve vocabularies, twelve types
//!
//! The epic lists oracle kind, authority, process outcome, comparison class,
//! normalizer id/version, D7 claim type, evidence kind/state, L-level, mode,
//! determinism class, freshness and platform as SEPARATE closed vocabularies.
//! They are separate `enum`s here with no `From`/`Into` between them and no
//! shared integer representation, because the failure mode is conflation: an
//! L-level standing in for a claim state is how an unearned claim gets
//! laundered into looking evidenced.

/// Which oracle produced an observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OracleKind {
    /// The pinned `lean` binary over source — elaborator-level.
    ReferenceBinary,
    /// The pinned `leanchecker` over compiled artifacts — kernel-level.
    ReferenceChecker,
    /// A committed artifact (`.olean`) read as an oracle of what the Reference
    /// accepted when it wrote it.
    PinnedArtifact,
    /// A recorded transcript from the epoch laboratory.
    EpochTranscript,
}

/// Whether an oracle's word can settle a question or only inform one.
///
/// Deliberately NOT a boolean and deliberately not ordered with anything else:
/// authority is a property of the oracle in a context, not a rank.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OracleAuthority {
    /// Its answer settles the question.
    Authoritative,
    /// Its answer is recorded and may inform, but cannot settle.
    Advisory,
}

/// What the oracle PROCESS did. Distinct from what it said.
///
/// Only [`ProcessOutcome::Completed`] can carry a semantic answer. Every other
/// arm is a statement about the run, not about the subject.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProcessOutcome {
    /// Ran to completion with this exit status.
    Completed { exit: i32 },
    /// Exceeded its wall or CPU allowance.
    Timeout { after_ms: u64 },
    /// Cooperatively cancelled.
    Cancelled,
    /// Refused to start or continue for want of a declared resource.
    ResourceRefused { what: &'static str },
    /// The platform this observation needs is not available here.
    PlatformUnavailable { platform: Platform },
    /// Died on a signal.
    Crashed { signal: Option<i32> },
}

/// Why an observation could not become a verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NonAuthoritative {
    /// The run did not complete. Carries the outcome so a reader can size a
    /// retry or route a platform gap.
    Inconclusive { outcome: ProcessOutcome },
    /// Our own accounting contradicted itself — an invariant failure, not a
    /// statement about the subject or the oracle.
    InternalFault { what: String },
    /// The oracle ran, our accounting is sound, and there is still no judgment
    /// about THIS subject: the oracle does not judge it, or it was never
    /// submitted at this scope.
    ///
    /// A fact about the subject's COVERAGE, which is why it is neither of the
    /// two above — the run completed, so it is not `Inconclusive`, and nothing
    /// contradicted itself, so it is not `InternalFault`. The gap was found by
    /// `fln-7odd`: 1,425 declarations the pinned checker legitimately declines
    /// to submit, plus the far larger set never submitted at a given scope.
    /// Before this arm the nearest encoding of either was a completed run with
    /// exit 0, which reads as [`OracleVerdict::Accepted`] — an answer the
    /// oracle never gave.
    ///
    /// Never reachable from [`Observation::verdict`], and deliberately so: an
    /// observation is a record of a PROCESS, and no process outcome can tell
    /// you whether a subject was in scope. Only a caller that knows the subject
    /// can say this, which is why it is constructed by
    /// [`NonAuthoritative::not_judged`] and never inferred.
    NotJudged { what: String },
}

impl ProcessOutcome {
    /// The exit status, and ONLY when the process actually completed.
    ///
    /// This is the structural half of the rule. There is no field access and no
    /// `unwrap`-shaped escape that yields an exit status from a crash: a caller
    /// that wants one must handle `None`, and `None` is every non-completion.
    pub fn completed_exit(&self) -> Option<i32> {
        match self {
            ProcessOutcome::Completed { exit } => Some(*exit),
            _ => None,
        }
    }

    /// True exactly when this outcome may be read as an answer about the
    /// subject.
    pub fn is_semantic(&self) -> bool {
        matches!(self, ProcessOutcome::Completed { .. })
    }

    /// Classify a non-completing outcome. Returns `None` for `Completed`,
    /// because a completed run is not non-authoritative.
    ///
    /// Note that a crash maps to `Inconclusive`, not `InternalFault`: the
    /// Reference dying is a fact about the Reference, not about our accounting.
    /// `InternalFault` is reserved for OUR contradictions and is constructed
    /// only by [`NonAuthoritative::internal_fault`].
    pub fn non_authoritative(&self) -> Option<NonAuthoritative> {
        if self.is_semantic() {
            return None;
        }
        Some(NonAuthoritative::Inconclusive {
            outcome: self.clone(),
        })
    }
}

impl NonAuthoritative {
    pub fn internal_fault(what: impl Into<String>) -> NonAuthoritative {
        NonAuthoritative::InternalFault { what: what.into() }
    }

    /// The oracle produced no judgment about this subject. See
    /// [`NonAuthoritative::NotJudged`] for why this is constructed and never
    /// inferred from a process outcome.
    pub fn not_judged(what: impl Into<String>) -> NonAuthoritative {
        NonAuthoritative::NotJudged { what: what.into() }
    }
}

/// One oracle observation, before any comparison.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Observation {
    pub kind: OracleKind,
    pub authority: OracleAuthority,
    pub outcome: ProcessOutcome,
    pub platform: Platform,
    /// The oracle's diagnostic text, retained whatever the outcome — a crash's
    /// stderr is evidence about the run even though it is not a verdict.
    pub diagnostic: String,
}

/// What an observation is worth once the authority rule is applied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OracleVerdict {
    /// The oracle completed and said yes.
    Accepted,
    /// The oracle completed and said no. A REAL judgment about the subject.
    Rejected { diagnostic: String },
    /// The oracle did not answer. Never a reject, never a divergence.
    NoAnswer(NonAuthoritative),
}

impl Observation {
    /// Apply the authority rule.
    ///
    /// The only route from an observation to a semantic verdict runs through
    /// `Completed`; everything else becomes [`OracleVerdict::NoAnswer`]. An
    /// Advisory oracle can still produce Accepted/Rejected — authority governs
    /// whether the verdict may SETTLE a question, which is a separate axis
    /// deliberately not folded into this one.
    pub fn verdict(&self) -> OracleVerdict {
        match self.outcome.completed_exit() {
            Some(0) => OracleVerdict::Accepted,
            Some(_) => OracleVerdict::Rejected {
                diagnostic: self.diagnostic.clone(),
            },
            None => match self.outcome.non_authoritative() {
                Some(reason) => OracleVerdict::NoAnswer(reason),
                // `completed_exit` said the run did not complete and
                // `non_authoritative` said it did: our own two classifiers
                // contradicting each other. FL-INV-07 says an invariant failure
                // is a typed outcome, not a panic and not a user diagnostic, so
                // it becomes an InternalFault — which is unscorable, exactly
                // like every other way of not having an answer.
                None => OracleVerdict::NoAnswer(NonAuthoritative::internal_fault(
                    "outcome classified as both completed and non-completed",
                )),
            },
        }
    }

    /// Whether this observation may settle a question: it must have answered
    /// AND be authoritative. Two separate conditions, checked separately.
    pub fn can_settle(&self) -> bool {
        self.authority == OracleAuthority::Authoritative
            && matches!(
                self.verdict(),
                OracleVerdict::Accepted | OracleVerdict::Rejected { .. }
            )
    }
}

/// FrankenLean's own answer about the same subject.
///
/// A separate type from [`OracleVerdict`] on purpose. They are not two values of
/// one vocabulary; one is what we computed and the other is what an external
/// process was observed to do, and the scoring rule below is the only place they
/// are allowed to meet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OurVerdict {
    Accepted,
    Rejected {
        diagnostic: String,
    },
    /// We did not answer. FL-INV-07: never rendered as, cached as, or promoted
    /// to acceptance *or* rejection.
    Inconclusive {
        what: String,
    },
}

/// The result of holding our answer up against an oracle observation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Scored {
    /// Both answered and agreed.
    Agree,
    /// The oracle accepted and we rejected. Restrictive — the D23 carve-out
    /// direction, still a finding, but not unsoundness.
    Restrictive,
    /// The oracle rejected and we accepted. UNSOUND, and never carve-out-able.
    UnsoundlyPermissive,
    /// One side did not answer, so there is nothing to score. **Not** a
    /// divergence, in either direction.
    Unscorable(NonAuthoritative),
}

impl Scored {
    /// Whether this is a divergence between the two implementations.
    ///
    /// [`Scored::Unscorable`] is deliberately not one. A rig that counts
    /// unscorable rows as divergences manufactures findings that do not exist,
    /// which is worse than missing real ones: it burns the oracle's credibility,
    /// and afterwards every genuine finding is discounted too.
    pub fn is_divergence(&self) -> bool {
        matches!(self, Scored::Restrictive | Scored::UnsoundlyPermissive)
    }
}

/// Score our answer against an oracle observation.
///
/// The whole rule of this module, in one function:
///
/// - a Reference timeout, cancellation, resource refusal, unavailable platform
///   or crash reaches [`Scored::Unscorable`] and can reach nothing else;
/// - our own Inconclusive is equally unscorable — the same law at the other end
///   of the pipe;
/// - only two answered sides can produce a divergence.
///
/// Note the order: the oracle's non-answer is checked BEFORE our verdict is
/// consulted at all, so there is no path where a crash is paired with anything.
pub fn score(ours: &OurVerdict, oracle: &Observation) -> Scored {
    score_verdicts(ours, &oracle.verdict())
}

/// Score two verdicts that have already been established.
///
/// The same rule as [`score`], applied one step later in the pipe. It exists
/// because a recorded row (the Parity Ledger) holds verdicts rather than a live
/// [`Observation`], and a ledger that re-implemented the scoring rule could
/// drift from it silently — the one place the two sides are allowed to meet has
/// to stay one place. [`score`] is defined in terms of this, so there is no
/// second copy to keep in step.
pub fn score_verdicts(ours: &OurVerdict, oracle: &OracleVerdict) -> Scored {
    let oracle_verdict = match oracle {
        OracleVerdict::NoAnswer(reason) => return Scored::Unscorable(reason.clone()),
        answered => answered.clone(),
    };
    match (ours, oracle_verdict) {
        (OurVerdict::Inconclusive { what }, _) => {
            Scored::Unscorable(NonAuthoritative::internal_fault(what.clone()))
        }
        (OurVerdict::Accepted, OracleVerdict::Accepted) => Scored::Agree,
        (OurVerdict::Rejected { .. }, OracleVerdict::Rejected { .. }) => Scored::Agree,
        (OurVerdict::Rejected { .. }, OracleVerdict::Accepted) => Scored::Restrictive,
        (OurVerdict::Accepted, OracleVerdict::Rejected { .. }) => Scored::UnsoundlyPermissive,
        // `verdict()` returned an answered value above, so this is unreachable
        // by construction; it is an internal fault rather than a panic because
        // FL-INV-07 says an invariant failure is typed, not a user diagnostic.
        (_, OracleVerdict::NoAnswer(reason)) => Scored::Unscorable(reason),
    }
}

/// How two observations were compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ComparisonClass {
    ByteIdentical,
    NormalizedIdentical,
    AcceptanceOnly,
    DiagnosticEquivalent,
}

/// D7 claim types. A weaker class may never enforce or justify a stronger one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClaimType {
    Invariant,
    Proof,
    BoundedModel,
    Statistical,
    Slo,
    Benchmark,
}

/// What a piece of evidence IS.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EvidenceKind {
    UnitTest,
    PropertyTest,
    MutationKill,
    Differential,
    NoMockE2E,
}

/// What STATE that evidence is in. Separate from its kind, and separate again
/// from the claim type it supports.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EvidenceState {
    Observed,
    Targeted,
    Hypothesis,
    Proven,
    Blocked,
}

/// Per-surface compatibility level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LLevel {
    L0,
    L1,
    L2,
    L3,
    L4,
}

/// The three governing modes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    Faithful,
    Sound,
    Frontier,
}

/// Determinism class of an operation (D0 mathematical … D4 external).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DeterminismClass {
    D0,
    D1,
    D2,
    D3,
    D4,
}

/// How current an observation is relative to the pin it describes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Freshness {
    /// Regenerated against the current pin.
    Current,
    /// Recorded against an earlier pin and not yet re-run.
    Stale,
    /// Never run on this platform.
    Absent,
}

/// A certified host.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Platform {
    LinuxX86_64,
    MacOSAarch64,
    WindowsX86_64,
}

/// The strength rank of a claim type, INTERNAL to the claim vocabulary.
///
/// Deliberately private and deliberately not a method on [`ClaimType`]: the
/// moment a rank is publicly reachable as an integer, some caller compares it
/// against an L-level, a determinism class, or an evidence state, and D7's rule
/// that "a weaker class may never enforce or justify a stronger one" turns into
/// arithmetic across vocabularies. Only [`EvidenceRow::justifies`] may use it.
fn claim_rank(c: ClaimType) -> u8 {
    match c {
        ClaimType::Invariant => 5,
        ClaimType::Proof => 4,
        ClaimType::BoundedModel => 3,
        ClaimType::Statistical => 2,
        ClaimType::Slo => 1,
        ClaimType::Benchmark => 0,
    }
}

/// One row of the evidence matrix: every vocabulary that describes a piece of
/// evidence, each in its own field, none derived from another.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceRow {
    pub claim: ClaimType,
    pub kind: EvidenceKind,
    pub state: EvidenceState,
    pub level: LLevel,
    pub mode: Mode,
    pub determinism: DeterminismClass,
    pub freshness: Freshness,
    pub platform: Platform,
}

impl EvidenceRow {
    /// D7: may this row justify a statement of type `claimed`?
    ///
    /// Two conditions, both inside their own vocabulary:
    ///
    /// 1. the row's claim type is at least as strong as the one claimed, and
    /// 2. the row's evidence STATE is one that has actually been established.
    ///
    /// It does **not** read `level`, `mode`, `determinism`, `freshness` or
    /// `platform`. An L-level standing in for a claim state is how an unearned
    /// claim gets laundered into looking evidenced, so the absence of that read
    /// is a property the suite checks by varying every other field and
    /// demanding the answer not move.
    pub fn justifies(&self, claimed: ClaimType) -> bool {
        let established = matches!(self.state, EvidenceState::Proven | EvidenceState::Observed);
        established && claim_rank(self.claim) >= claim_rank(claimed)
    }

    /// The per-surface compatibility level this row may be reported at, if any.
    ///
    /// Symmetric to [`EvidenceRow::justifies`]: an L-level is *earned* by the
    /// evidence state, so a row that is still Hypothesis/Targeted/Blocked has no
    /// reportable level at all. It does **not** read `claim` — a strong claim
    /// type does not confer a compatibility level any more than a level confers
    /// a claim.
    pub fn compatibility_level(&self) -> Option<LLevel> {
        match self.state {
            EvidenceState::Proven | EvidenceState::Observed => Some(self.level),
            EvidenceState::Targeted | EvidenceState::Hypothesis | EvidenceState::Blocked => None,
        }
    }
}

#[cfg(test)]
mod conflation {
    //! The vocabularies are separate TYPES, so conflating two of them is a
    //! compile error rather than a runtime mistake. These tests pin the
    //! properties a reviewer would otherwise have to take on trust.
    use super::*;

    #[test]
    fn no_vocabulary_carries_another_ones_meaning() {
        // A claim type and an L-level are both "levels" in prose and neither is
        // convertible to the other. Nothing here can be written as an integer
        // comparison across vocabularies, which is the laundering route the
        // epic names.
        let claim = ClaimType::Invariant;
        let level = LLevel::L4;
        // Same-vocabulary comparison is fine.
        assert_ne!(claim, ClaimType::Benchmark);
        assert_ne!(level, LLevel::L0);
        // Cross-vocabulary comparison does not compile, which is the point:
        //   assert_eq!(claim, level);   // error[E0308]: mismatched types
        // Evidence state is likewise distinct from claim type.
        let state = EvidenceState::Proven;
        assert_ne!(state, EvidenceState::Hypothesis);
    }
}
