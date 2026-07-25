//! Kernel-bound publication of a Verdict-reflected theorem.
//!
//! The solver and proof checker are deliberately untrusted. This module therefore
//! exposes one whole-pipeline operation rather than a public "checked" token:
//!
//! 1. replay the exact canonical CNF and proof streams with the independent checker;
//! 2. let Crucible borrow the one owned theorem declaration;
//! 3. after `Accepted`, move that same declaration payload into Grimoire's bounded
//!    plan and commit.
//!
//! There is no clone, reconstruction, replacement parameter, or equality-based
//! handoff between steps 2 and 3. Rust ownership is the check-A/publish-A witness.
//! The wider rule that *all* environment admission requires an opaque kernel
//! capability remains the kernel-owned `fln-yswb` prerequisite; this module closes
//! the Verdict production path without pretending to close that system-wide API.

use fln_core::mode::{Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
use fln_env::constants::{ConstantInfo, TheoremVal};
use fln_env::environment::{
    DeclarationBudget, DeclarationCommitted, DeclarationPlan, DeclarationPublication, Environment,
};
use fln_env::modules::CancellationProbe;
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::verdict::{
    Budget as KernelBudget, Consumption as KernelConsumption, RejectClass, Verdict as KernelVerdict,
};

use crate::{
    CheckedUnsat, DETERMINISTIC_CDCL_POLICY, ProofCheckInconclusive, ProofCheckInternalFault,
    ProofCheckLimits, ProofCheckOutcome, ProofCheckReceipt, ProofRefusal,
    check_unsat_streams_with_cancel,
};

/// The registered algorithm policy for the in-memory reflection/publication path.
///
/// This is not a new durable schema. The only byte streams consumed here retain the
/// already-registered CNF and UNSAT-proof schemas.
pub const REFLECTED_THEOREM_POLICY_ID: &str = "fln.verdict.reflected-theorem-publication/1";

/// Refusal while constructing the non-authoritative reflection candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReflectedArtifactError {
    EmptyBitblastPolicyId,
}

/// Non-authoritative provenance bundled with the exact certificate and theorem.
///
/// Provenance does not certify itself. Authority comes only from replaying the
/// certificate, kernel-checking the theorem, and publishing the same owned theorem.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReflectedTheoremProvenance {
    bitblast_policy_id: &'static str,
    mode: Mode,
    reproducibility: ReproducibilityProfile,
}

impl ReflectedTheoremProvenance {
    pub fn new(
        bitblast_policy_id: &'static str,
        mode: Mode,
        reproducibility: ReproducibilityProfile,
    ) -> Result<Self, ReflectedArtifactError> {
        if bitblast_policy_id.is_empty() {
            return Err(ReflectedArtifactError::EmptyBitblastPolicyId);
        }
        Ok(Self {
            bitblast_policy_id,
            mode,
            reproducibility,
        })
    }

    pub const fn bitblast_policy_id(self) -> &'static str {
        self.bitblast_policy_id
    }

    pub const fn solver_policy_id(self) -> &'static str {
        DETERMINISTIC_CDCL_POLICY.policy_id
    }

    pub const fn reflection_policy_id(self) -> &'static str {
        REFLECTED_THEOREM_POLICY_ID
    }

    pub const fn mode(self) -> Mode {
        self.mode
    }

    pub const fn reproducibility(self) -> ReproducibilityProfile {
        self.reproducibility
    }
}

/// A non-authoritative candidate whose certificate was previously accepted by
/// Verdict's independent checker.
///
/// The fields are private and the type is intentionally not `Clone`: the whole value
/// is consumed by [`publish_reflected_theorem`]. The streams are moved out of
/// [`CheckedUnsat`] without re-encoding, and the theorem has exactly one owned copy in
/// this pipeline.
#[derive(Debug)]
pub struct ReflectedTheoremArtifact {
    cnf_bytes: Box<[u8]>,
    proof_bytes: Box<[u8]>,
    theorem: TheoremVal,
    provenance: ReflectedTheoremProvenance,
}

impl ReflectedTheoremArtifact {
    pub fn from_checked_unsat(
        certificate: CheckedUnsat,
        theorem: TheoremVal,
        provenance: ReflectedTheoremProvenance,
    ) -> Self {
        let (cnf_bytes, proof_bytes) = certificate.into_canonical_streams();
        Self {
            cnf_bytes,
            proof_bytes,
            theorem,
            provenance,
        }
    }

    pub fn theorem_name(&self) -> &Name {
        &self.theorem.base.name
    }

    pub const fn provenance(&self) -> ReflectedTheoremProvenance {
        self.provenance
    }

    pub fn cnf_bytes(&self) -> &[u8] {
        &self.cnf_bytes
    }

    pub fn proof_bytes(&self) -> &[u8] {
        &self.proof_bytes
    }
}

/// Independent checker, kernel, and bounded publication limits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReflectedTheoremLimits {
    pub proof: ProofCheckLimits,
    pub kernel: KernelBudget,
    pub declaration: DeclarationBudget,
    pub collisions: CollisionBudget,
}

impl Default for ReflectedTheoremLimits {
    fn default() -> Self {
        Self {
            proof: ProofCheckLimits::default(),
            kernel: KernelBudget::DEFAULT,
            declaration: DeclarationBudget::UNBOUNDED,
            collisions: CollisionBudget::UNBOUNDED,
        }
    }
}

/// Frozen cancellation points owned by this orchestration layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReflectedTheoremCheckpoint {
    BeforeKernel,
    BeforeAdmission,
}

impl ReflectedTheoremCheckpoint {
    const fn as_str(self) -> &'static str {
        match self {
            Self::BeforeKernel => "reflected-theorem/before-kernel",
            Self::BeforeAdmission => "reflected-theorem/before-admission",
        }
    }
}

/// A completed negative determination. None of these arms publishes a theorem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReflectedTheoremRefusal {
    Proof(ProofRefusal),
    Kernel {
        class: RejectClass,
        message: String,
        consumption: KernelConsumption,
    },
    DuplicateName {
        name: Name,
    },
}

/// A non-answer. It can never carry a publication or theorem verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReflectedTheoremInconclusive {
    Proof(ProofCheckInconclusive),
    Pipeline(Inconclusive),
    Kernel(Inconclusive),
    Admission(Inconclusive),
}

/// An implementation fault. It can never carry a publication or theorem verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReflectedTheoremInternalFault {
    Proof(ProofCheckInternalFault),
    Bridge(InternalFault),
    Kernel(InternalFault),
    Admission(InternalFault),
}

/// The evidence that survives only after the exact theorem was published.
#[derive(Debug, Clone)]
pub struct ReflectedTheoremPublication {
    pub publication: DeclarationPublication,
    pub proof_receipt: ProofCheckReceipt,
    pub kernel_consumption: KernelConsumption,
    pub provenance: ReflectedTheoremProvenance,
}

/// The disjoint terminal classes of reflected theorem publication.
#[derive(Debug)]
#[must_use]
pub enum ReflectedTheoremOutcome {
    Published(ReflectedTheoremPublication),
    Refused(ReflectedTheoremRefusal),
    Inconclusive(ReflectedTheoremInconclusive),
    InternalFault(ReflectedTheoremInternalFault),
}

/// Private typestate: the only declaration this value can publish is the theorem
/// payload moved out of the declaration Crucible just accepted.
struct KernelCheckedTheorem {
    theorem: TheoremVal,
    consumption: KernelConsumption,
}

impl KernelCheckedTheorem {
    fn into_publication_input(self) -> (ConstantInfo, KernelConsumption) {
        (ConstantInfo::Thm(self.theorem), self.consumption)
    }
}

fn is_cancelled(cancellation: Option<&dyn CancellationProbe>) -> bool {
    cancellation.is_some_and(CancellationProbe::is_cancelled)
}

fn cancelled(checkpoint: ReflectedTheoremCheckpoint) -> ReflectedTheoremOutcome {
    ReflectedTheoremOutcome::Inconclusive(ReflectedTheoremInconclusive::Pipeline(
        Inconclusive::cancelled(checkpoint.as_str()),
    ))
}

/// Replay a certificate, kernel-check its reflected theorem, and publish that exact
/// theorem through Grimoire's bounded admission transaction.
///
/// No intermediate authority token is public. Every refusal, cancellation,
/// exhaustion, internal fault, stale plan, or duplicate name returns without an
/// environment containing the candidate theorem.
pub fn publish_reflected_theorem(
    environment: &Environment,
    artifact: ReflectedTheoremArtifact,
    limits: ReflectedTheoremLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> ReflectedTheoremOutcome {
    let proof_receipt = match check_unsat_streams_with_cancel(
        artifact.cnf_bytes.as_ref(),
        artifact.proof_bytes.as_ref(),
        limits.proof,
        || is_cancelled(cancellation),
    ) {
        ProofCheckOutcome::Verified(receipt) => receipt,
        ProofCheckOutcome::Refused(refusal) => {
            return ReflectedTheoremOutcome::Refused(ReflectedTheoremRefusal::Proof(refusal));
        }
        ProofCheckOutcome::Inconclusive(inconclusive) => {
            return ReflectedTheoremOutcome::Inconclusive(ReflectedTheoremInconclusive::Proof(
                inconclusive,
            ));
        }
        ProofCheckOutcome::InternalFault(fault) => {
            return ReflectedTheoremOutcome::InternalFault(ReflectedTheoremInternalFault::Proof(
                fault,
            ));
        }
    };

    if is_cancelled(cancellation) {
        return cancelled(ReflectedTheoremCheckpoint::BeforeKernel);
    }

    let ReflectedTheoremArtifact {
        cnf_bytes: _,
        proof_bytes: _,
        theorem,
        provenance,
    } = artifact;
    let declaration = Declaration::Thm(theorem);
    let kernel_consumption = match fln_kernel::check(environment, &declaration, limits.kernel) {
        Outcome::Complete(KernelVerdict::Accepted { consumption }) => consumption,
        Outcome::Complete(KernelVerdict::Rejected {
            class,
            message,
            consumption,
        }) => {
            return ReflectedTheoremOutcome::Refused(ReflectedTheoremRefusal::Kernel {
                class,
                message,
                consumption,
            });
        }
        Outcome::Inconclusive(inconclusive) => {
            return ReflectedTheoremOutcome::Inconclusive(ReflectedTheoremInconclusive::Kernel(
                inconclusive,
            ));
        }
        Outcome::InternalFault(fault) => {
            return ReflectedTheoremOutcome::InternalFault(ReflectedTheoremInternalFault::Kernel(
                fault,
            ));
        }
    };

    let Declaration::Thm(theorem) = declaration else {
        return ReflectedTheoremOutcome::InternalFault(ReflectedTheoremInternalFault::Bridge(
            InternalFault::new(
                "FL-INV-06",
                "kernel-accepted reflected declaration changed kind before publication",
            ),
        ));
    };
    let checked = KernelCheckedTheorem {
        theorem,
        consumption: kernel_consumption,
    };

    if is_cancelled(cancellation) {
        return cancelled(ReflectedTheoremCheckpoint::BeforeAdmission);
    }

    let (info, kernel_consumption) = checked.into_publication_input();
    let plan = match environment.plan_add_decl(
        info,
        limits.declaration,
        limits.collisions,
        cancellation,
    ) {
        Outcome::Complete(DeclarationPlan::Prepared(plan)) => plan,
        Outcome::Complete(DeclarationPlan::DuplicateName { name }) => {
            return ReflectedTheoremOutcome::Refused(ReflectedTheoremRefusal::DuplicateName {
                name,
            });
        }
        Outcome::Inconclusive(inconclusive) => {
            return ReflectedTheoremOutcome::Inconclusive(ReflectedTheoremInconclusive::Admission(
                inconclusive,
            ));
        }
        Outcome::InternalFault(fault) => {
            return ReflectedTheoremOutcome::InternalFault(
                ReflectedTheoremInternalFault::Admission(fault),
            );
        }
    };

    match plan.commit(environment, cancellation) {
        Outcome::Complete(DeclarationCommitted::Published(publication)) => {
            ReflectedTheoremOutcome::Published(ReflectedTheoremPublication {
                publication,
                proof_receipt,
                kernel_consumption,
                provenance,
            })
        }
        Outcome::Complete(DeclarationCommitted::DuplicateName { name }) => {
            ReflectedTheoremOutcome::Refused(ReflectedTheoremRefusal::DuplicateName { name })
        }
        Outcome::Inconclusive(inconclusive) => ReflectedTheoremOutcome::Inconclusive(
            ReflectedTheoremInconclusive::Admission(inconclusive),
        ),
        Outcome::InternalFault(fault) => {
            ReflectedTheoremOutcome::InternalFault(ReflectedTheoremInternalFault::Admission(fault))
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::AtomicBool;

    use fln_core::expr::{BinderInfo, Expr};
    use fln_core::level::Level;
    use fln_core::mode::{Mode, ReproducibilityProfile};
    use fln_core::name::Name;
    use fln_core::options::KVMap;
    use fln_env::constants::{ConstantInfo, ConstantVal, TheoremVal};
    use fln_env::environment::Environment;
    use fln_kernel::verdict::{Budget as KernelBudget, RejectClass};

    use crate::{
        Clause, ClauseId, Cnf, InputClause, Literal, Polarity, ReflectedTheoremArtifact,
        ReflectedTheoremInconclusive, ReflectedTheoremLimits, ReflectedTheoremOutcome,
        ReflectedTheoremProvenance, ReflectedTheoremRefusal, SchemaLimits, SolverLimits,
        SolverOutcome, VariableId, publish_reflected_theorem, solve,
    };

    fn name(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    fn proposition() -> Expr {
        Expr::sort(Level::zero())
    }

    fn valid_theorem(theorem_name: &str) -> TheoremVal {
        let type_ = Expr::forall_e(
            name("p"),
            proposition(),
            Expr::forall_e(
                name("h"),
                Expr::bvar(0).expect("test bound variable is in range"),
                Expr::bvar(1).expect("test bound variable is in range"),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let value = Expr::lam(
            name("p"),
            proposition(),
            Expr::lam(
                name("h"),
                Expr::bvar(0).expect("test bound variable is in range"),
                Expr::bvar(0).expect("test bound variable is in range"),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        TheoremVal {
            base: ConstantVal {
                name: name(theorem_name),
                level_params: vec![],
                type_,
            },
            value,
            all: vec![name(theorem_name)],
        }
    }

    fn invalid_theorem(theorem_name: &str) -> TheoremVal {
        TheoremVal {
            base: ConstantVal {
                name: name(theorem_name),
                level_params: vec![],
                type_: Expr::sort(Level::one()),
            },
            value: proposition(),
            all: vec![name(theorem_name)],
        }
    }

    fn checked_contradiction() -> Result<crate::CheckedUnsat, String> {
        let variable = VariableId::new(1).expect("test variable is nonzero");
        let positive = Clause::new(vec![Literal::new(variable, Polarity::Positive)])
            .expect("test clause is valid");
        let negative = Clause::new(vec![Literal::new(variable, Polarity::Negative)])
            .expect("test clause is valid");
        let cnf = Cnf::new(
            1,
            vec![
                InputClause::new(
                    ClauseId::new(1).expect("test clause id is nonzero"),
                    positive,
                ),
                InputClause::new(
                    ClauseId::new(2).expect("test clause id is nonzero"),
                    negative,
                ),
            ],
            SchemaLimits::default(),
        )
        .expect("test CNF is valid");
        match solve(&cnf, SolverLimits::default()) {
            SolverOutcome::Unsat { artifact, .. } => Ok(artifact),
            other => Err(format!("unit contradiction must be UNSAT, got {other:?}")),
        }
    }

    fn provenance() -> ReflectedTheoremProvenance {
        ReflectedTheoremProvenance::new(
            "fln.verdict.test-bitblast/1",
            Mode::Sound,
            ReproducibilityProfile::Standard,
        )
        .expect("test policy id is nonempty")
    }

    fn artifact(theorem: TheoremVal) -> ReflectedTheoremArtifact {
        ReflectedTheoremArtifact::from_checked_unsat(
            checked_contradiction().expect("test contradiction produces a certificate"),
            theorem,
            provenance(),
        )
    }

    fn published(
        environment: &Environment,
        artifact: ReflectedTheoremArtifact,
        limits: ReflectedTheoremLimits,
    ) -> Result<super::ReflectedTheoremPublication, String> {
        match publish_reflected_theorem(environment, artifact, limits, None) {
            ReflectedTheoremOutcome::Published(publication) => Ok(publication),
            other => Err(format!(
                "expected reflected theorem publication, got {other:?}"
            )),
        }
    }

    #[test]
    fn reflected_theorem_replay_publishes_the_kernel_checked_owner() {
        let environment = Environment::new();
        let publication = published(
            &environment,
            artifact(valid_theorem("reflected.identity")),
            ReflectedTheoremLimits::default(),
        )
        .expect("valid reflected theorem publishes");

        assert!(
            environment.is_empty(),
            "publication mutated the immutable base"
        );
        assert!(matches!(
            publication
                .publication
                .environment
                .find(&name("reflected.identity")),
            Some(ConstantInfo::Thm(_))
        ));
        assert_eq!(
            publication.publication.digest,
            Environment::decl_content_digest(
                publication
                    .publication
                    .environment
                    .find(&name("reflected.identity"))
                    .expect("published theorem exists")
            )
        );
    }

    #[test]
    fn kernel_admission_boundary_refuses_corrupted_reflected_term() {
        let environment = Environment::new();
        let outcome = publish_reflected_theorem(
            &environment,
            artifact(invalid_theorem("reflected.invalid")),
            ReflectedTheoremLimits::default(),
            None,
        );

        assert!(matches!(
            outcome,
            ReflectedTheoremOutcome::Refused(ReflectedTheoremRefusal::Kernel {
                class: RejectClass::TheoremNotProp,
                ..
            })
        ));
        assert!(environment.is_empty());
    }

    #[test]
    fn kernel_admission_boundary_refuses_proof_corruption_before_theorem_check() {
        let environment = Environment::new();
        let mut candidate = artifact(invalid_theorem("reflected.unreachable"));
        candidate.proof_bytes[0] ^= 0xff;
        let outcome = publish_reflected_theorem(
            &environment,
            candidate,
            ReflectedTheoremLimits::default(),
            None,
        );

        assert!(matches!(
            outcome,
            ReflectedTheoremOutcome::Refused(ReflectedTheoremRefusal::Proof(_))
        ));
        assert!(environment.is_empty());
    }

    #[test]
    fn kernel_admission_boundary_refuses_unknown_proof_version() {
        let environment = Environment::new();
        let mut candidate = artifact(valid_theorem("reflected.unknownVersion"));
        candidate.proof_bytes[9..11].copy_from_slice(&u16::MAX.to_le_bytes());
        let outcome = publish_reflected_theorem(
            &environment,
            candidate,
            ReflectedTheoremLimits::default(),
            None,
        );

        assert!(matches!(
            outcome,
            ReflectedTheoremOutcome::Refused(ReflectedTheoremRefusal::Proof(
                crate::ProofRefusal::UnsupportedVersion { .. }
            ))
        ));
        assert!(environment.is_empty());
    }

    #[test]
    fn kernel_admission_boundary_never_promotes_checker_exhaustion() {
        let environment = Environment::new();
        let limits = ReflectedTheoremLimits {
            proof: crate::ProofCheckLimits {
                max_work_units: 0,
                ..crate::ProofCheckLimits::default()
            },
            ..ReflectedTheoremLimits::default()
        };
        let outcome = publish_reflected_theorem(
            &environment,
            artifact(valid_theorem("reflected.checkerBudget")),
            limits,
            None,
        );

        assert!(matches!(
            outcome,
            ReflectedTheoremOutcome::Inconclusive(ReflectedTheoremInconclusive::Proof(
                crate::ProofCheckInconclusive::ResourceExhausted { .. }
            ))
        ));
        assert!(environment.is_empty());
    }

    #[test]
    fn kernel_admission_boundary_never_promotes_kernel_exhaustion() {
        let environment = Environment::new();
        let limits = ReflectedTheoremLimits {
            kernel: KernelBudget { steps: 0, depth: 1 },
            ..ReflectedTheoremLimits::default()
        };
        let outcome = publish_reflected_theorem(
            &environment,
            artifact(valid_theorem("reflected.kernelBudget")),
            limits,
            None,
        );

        assert!(matches!(
            outcome,
            ReflectedTheoremOutcome::Inconclusive(ReflectedTheoremInconclusive::Kernel(_))
        ));
        assert!(environment.is_empty());
    }

    #[test]
    fn kernel_admission_boundary_never_promotes_cancellation() {
        let environment = Environment::new();
        let cancelled = AtomicBool::new(true);
        let outcome = publish_reflected_theorem(
            &environment,
            artifact(valid_theorem("reflected.cancelled")),
            ReflectedTheoremLimits::default(),
            Some(&cancelled),
        );

        assert!(matches!(
            outcome,
            ReflectedTheoremOutcome::Inconclusive(ReflectedTheoremInconclusive::Proof(
                crate::ProofCheckInconclusive::Cancelled
            ))
        ));
        assert!(environment.is_empty());
    }

    #[test]
    fn kernel_admission_boundary_refuses_duplicate_without_overwrite() {
        let first = published(
            &Environment::new(),
            artifact(valid_theorem("reflected.duplicate")),
            ReflectedTheoremLimits::default(),
        )
        .expect("first declaration publishes");
        let environment = first.publication.environment;
        let before = environment.logical_root(&KVMap::new());
        let outcome = publish_reflected_theorem(
            &environment,
            artifact(valid_theorem("reflected.duplicate")),
            ReflectedTheoremLimits::default(),
            None,
        );

        assert!(matches!(
            outcome,
            ReflectedTheoremOutcome::Refused(ReflectedTheoremRefusal::Kernel {
                class: RejectClass::AlreadyDeclared,
                ..
            })
        ));
        assert_eq!(before, environment.logical_root(&KVMap::new()));
    }

    fn replay_identity() -> (Vec<u8>, Vec<u8>, String, crate::ProofCheckReceipt) {
        let checked = checked_contradiction().expect("test contradiction produces a certificate");
        let cnf_bytes = checked.cnf_bytes().to_vec();
        let proof_bytes = checked.proof_bytes().to_vec();
        let publication = published(
            &Environment::new(),
            ReflectedTheoremArtifact::from_checked_unsat(
                checked,
                valid_theorem("reflected.deterministic"),
                provenance(),
            ),
            ReflectedTheoremLimits::default(),
        )
        .expect("determinism sample publishes");
        (
            cnf_bytes,
            proof_bytes,
            publication.publication.digest.to_string(),
            publication.proof_receipt,
        )
    }

    #[test]
    fn reflected_theorem_replay_is_byte_identical_at_1_8_32_workers() {
        let expected = replay_identity();
        for workers in [1_usize, 8, 32] {
            let handles: Vec<_> = (0..workers)
                .map(|_| std::thread::spawn(replay_identity))
                .collect();
            for handle in handles {
                assert_eq!(
                    handle.join().expect("reflection worker did not panic"),
                    expected
                );
            }
        }
    }
}
