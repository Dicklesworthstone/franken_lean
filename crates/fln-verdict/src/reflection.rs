//! Kernel-bound publication of a Verdict-reflected theorem.
//!
//! The solver and proof checker are deliberately untrusted. This module therefore
//! exposes one whole-pipeline operation rather than a public "checked" token:
//!
//! 1. replay the exact canonical CNF and proof streams with the independent checker;
//! 2. move the one owned theorem declaration into Crucible's opaque
//!    checked-declaration capability;
//! 3. consume that capability to publish into the exact base environment against
//!    which Crucible checked it.
//!
//! There is no second declaration parameter, reconstructed theorem, caller-selected
//! publication base, or equality-based handoff between steps 2 and 3. The capability
//! owns the declaration Crucible accepted, borrows its checked base, and is consumed
//! by publication. Rust's type system is therefore the check-A/publish-A witness.

use fln_core::expr::Expr;
use fln_core::mode::{Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
use fln_env::constants::{ConstantVal, TheoremVal};
use fln_env::environment::{
    DeclarationBudget, DeclarationCommitted, DeclarationPublication, Environment,
};
use fln_env::modules::CancellationProbe;
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{
    Admitted as KernelAdmitted, Published as KernelPublished, admit as kernel_admit,
};
use fln_kernel::verdict::{Budget as KernelBudget, Consumption as KernelConsumption, RejectClass};

use crate::{
    BITBLAST_MANIFEST_ID, BITBLAST_MANIFEST_VERSION, BitblastArtifact, BitblastFacts, CNF_SCHEMA,
    CheckedUnsat, DETERMINISTIC_CDCL_POLICY, ProofCheckInconclusive, ProofCheckInternalFault,
    ProofCheckLimits, ProofCheckOutcome, ProofCheckReceipt, ProofRefusal,
    STREAMING_PROOF_CHECKER_POLICY_ID, SchemaId, UNSAT_PROOF_SCHEMA,
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
    /// The certificate was checked against a different formula than the
    /// canonical bitblast artifact supplied to this construction.
    CnfMismatch {
        bitblast_bytes: u64,
        certificate_bytes: u64,
    },
}

/// Non-authoritative provenance bundled with the exact certificate and theorem.
///
/// Provenance does not certify itself. Authority comes only from replaying the
/// certificate, kernel-checking the theorem, and publishing the same owned theorem.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReflectedTheoremProvenance {
    mode: Mode,
    reproducibility: ReproducibilityProfile,
}

impl ReflectedTheoremProvenance {
    pub const fn new(mode: Mode, reproducibility: ReproducibilityProfile) -> Self {
        Self {
            mode,
            reproducibility,
        }
    }

    pub const fn bitblast_manifest_id(self) -> &'static str {
        BITBLAST_MANIFEST_ID
    }

    pub const fn bitblast_manifest_version(self) -> u16 {
        BITBLAST_MANIFEST_VERSION
    }

    pub const fn bitblast_policy_id(self) -> &'static str {
        crate::CANONICAL_BITBLAST_POLICY_ID
    }

    pub const fn solver_policy_id(self) -> &'static str {
        DETERMINISTIC_CDCL_POLICY.policy_id
    }

    pub const fn proof_checker_policy_id(self) -> &'static str {
        STREAMING_PROOF_CHECKER_POLICY_ID
    }

    pub const fn cnf_schema(self) -> SchemaId {
        CNF_SCHEMA
    }

    pub const fn proof_schema(self) -> SchemaId {
        UNSAT_PROOF_SCHEMA
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
    bitblast_facts: BitblastFacts,
    proof_receipt: ProofCheckReceipt,
    theorem: TheoremVal,
    provenance: ReflectedTheoremProvenance,
}

impl ReflectedTheoremArtifact {
    /// Construct the sole non-authoritative reflection candidate from canonical
    /// bitblast output and a certificate checked against those exact CNF bytes.
    ///
    /// The theorem declaration is assembled here from the exact source
    /// proposition and reflected proof term. Callers cannot hand this boundary an
    /// already-assembled declaration with a different type or membership list.
    /// Crucible still validates the resulting proof term before the opaque
    /// capability can exist.
    pub fn from_bitblast_unsat(
        bitblast: BitblastArtifact,
        certificate: CheckedUnsat,
        theorem_name: Name,
        level_params: Vec<Name>,
        source_proposition: Expr,
        reflected_proof: Expr,
        provenance: ReflectedTheoremProvenance,
    ) -> Result<Self, ReflectedArtifactError> {
        let bitblast_bytes = bitblast.cnf_bytes();
        if bitblast_bytes.as_slice() != certificate.cnf_bytes() {
            return Err(ReflectedArtifactError::CnfMismatch {
                bitblast_bytes: u64::try_from(bitblast_bytes.len()).unwrap_or(u64::MAX),
                certificate_bytes: u64::try_from(certificate.cnf_bytes().len()).unwrap_or(u64::MAX),
            });
        }
        let bitblast_facts = bitblast.facts();
        let proof_receipt = *certificate.receipt();
        let (cnf_bytes, proof_bytes) = certificate.into_canonical_streams();
        let theorem = TheoremVal {
            base: ConstantVal {
                name: theorem_name.clone(),
                level_params,
                type_: source_proposition,
            },
            value: reflected_proof,
            all: vec![theorem_name],
        };
        Ok(Self {
            cnf_bytes,
            proof_bytes,
            bitblast_facts,
            proof_receipt,
            theorem,
            provenance,
        })
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

    pub const fn bitblast_facts(&self) -> BitblastFacts {
        self.bitblast_facts
    }

    pub const fn proof_receipt(&self) -> ProofCheckReceipt {
        self.proof_receipt
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
    cnf_bytes: Box<[u8]>,
    proof_bytes: Box<[u8]>,
    bitblast_facts: BitblastFacts,
}

impl ReflectedTheoremPublication {
    /// The exact canonical CNF stream independently checked before admission.
    pub fn cnf_bytes(&self) -> &[u8] {
        &self.cnf_bytes
    }

    /// The exact proof stream independently checked before admission.
    pub fn proof_bytes(&self) -> &[u8] {
        &self.proof_bytes
    }

    pub const fn bitblast_facts(&self) -> BitblastFacts {
        self.bitblast_facts
    }
}

/// The disjoint terminal classes of reflected theorem publication.
#[derive(Debug)]
#[must_use]
pub enum ReflectedTheoremOutcome {
    Published(Box<ReflectedTheoremPublication>),
    Refused(ReflectedTheoremRefusal),
    Inconclusive(ReflectedTheoremInconclusive),
    InternalFault(ReflectedTheoremInternalFault),
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

    if proof_receipt != artifact.proof_receipt {
        return ReflectedTheoremOutcome::InternalFault(ReflectedTheoremInternalFault::Bridge(
            InternalFault::new(
                "FL-INV-06",
                "independent proof replay changed the certificate receipt",
            ),
        ));
    }

    if is_cancelled(cancellation) {
        return cancelled(ReflectedTheoremCheckpoint::BeforeKernel);
    }

    let ReflectedTheoremArtifact {
        cnf_bytes,
        proof_bytes,
        bitblast_facts,
        proof_receipt: _,
        theorem,
        provenance,
    } = artifact;
    let checked = match kernel_admit(environment, Declaration::Thm(theorem), limits.kernel) {
        Outcome::Complete(KernelAdmitted::Accepted(checked)) => checked,
        Outcome::Complete(KernelAdmitted::Rejected {
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

    if is_cancelled(cancellation) {
        return cancelled(ReflectedTheoremCheckpoint::BeforeAdmission);
    }

    let kernel_consumption = checked.consumption();
    match checked.publish(limits.declaration, limits.collisions, cancellation) {
        Outcome::Complete(KernelPublished::Committed(DeclarationCommitted::Published(
            publication,
        ))) => ReflectedTheoremOutcome::Published(Box::new(ReflectedTheoremPublication {
            publication,
            proof_receipt,
            kernel_consumption,
            provenance,
            cnf_bytes,
            proof_bytes,
            bitblast_facts,
        })),
        Outcome::Complete(KernelPublished::Committed(DeclarationCommitted::DuplicateName {
            name,
        }))
        | Outcome::Complete(KernelPublished::DuplicateName { name }) => {
            ReflectedTheoremOutcome::Refused(ReflectedTheoremRefusal::DuplicateName { name })
        }
        Outcome::Complete(KernelPublished::BlockHandoffUnavailable) => {
            ReflectedTheoremOutcome::InternalFault(ReflectedTheoremInternalFault::Bridge(
                InternalFault::new(
                    "FL-INV-06",
                    "kernel capability lost the single-theorem publication handoff",
                ),
            ))
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
        BITBLAST_MANIFEST_ID, BITBLAST_MANIFEST_VERSION, BitblastArtifact, BitblastOutcome,
        BitblastSymbol, BoolBinaryOp, BoolExpr, CNF_SCHEMA, CheckedUnsat, ReflectedArtifactError,
        ReflectedTheoremArtifact, ReflectedTheoremInconclusive, ReflectedTheoremInternalFault,
        ReflectedTheoremLimits, ReflectedTheoremOutcome, ReflectedTheoremProvenance,
        ReflectedTheoremRefusal, STREAMING_PROOF_CHECKER_POLICY_ID, SolverLimits, SolverOutcome,
        UNSAT_PROOF_SCHEMA, bitblast, publish_reflected_theorem, solve,
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

    fn checked_bitblast(expr: &BoolExpr) -> Result<(BitblastArtifact, CheckedUnsat), String> {
        let bitblast = match bitblast(expr, crate::BitblastLimits::default()) {
            BitblastOutcome::Complete(artifact) => artifact,
            other => return Err(format!("test bitblast must complete, got {other:?}")),
        };
        match solve(bitblast.cnf(), SolverLimits::default()) {
            SolverOutcome::Unsat { artifact, .. } => Ok((bitblast, artifact)),
            other => Err(format!("test bitblast must be UNSAT, got {other:?}")),
        }
    }

    fn provenance() -> ReflectedTheoremProvenance {
        ReflectedTheoremProvenance::new(Mode::Sound, ReproducibilityProfile::Standard)
    }

    fn artifact_from_pair(
        bitblast: BitblastArtifact,
        certificate: CheckedUnsat,
        theorem: TheoremVal,
    ) -> Result<ReflectedTheoremArtifact, ReflectedArtifactError> {
        let TheoremVal { base, value, all } = theorem;
        assert_eq!(
            all,
            vec![base.name.clone()],
            "test theorem membership is canonical"
        );
        ReflectedTheoremArtifact::from_bitblast_unsat(
            bitblast,
            certificate,
            base.name,
            base.level_params,
            base.type_,
            value,
            provenance(),
        )
    }

    fn artifact(theorem: TheoremVal) -> ReflectedTheoremArtifact {
        let (bitblast, certificate) = checked_bitblast(&BoolExpr::Constant(false))
            .expect("false bitblast produces a certificate");
        artifact_from_pair(bitblast, certificate, theorem)
            .expect("certificate belongs to the canonical bitblast")
    }

    fn published(
        environment: &Environment,
        artifact: ReflectedTheoremArtifact,
        limits: ReflectedTheoremLimits,
    ) -> Result<super::ReflectedTheoremPublication, String> {
        match publish_reflected_theorem(environment, artifact, limits, None) {
            ReflectedTheoremOutcome::Published(publication) => Ok(*publication),
            other => Err(format!(
                "expected reflected theorem publication, got {other:?}"
            )),
        }
    }

    #[test]
    fn reflected_theorem_replay_publishes_the_kernel_checked_owner() {
        let environment = Environment::new();
        let expected = valid_theorem("reflected.identity");
        let expected_type = expected.base.type_.clone();
        let publication = published(
            &environment,
            artifact(expected),
            ReflectedTheoremLimits::default(),
        )
        .expect("valid reflected theorem publishes");

        assert!(
            environment.is_empty(),
            "publication mutated the immutable base"
        );
        let published_theorem = publication
            .publication
            .environment
            .find(&name("reflected.identity"));
        assert!(matches!(published_theorem, Some(ConstantInfo::Thm(_))));
        let Some(ConstantInfo::Thm(theorem)) = published_theorem else {
            return;
        };
        assert_eq!(
            theorem.base.type_, expected_type,
            "the exact source proposition must become the checked theorem type"
        );
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
        assert_eq!(
            publication.provenance.bitblast_manifest_id(),
            BITBLAST_MANIFEST_ID
        );
        assert_eq!(
            publication.provenance.bitblast_manifest_version(),
            BITBLAST_MANIFEST_VERSION
        );
        assert_eq!(publication.provenance.cnf_schema(), CNF_SCHEMA);
        assert_eq!(publication.provenance.proof_schema(), UNSAT_PROOF_SCHEMA);
        assert_eq!(
            publication.provenance.proof_checker_policy_id(),
            STREAMING_PROOF_CHECKER_POLICY_ID
        );
        assert_eq!(
            publication.cnf_bytes().len() as u64,
            publication.proof_receipt.cnf_bytes_read
        );
        assert_eq!(
            publication.proof_bytes().len() as u64,
            publication.proof_receipt.proof_bytes_read
        );
        assert_eq!(
            publication.bitblast_facts().encoded_bytes,
            publication.proof_receipt.cnf_bytes_read
        );
    }

    #[test]
    fn reflected_artifact_refuses_a_certificate_from_another_bitblast() {
        let (bitblast, _) = checked_bitblast(&BoolExpr::Constant(false))
            .expect("false bitblast produces a certificate");
        let symbol = BitblastSymbol::new(1).expect("test symbol is nonzero");
        let other = BoolExpr::binary(
            BoolBinaryOp::And,
            BoolExpr::Constant(false),
            BoolExpr::Input(symbol),
        );
        let (_, other_certificate) =
            checked_bitblast(&other).expect("different false formula is still UNSAT");

        let outcome = artifact_from_pair(
            bitblast,
            other_certificate,
            valid_theorem("reflected.mismatch"),
        );
        assert!(matches!(
            outcome,
            Err(ReflectedArtifactError::CnfMismatch { .. })
        ));
    }

    #[test]
    fn kernel_admission_boundary_has_no_raw_check_or_environment_plan_route() {
        let source = include_str!("reflection.rs");
        assert!(
            !source.contains(concat!("fln_kernel::", "check(")),
            "Verdict must enter Crucible through the opaque capability producer"
        );
        assert!(
            !source.contains(concat!(".plan_", "add_decl(")),
            "Verdict must not publish a caller-owned declaration directly"
        );
        assert!(
            source.contains("checked.publish("),
            "the accepted capability must be the publication input"
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
    fn kernel_admission_boundary_refuses_checker_receipt_drift() {
        let environment = Environment::new();
        let mut candidate = artifact(valid_theorem("reflected.receiptDrift"));
        candidate.proof_receipt.work_units = candidate.proof_receipt.work_units.saturating_add(1);
        let outcome = publish_reflected_theorem(
            &environment,
            candidate,
            ReflectedTheoremLimits::default(),
            None,
        );

        assert!(matches!(
            outcome,
            ReflectedTheoremOutcome::InternalFault(ReflectedTheoremInternalFault::Bridge(_))
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
        let (bitblast, checked) = checked_bitblast(&BoolExpr::Constant(false))
            .expect("false bitblast produces a certificate");
        let cnf_bytes = checked.cnf_bytes().to_vec();
        let proof_bytes = checked.proof_bytes().to_vec();
        let publication = published(
            &Environment::new(),
            artifact_from_pair(bitblast, checked, valid_theorem("reflected.deterministic"))
                .expect("certificate belongs to the canonical bitblast"),
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
