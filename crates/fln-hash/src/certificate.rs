//! Canonical declaration-certificate envelope (plan §8.6; bead `fln-7zrh`).
//!
//! A decoded value from this module is only a replay candidate. It cannot admit a
//! declaration, contains no kernel verdict or environment value, and has no API that
//! converts a claimed result into authority. The independent checker or the kernel
//! must still recompute the judgment. Every boundary failure selects recomputation;
//! unknown versions and critical extensions are refused rather than guessed.
//!
//! The certificate term plane is a flat, structure-shared DAG. Every edge points to a
//! smaller node id, so validation and decoding are iterative and bounded by the
//! caller's canonical decode budget. Binder metadata is preserved for faithful export,
//! while free variables, metavariables, universe metavariables, and expression metadata
//! are deliberately absent from the checked kernel-language format.

use std::collections::BTreeSet;

use fln_core::diag::ResourceReason;
use fln_core::expr::{BinderInfo, NatLit};
use fln_core::level::Level;
use fln_core::mode::{BuildProfileId, ContentRoot, EpochId, Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};

use crate::canon::{
    CanonError, CanonReader, CanonWriter, Canonical, DecodeBudget, SCHEMA_DECLARATION_CERTIFICATE,
};
use crate::domain::{Digest, Domain, hash};

/// The community export format resolved by OQ-8.
pub const LEAN4EXPORT_FORMAT_VERSION: &str = "3.1.0";
/// The reviewed upstream exporter revision used to freeze the v3.1.0 row inventory.
pub const LEAN4EXPORT_REVISION: &str = "4e7915201d3f9f04470d9eae002fa695f7cdc589";

/// A node index in the certificate's topologically ordered term DAG.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermNodeId(u32);

impl TermNodeId {
    pub const fn new(value: u32) -> TermNodeId {
        TermNodeId(value)
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

/// Kernel-language expression constructors representable in a certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermNodeV1 {
    BVar {
        index: u32,
    },
    Sort {
        level: Level,
    },
    Const {
        name: Name,
        levels: Vec<Level>,
    },
    App {
        function: TermNodeId,
        argument: TermNodeId,
    },
    Lam {
        binder_name: Name,
        binder_info: BinderInfo,
        domain: TermNodeId,
        body: TermNodeId,
    },
    Forall {
        binder_name: Name,
        binder_info: BinderInfo,
        domain: TermNodeId,
        body: TermNodeId,
    },
    Let {
        declaration_name: Name,
        type_node: TermNodeId,
        value_node: TermNodeId,
        body: TermNodeId,
    },
    Proj {
        type_name: Name,
        index: u32,
        structure: TermNodeId,
    },
    NatLiteral {
        value: NatLit,
    },
    StringLiteral {
        value: String,
    },
}

/// A topologically ordered, structure-shared kernel term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TermDagV1 {
    pub nodes: Vec<TermNodeV1>,
}

impl TermDagV1 {
    /// Root of only the term DAG, excluding producer and environment facts.
    pub fn content_root(&self) -> ContentRoot {
        let mut writer = CanonWriter::new();
        write_term_dag(&mut writer, self);
        ContentRoot::new(hash(Domain::Receipt, &writer.into_bytes()).0)
    }
}

/// Declaration class carried by a declaration-check judgment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclarationKindV1 {
    Axiom,
    Definition,
    Theorem,
    Opaque,
    Quotient,
    Inductive,
    Constructor,
    Recursor,
}

/// The complete top-level judgment inventory supported by schema v1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateJudgmentV1 {
    CheckDeclaration {
        name: Name,
        kind: DeclarationKindV1,
        type_node: TermNodeId,
        value_node: Option<TermNodeId>,
    },
    InferType {
        term_node: TermNodeId,
        inferred_type_node: TermNodeId,
    },
    DefinitionalEquality {
        left_node: TermNodeId,
        right_node: TermNodeId,
        type_node: Option<TermNodeId>,
    },
    WeakHeadNormalForm {
        input_node: TermNodeId,
        output_node: TermNodeId,
    },
    ValidateInductiveGroup {
        names: Vec<Name>,
        type_nodes: Vec<TermNodeId>,
    },
    ValidateQuotientPackage {
        name: Name,
        type_node: TermNodeId,
    },
}

/// Stable negative class claimed by an untrusted producer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClaimedRejectionV1 {
    IllTyped,
    DefinitionalMismatch,
    UniverseViolation,
    PositivityViolation,
    DeclarationConflict,
    UnsafeDeclaration,
}

/// A producer's claim. This is data to compare, never a kernel verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClaimedResultV1 {
    Accepted,
    Rejected(ClaimedRejectionV1),
}

/// Consensus policy whose identity is bound into the candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConsensusPolicyV1 {
    Standard,
    Release,
    Paranoid,
    CompatibilityBenchmark,
}

/// Deterministic resource profile used by the producer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuelProfileV1 {
    pub profile_id: u128,
    pub heartbeats: u64,
    pub recursion_depth: u64,
    pub reduction_steps: u64,
    pub expanded_weight: u64,
    pub allocation_bytes: u64,
}

/// Roots and producer coordinates that must match before replay is attempted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateBindingV1 {
    pub epoch: EpochId,
    pub mode: Mode,
    pub reproducibility: ReproducibilityProfile,
    pub build_profile: BuildProfileId,
    pub consensus_policy: ConsensusPolicyV1,
    pub environment_root: ContentRoot,
    pub dependency_roots: Vec<ContentRoot>,
    pub declaration_root: ContentRoot,
    pub term_root: ContentRoot,
    pub kernel_build_root: ContentRoot,
    pub checker_build_root: ContentRoot,
    pub policy_root: ContentRoot,
    pub engine_id: String,
    pub engine_version: u16,
    pub fuel: FuelProfileV1,
}

/// Nat operations whose accelerated reductions may carry replay transcripts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatOperationV1 {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Gcd,
    Equal,
    LessEqual,
    LessThan,
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
}

impl NatOperationV1 {
    pub const ALL: [NatOperationV1; 15] = [
        NatOperationV1::Add,
        NatOperationV1::Sub,
        NatOperationV1::Mul,
        NatOperationV1::Div,
        NatOperationV1::Mod,
        NatOperationV1::Pow,
        NatOperationV1::Gcd,
        NatOperationV1::Equal,
        NatOperationV1::LessEqual,
        NatOperationV1::LessThan,
        NatOperationV1::BitAnd,
        NatOperationV1::BitOr,
        NatOperationV1::BitXor,
        NatOperationV1::ShiftLeft,
        NatOperationV1::ShiftRight,
    ];

    const fn returns_bool(self) -> bool {
        matches!(
            self,
            NatOperationV1::Equal | NatOperationV1::LessEqual | NatOperationV1::LessThan
        )
    }
}

/// Result of one literal-arithmetic transcript.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatHintResultV1 {
    Nat(NatLit),
    Bool(bool),
}

/// Optional replay hints. A checker may ignore all of them and recompute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReductionHintV1 {
    Unfold {
        declaration: Name,
    },
    NatOperation {
        operation: NatOperationV1,
        inputs: [NatLit; 2],
        result: NatHintResultV1,
    },
}

/// Extension field. Unknown advisory fields survive byte-for-byte; unknown critical
/// fields are refused. Schema v1 intentionally registers no critical extensions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateExtensionV1 {
    pub id: u32,
    pub critical: bool,
    pub payload: Vec<u8>,
}

impl CertificateExtensionV1 {
    pub fn advisory(id: u32, payload: impl Into<Vec<u8>>) -> CertificateExtensionV1 {
        CertificateExtensionV1 {
            id,
            critical: false,
            payload: payload.into(),
        }
    }
}

/// Candidate-only declaration certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclarationCertificateV1 {
    pub binding: CertificateBindingV1,
    pub judgment: CertificateJudgmentV1,
    pub claimed_result: ClaimedResultV1,
    pub term_dag: TermDagV1,
    pub reduction_hints: Vec<ReductionHintV1>,
    pub extensions: Vec<CertificateExtensionV1>,
}

/// Exact structural law violated by an otherwise parseable v1 candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CertificateRuleV1 {
    EmptyEngineId,
    InvalidEngineId,
    ZeroEngineVersion,
    DependencyRootsNotStrictlySorted,
    EmptyTermDag,
    TooManyTermNodes,
    DagReferenceNotBackward,
    AnonymousGlobalName,
    UniverseMetavariable,
    JudgmentReferenceOutOfBounds,
    EmptyInductiveGroup,
    InductiveArityMismatch,
    DuplicateInductiveName,
    TermRootMismatch,
    InvalidHintResult,
    ExtensionsNotStrictlySorted,
}

/// Typed completed refusal. Resource stops remain outcome-level inconclusive values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateRefusalV1 {
    SchemaNameMismatch,
    UnsupportedVersion { seen: u16 },
    Malformed(CanonError),
    InvalidStructure { rule: CertificateRuleV1, index: u64 },
    UnknownCriticalExtension { id: u32 },
}

/// Outcome of decoding an untrusted certificate.
pub type CertificateDecodeOutcomeV1 =
    Outcome<Result<DeclarationCertificateV1, CertificateRefusalV1>>;

impl DeclarationCertificateV1 {
    pub fn new(
        binding: CertificateBindingV1,
        judgment: CertificateJudgmentV1,
        claimed_result: ClaimedResultV1,
        term_dag: TermDagV1,
        reduction_hints: Vec<ReductionHintV1>,
        extensions: Vec<CertificateExtensionV1>,
    ) -> Result<DeclarationCertificateV1, CertificateRefusalV1> {
        let certificate = DeclarationCertificateV1 {
            binding,
            judgment,
            claimed_result,
            term_dag,
            reduction_hints,
            extensions,
        };
        certificate.validate()?;
        Ok(certificate)
    }

    /// Canonical bytes. Invalid in-memory candidates cannot be serialized.
    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>, CertificateRefusalV1> {
        self.validate()?;
        let mut writer = CanonWriter::new();
        writer.schema(SCHEMA_DECLARATION_CERTIFICATE);
        write_binding(&mut writer, &self.binding);
        write_judgment(&mut writer, &self.judgment);
        write_claimed_result(&mut writer, self.claimed_result);
        write_term_dag(&mut writer, &self.term_dag);
        write_hints(&mut writer, &self.reduction_hints);
        write_extensions(&mut writer, &self.extensions);
        Ok(writer.into_bytes())
    }

    /// Receipt-domain identity of the complete canonical envelope.
    pub fn digest(&self) -> Result<Digest, CertificateRefusalV1> {
        Ok(hash(Domain::Receipt, &self.to_canonical_bytes()?))
    }

    pub fn from_canonical_bytes(bytes: &[u8]) -> CertificateDecodeOutcomeV1 {
        Self::from_canonical_bytes_budgeted(bytes, DecodeBudget::unlimited())
    }

    /// Total decode under the caller's structural budget.
    pub fn from_canonical_bytes_budgeted(
        bytes: &[u8],
        budget: DecodeBudget,
    ) -> CertificateDecodeOutcomeV1 {
        let mut reader = CanonReader::with_budget(bytes, budget);

        macro_rules! read {
            ($expression:expr) => {
                match $expression {
                    Ok(value) => value,
                    Err(error) => {
                        return match reader.exhausted() {
                            Some(exhausted) => Outcome::Inconclusive(exhausted.into_inconclusive()),
                            None => Outcome::Complete(Err(CertificateRefusalV1::Malformed(error))),
                        };
                    }
                }
            };
        }

        let schema_name = read!(reader.str());
        if schema_name != SCHEMA_DECLARATION_CERTIFICATE.name {
            return Outcome::Complete(Err(CertificateRefusalV1::SchemaNameMismatch));
        }
        let version = read!(reader.u16());
        if version != SCHEMA_DECLARATION_CERTIFICATE.version {
            return Outcome::Complete(Err(CertificateRefusalV1::UnsupportedVersion {
                seen: version,
            }));
        }

        let binding = read!(read_binding(&mut reader));
        let judgment = read!(read_judgment(&mut reader));
        let claimed_result = read!(read_claimed_result(&mut reader));
        let term_dag = read!(read_term_dag(&mut reader));
        let reduction_hints = read!(read_hints(&mut reader));
        let extensions = read!(read_extensions(&mut reader));

        let certificate = DeclarationCertificateV1 {
            binding,
            judgment,
            claimed_result,
            term_dag,
            reduction_hints,
            extensions,
        };

        let exhausted = reader.exhausted();
        let finish = reader.finish();
        if let Some(exhausted) = exhausted {
            return match finish {
                Ok(()) => Outcome::InternalFault(
                    InternalFault::new(
                        "FL-INV-07",
                        "certificate decode completed after recording a budget stop",
                    )
                    .with_evidence("fln_hash::certificate::from_canonical_bytes_budgeted"),
                ),
                Err(_) => Outcome::Inconclusive(exhausted.into_inconclusive()),
            };
        }
        if let Err(error) = finish {
            return Outcome::Complete(Err(CertificateRefusalV1::Malformed(error)));
        }
        Outcome::Complete(certificate.validate().map(|()| certificate))
    }

    fn validate(&self) -> Result<(), CertificateRefusalV1> {
        validate_engine_id(&self.binding.engine_id)?;
        if self.binding.engine_version == 0 {
            return invalid(CertificateRuleV1::ZeroEngineVersion, 0);
        }
        if !strictly_sorted(&self.binding.dependency_roots) {
            return invalid(CertificateRuleV1::DependencyRootsNotStrictlySorted, 0);
        }
        validate_term_dag(&self.term_dag)?;
        validate_judgment(&self.judgment, self.term_dag.nodes.len())?;
        if self.binding.term_root != self.term_dag.content_root() {
            return invalid(CertificateRuleV1::TermRootMismatch, 0);
        }
        validate_hints(&self.reduction_hints)?;
        validate_extensions(&self.extensions)?;
        Ok(())
    }
}

fn invalid<T>(rule: CertificateRuleV1, index: u64) -> Result<T, CertificateRefusalV1> {
    Err(CertificateRefusalV1::InvalidStructure { rule, index })
}

fn validate_engine_id(engine_id: &str) -> Result<(), CertificateRefusalV1> {
    if engine_id.is_empty() {
        return invalid(CertificateRuleV1::EmptyEngineId, 0);
    }
    if engine_id.len() > 128
        || !engine_id.bytes().all(|byte| {
            byte.is_ascii_lowercase() || byte.is_ascii_digit() || matches!(byte, b'.' | b'-' | b'_')
        })
    {
        return invalid(CertificateRuleV1::InvalidEngineId, 0);
    }
    Ok(())
}

fn strictly_sorted<T: Ord>(values: &[T]) -> bool {
    values.windows(2).all(|pair| pair[0] < pair[1])
}

fn validate_term_dag(dag: &TermDagV1) -> Result<(), CertificateRefusalV1> {
    if dag.nodes.is_empty() {
        return invalid(CertificateRuleV1::EmptyTermDag, 0);
    }
    if dag.nodes.len() > u32::MAX as usize {
        return invalid(CertificateRuleV1::TooManyTermNodes, dag.nodes.len() as u64);
    }
    for (index, node) in dag.nodes.iter().enumerate() {
        let before = index as u32;
        let check_ref = |id: TermNodeId| {
            if id.get() < before {
                Ok(())
            } else {
                invalid(CertificateRuleV1::DagReferenceNotBackward, index as u64)
            }
        };
        match node {
            TermNodeV1::BVar { .. }
            | TermNodeV1::NatLiteral { .. }
            | TermNodeV1::StringLiteral { .. } => {}
            TermNodeV1::Sort { level } => validate_level(level, index)?,
            TermNodeV1::Const { name, levels } => {
                validate_global_name(name, index)?;
                for level in levels {
                    validate_level(level, index)?;
                }
            }
            TermNodeV1::App { function, argument } => {
                check_ref(*function)?;
                check_ref(*argument)?;
            }
            TermNodeV1::Lam { domain, body, .. } | TermNodeV1::Forall { domain, body, .. } => {
                check_ref(*domain)?;
                check_ref(*body)?;
            }
            TermNodeV1::Let {
                type_node,
                value_node,
                body,
                ..
            } => {
                check_ref(*type_node)?;
                check_ref(*value_node)?;
                check_ref(*body)?;
            }
            TermNodeV1::Proj {
                type_name,
                structure,
                ..
            } => {
                validate_global_name(type_name, index)?;
                check_ref(*structure)?;
            }
        }
    }
    Ok(())
}

fn validate_level(level: &Level, index: usize) -> Result<(), CertificateRefusalV1> {
    if level.data().has_mvar() {
        invalid(CertificateRuleV1::UniverseMetavariable, index as u64)
    } else {
        Ok(())
    }
}

fn validate_global_name(name: &Name, index: usize) -> Result<(), CertificateRefusalV1> {
    if name.is_anonymous() {
        invalid(CertificateRuleV1::AnonymousGlobalName, index as u64)
    } else {
        Ok(())
    }
}

fn validate_judgment(
    judgment: &CertificateJudgmentV1,
    node_count: usize,
) -> Result<(), CertificateRefusalV1> {
    let check_ref = |id: TermNodeId| {
        if id.get() as usize >= node_count {
            invalid(
                CertificateRuleV1::JudgmentReferenceOutOfBounds,
                u64::from(id.get()),
            )
        } else {
            Ok(())
        }
    };
    match judgment {
        CertificateJudgmentV1::CheckDeclaration {
            name,
            type_node,
            value_node,
            ..
        } => {
            validate_global_name(name, 0)?;
            check_ref(*type_node)?;
            if let Some(value_node) = value_node {
                check_ref(*value_node)?;
            }
        }
        CertificateJudgmentV1::InferType {
            term_node,
            inferred_type_node,
        } => {
            check_ref(*term_node)?;
            check_ref(*inferred_type_node)?;
        }
        CertificateJudgmentV1::DefinitionalEquality {
            left_node,
            right_node,
            type_node,
        } => {
            check_ref(*left_node)?;
            check_ref(*right_node)?;
            if let Some(type_node) = type_node {
                check_ref(*type_node)?;
            }
        }
        CertificateJudgmentV1::WeakHeadNormalForm {
            input_node,
            output_node,
        } => {
            check_ref(*input_node)?;
            check_ref(*output_node)?;
        }
        CertificateJudgmentV1::ValidateInductiveGroup { names, type_nodes } => {
            if names.is_empty() {
                return invalid(CertificateRuleV1::EmptyInductiveGroup, 0);
            }
            if names.len() != type_nodes.len() {
                return invalid(CertificateRuleV1::InductiveArityMismatch, 0);
            }
            let mut seen = BTreeSet::new();
            for (index, (name, type_node)) in names.iter().zip(type_nodes).enumerate() {
                validate_global_name(name, index)?;
                if !seen.insert(name.clone()) {
                    return invalid(CertificateRuleV1::DuplicateInductiveName, index as u64);
                }
                check_ref(*type_node)?;
            }
        }
        CertificateJudgmentV1::ValidateQuotientPackage { name, type_node } => {
            validate_global_name(name, 0)?;
            check_ref(*type_node)?;
        }
    }
    Ok(())
}

fn validate_hints(hints: &[ReductionHintV1]) -> Result<(), CertificateRefusalV1> {
    for (index, hint) in hints.iter().enumerate() {
        match hint {
            ReductionHintV1::Unfold { declaration } => {
                validate_global_name(declaration, index)?;
            }
            ReductionHintV1::NatOperation {
                operation, result, ..
            } => {
                let result_is_bool = matches!(result, NatHintResultV1::Bool(_));
                if operation.returns_bool() != result_is_bool {
                    return invalid(CertificateRuleV1::InvalidHintResult, index as u64);
                }
            }
        }
    }
    Ok(())
}

fn validate_extensions(extensions: &[CertificateExtensionV1]) -> Result<(), CertificateRefusalV1> {
    if !extensions.windows(2).all(|pair| pair[0].id < pair[1].id) {
        return invalid(CertificateRuleV1::ExtensionsNotStrictlySorted, 0);
    }
    if let Some(extension) = extensions.iter().find(|extension| extension.critical) {
        return Err(CertificateRefusalV1::UnknownCriticalExtension { id: extension.id });
    }
    Ok(())
}

/// Every format boundary state has one deterministic action.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CandidateStateV1 {
    CurrentAndBound,
    Absent,
    UnsupportedVersion,
    Malformed,
    ResourceLimited,
    Cancelled,
    BindingMismatch,
    UnknownCriticalExtension,
    VerificationFailed,
    InternalFault,
}

impl CandidateStateV1 {
    pub const ALL: [CandidateStateV1; 10] = [
        CandidateStateV1::CurrentAndBound,
        CandidateStateV1::Absent,
        CandidateStateV1::UnsupportedVersion,
        CandidateStateV1::Malformed,
        CandidateStateV1::ResourceLimited,
        CandidateStateV1::Cancelled,
        CandidateStateV1::BindingMismatch,
        CandidateStateV1::UnknownCriticalExtension,
        CandidateStateV1::VerificationFailed,
        CandidateStateV1::InternalFault,
    ];
}

/// Pure certificate-use policy. No arm can produce a verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CandidateActionV1 {
    VerifyCandidate,
    Recompute,
    QuarantineAndRecomputeIndependently,
}

pub const fn candidate_action(state: CandidateStateV1) -> CandidateActionV1 {
    match state {
        CandidateStateV1::CurrentAndBound => CandidateActionV1::VerifyCandidate,
        CandidateStateV1::Absent
        | CandidateStateV1::UnsupportedVersion
        | CandidateStateV1::Malformed
        | CandidateStateV1::ResourceLimited
        | CandidateStateV1::Cancelled
        | CandidateStateV1::BindingMismatch
        | CandidateStateV1::UnknownCriticalExtension
        | CandidateStateV1::VerificationFailed => CandidateActionV1::Recompute,
        CandidateStateV1::InternalFault => CandidateActionV1::QuarantineAndRecomputeIndependently,
    }
}

/// Internal fields classified by the OQ-8 export decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Oq8FieldV1 {
    TermDag,
    Judgment,
    ClaimedResult,
    EnvironmentRoot,
    DependencyRoots,
    DeclarationRoot,
    ProducerEngine,
    FuelProfile,
    Mode,
    BuildProfile,
    Extensions,
}

impl Oq8FieldV1 {
    pub const ALL: [Oq8FieldV1; 11] = [
        Oq8FieldV1::TermDag,
        Oq8FieldV1::Judgment,
        Oq8FieldV1::ClaimedResult,
        Oq8FieldV1::EnvironmentRoot,
        Oq8FieldV1::DependencyRoots,
        Oq8FieldV1::DeclarationRoot,
        Oq8FieldV1::ProducerEngine,
        Oq8FieldV1::FuelProfile,
        Oq8FieldV1::Mode,
        Oq8FieldV1::BuildProfile,
        Oq8FieldV1::Extensions,
    ];
}

/// There is intentionally no "drop" projection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Oq8ProjectionV1 {
    Lean4ExportKernelLanguage,
    CertificateSidecar,
    RefuseWithoutRegisteredMapping,
}

pub const fn oq8_projection(field: Oq8FieldV1) -> Oq8ProjectionV1 {
    match field {
        Oq8FieldV1::TermDag | Oq8FieldV1::Judgment => Oq8ProjectionV1::Lean4ExportKernelLanguage,
        Oq8FieldV1::ClaimedResult
        | Oq8FieldV1::EnvironmentRoot
        | Oq8FieldV1::DependencyRoots
        | Oq8FieldV1::DeclarationRoot
        | Oq8FieldV1::ProducerEngine
        | Oq8FieldV1::FuelProfile
        | Oq8FieldV1::Mode
        | Oq8FieldV1::BuildProfile => Oq8ProjectionV1::CertificateSidecar,
        Oq8FieldV1::Extensions => Oq8ProjectionV1::RefuseWithoutRegisteredMapping,
    }
}

/// Frozen lean4export v3.1.0 row inventory used by the projection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lean4ExportRowV1 {
    Meta,
    NameString,
    NameNumeric,
    LevelSucc,
    LevelMax,
    LevelIMax,
    LevelParam,
    ExprBVar,
    ExprSort,
    ExprConst,
    ExprApp,
    ExprLam,
    ExprForall,
    ExprLet,
    ExprProj,
    ExprNatValue,
    ExprStringValue,
    ExprMetadata,
    Axiom,
    Definition,
    Opaque,
    Theorem,
    Quotient,
    InductiveGroup,
}

impl Lean4ExportRowV1 {
    pub const ALL: [Lean4ExportRowV1; 24] = [
        Lean4ExportRowV1::Meta,
        Lean4ExportRowV1::NameString,
        Lean4ExportRowV1::NameNumeric,
        Lean4ExportRowV1::LevelSucc,
        Lean4ExportRowV1::LevelMax,
        Lean4ExportRowV1::LevelIMax,
        Lean4ExportRowV1::LevelParam,
        Lean4ExportRowV1::ExprBVar,
        Lean4ExportRowV1::ExprSort,
        Lean4ExportRowV1::ExprConst,
        Lean4ExportRowV1::ExprApp,
        Lean4ExportRowV1::ExprLam,
        Lean4ExportRowV1::ExprForall,
        Lean4ExportRowV1::ExprLet,
        Lean4ExportRowV1::ExprProj,
        Lean4ExportRowV1::ExprNatValue,
        Lean4ExportRowV1::ExprStringValue,
        Lean4ExportRowV1::ExprMetadata,
        Lean4ExportRowV1::Axiom,
        Lean4ExportRowV1::Definition,
        Lean4ExportRowV1::Opaque,
        Lean4ExportRowV1::Theorem,
        Lean4ExportRowV1::Quotient,
        Lean4ExportRowV1::InductiveGroup,
    ];
}

/// Exact term-row projection. Expression metadata has no input variant here because
/// it is nonsemantic to the kernel and lean4export strips it unless explicitly asked
/// to preserve it.
pub const fn lean4export_row_for_term(node: &TermNodeV1) -> Lean4ExportRowV1 {
    match node {
        TermNodeV1::BVar { .. } => Lean4ExportRowV1::ExprBVar,
        TermNodeV1::Sort { .. } => Lean4ExportRowV1::ExprSort,
        TermNodeV1::Const { .. } => Lean4ExportRowV1::ExprConst,
        TermNodeV1::App { .. } => Lean4ExportRowV1::ExprApp,
        TermNodeV1::Lam { .. } => Lean4ExportRowV1::ExprLam,
        TermNodeV1::Forall { .. } => Lean4ExportRowV1::ExprForall,
        TermNodeV1::Let { .. } => Lean4ExportRowV1::ExprLet,
        TermNodeV1::Proj { .. } => Lean4ExportRowV1::ExprProj,
        TermNodeV1::NatLiteral { .. } => Lean4ExportRowV1::ExprNatValue,
        TermNodeV1::StringLiteral { .. } => Lean4ExportRowV1::ExprStringValue,
    }
}

/// Exact declaration-row projection. Constructors and recursors are members of the
/// exporter's inductive-group row rather than free-standing declarations.
pub const fn lean4export_row_for_declaration(kind: DeclarationKindV1) -> Lean4ExportRowV1 {
    match kind {
        DeclarationKindV1::Axiom => Lean4ExportRowV1::Axiom,
        DeclarationKindV1::Definition => Lean4ExportRowV1::Definition,
        DeclarationKindV1::Theorem => Lean4ExportRowV1::Theorem,
        DeclarationKindV1::Opaque => Lean4ExportRowV1::Opaque,
        DeclarationKindV1::Quotient => Lean4ExportRowV1::Quotient,
        DeclarationKindV1::Inductive
        | DeclarationKindV1::Constructor
        | DeclarationKindV1::Recursor => Lean4ExportRowV1::InductiveGroup,
    }
}

fn write_binding(writer: &mut CanonWriter, binding: &CertificateBindingV1) {
    write_u128(writer, binding.epoch.get());
    writer.u8(binding.mode.tag());
    writer.u8(binding.reproducibility.tag());
    write_u128(writer, binding.build_profile.get());
    writer.u8(consensus_policy_tag(binding.consensus_policy));
    write_root(writer, binding.environment_root);
    writer.u64(binding.dependency_roots.len() as u64);
    for root in &binding.dependency_roots {
        write_root(writer, *root);
    }
    write_root(writer, binding.declaration_root);
    write_root(writer, binding.term_root);
    write_root(writer, binding.kernel_build_root);
    write_root(writer, binding.checker_build_root);
    write_root(writer, binding.policy_root);
    writer.str(&binding.engine_id);
    writer.u16(binding.engine_version);
    write_u128(writer, binding.fuel.profile_id);
    writer.u64(binding.fuel.heartbeats);
    writer.u64(binding.fuel.recursion_depth);
    writer.u64(binding.fuel.reduction_steps);
    writer.u64(binding.fuel.expanded_weight);
    writer.u64(binding.fuel.allocation_bytes);
}

fn read_binding(reader: &mut CanonReader<'_>) -> Result<CertificateBindingV1, CanonError> {
    let epoch = EpochId::new(read_u128(reader)?);
    let mode = Mode::from_tag(Some(reader.u8()?))
        .map_err(|_| reader.reject("unknown certificate mode"))?;
    let reproducibility = ReproducibilityProfile::from_tag(Some(reader.u8()?))
        .map_err(|_| reader.reject("unknown certificate reproducibility profile"))?;
    let build_profile = BuildProfileId::new(read_u128(reader)?);
    let consensus_policy = read_consensus_policy(reader)?;
    let environment_root = read_root(reader)?;
    let dependency_roots = read_vec(reader, read_root)?;
    let declaration_root = read_root(reader)?;
    let term_root = read_root(reader)?;
    let kernel_build_root = read_root(reader)?;
    let checker_build_root = read_root(reader)?;
    let policy_root = read_root(reader)?;
    let engine_id = reader.str()?.to_owned();
    reader.charge_node()?;
    let engine_version = reader.u16()?;
    let fuel = FuelProfileV1 {
        profile_id: read_u128(reader)?,
        heartbeats: reader.u64()?,
        recursion_depth: reader.u64()?,
        reduction_steps: reader.u64()?,
        expanded_weight: reader.u64()?,
        allocation_bytes: reader.u64()?,
    };
    Ok(CertificateBindingV1 {
        epoch,
        mode,
        reproducibility,
        build_profile,
        consensus_policy,
        environment_root,
        dependency_roots,
        declaration_root,
        term_root,
        kernel_build_root,
        checker_build_root,
        policy_root,
        engine_id,
        engine_version,
        fuel,
    })
}

fn write_term_dag(writer: &mut CanonWriter, dag: &TermDagV1) {
    writer.u64(dag.nodes.len() as u64);
    for node in &dag.nodes {
        write_term_node(writer, node);
    }
}

fn read_term_dag(reader: &mut CanonReader<'_>) -> Result<TermDagV1, CanonError> {
    let nodes = read_vec(reader, read_term_node)?;
    Ok(TermDagV1 { nodes })
}

fn write_term_node(writer: &mut CanonWriter, node: &TermNodeV1) {
    match node {
        TermNodeV1::BVar { index } => {
            writer.u8(0);
            writer.u32(*index);
        }
        TermNodeV1::Sort { level } => {
            writer.u8(1);
            write_level(writer, level);
        }
        TermNodeV1::Const { name, levels } => {
            writer.u8(2);
            write_name(writer, name);
            writer.u64(levels.len() as u64);
            for level in levels {
                write_level(writer, level);
            }
        }
        TermNodeV1::App { function, argument } => {
            writer.u8(3);
            write_node_id(writer, *function);
            write_node_id(writer, *argument);
        }
        TermNodeV1::Lam {
            binder_name,
            binder_info,
            domain,
            body,
        } => {
            writer.u8(4);
            write_name(writer, binder_name);
            writer.u8(binder_info_tag(*binder_info));
            write_node_id(writer, *domain);
            write_node_id(writer, *body);
        }
        TermNodeV1::Forall {
            binder_name,
            binder_info,
            domain,
            body,
        } => {
            writer.u8(5);
            write_name(writer, binder_name);
            writer.u8(binder_info_tag(*binder_info));
            write_node_id(writer, *domain);
            write_node_id(writer, *body);
        }
        TermNodeV1::Let {
            declaration_name,
            type_node,
            value_node,
            body,
        } => {
            writer.u8(6);
            write_name(writer, declaration_name);
            write_node_id(writer, *type_node);
            write_node_id(writer, *value_node);
            write_node_id(writer, *body);
        }
        TermNodeV1::Proj {
            type_name,
            index,
            structure,
        } => {
            writer.u8(7);
            write_name(writer, type_name);
            writer.u32(*index);
            write_node_id(writer, *structure);
        }
        TermNodeV1::NatLiteral { value } => {
            writer.u8(8);
            write_nat(writer, value);
        }
        TermNodeV1::StringLiteral { value } => {
            writer.u8(9);
            writer.str(value);
        }
    }
}

fn read_term_node(reader: &mut CanonReader<'_>) -> Result<TermNodeV1, CanonError> {
    match reader.u8()? {
        0 => Ok(TermNodeV1::BVar {
            index: reader.u32()?,
        }),
        1 => Ok(TermNodeV1::Sort {
            level: read_level(reader)?,
        }),
        2 => Ok(TermNodeV1::Const {
            name: read_name(reader)?,
            levels: read_vec(reader, read_level)?,
        }),
        3 => Ok(TermNodeV1::App {
            function: read_node_id(reader)?,
            argument: read_node_id(reader)?,
        }),
        4 => Ok(TermNodeV1::Lam {
            binder_name: read_name(reader)?,
            binder_info: read_binder_info(reader)?,
            domain: read_node_id(reader)?,
            body: read_node_id(reader)?,
        }),
        5 => Ok(TermNodeV1::Forall {
            binder_name: read_name(reader)?,
            binder_info: read_binder_info(reader)?,
            domain: read_node_id(reader)?,
            body: read_node_id(reader)?,
        }),
        6 => Ok(TermNodeV1::Let {
            declaration_name: read_name(reader)?,
            type_node: read_node_id(reader)?,
            value_node: read_node_id(reader)?,
            body: read_node_id(reader)?,
        }),
        7 => Ok(TermNodeV1::Proj {
            type_name: read_name(reader)?,
            index: reader.u32()?,
            structure: read_node_id(reader)?,
        }),
        8 => Ok(TermNodeV1::NatLiteral {
            value: read_nat(reader)?,
        }),
        9 => Ok(TermNodeV1::StringLiteral {
            value: reader.str()?.to_owned(),
        }),
        _ => Err(reader.reject("unknown certificate term-node tag")),
    }
}

fn write_judgment(writer: &mut CanonWriter, judgment: &CertificateJudgmentV1) {
    match judgment {
        CertificateJudgmentV1::CheckDeclaration {
            name,
            kind,
            type_node,
            value_node,
        } => {
            writer.u8(0);
            write_name(writer, name);
            writer.u8(declaration_kind_tag(*kind));
            write_node_id(writer, *type_node);
            write_optional_node_id(writer, *value_node);
        }
        CertificateJudgmentV1::InferType {
            term_node,
            inferred_type_node,
        } => {
            writer.u8(1);
            write_node_id(writer, *term_node);
            write_node_id(writer, *inferred_type_node);
        }
        CertificateJudgmentV1::DefinitionalEquality {
            left_node,
            right_node,
            type_node,
        } => {
            writer.u8(2);
            write_node_id(writer, *left_node);
            write_node_id(writer, *right_node);
            write_optional_node_id(writer, *type_node);
        }
        CertificateJudgmentV1::WeakHeadNormalForm {
            input_node,
            output_node,
        } => {
            writer.u8(3);
            write_node_id(writer, *input_node);
            write_node_id(writer, *output_node);
        }
        CertificateJudgmentV1::ValidateInductiveGroup { names, type_nodes } => {
            writer.u8(4);
            writer.u64(names.len() as u64);
            for name in names {
                write_name(writer, name);
            }
            writer.u64(type_nodes.len() as u64);
            for node in type_nodes {
                write_node_id(writer, *node);
            }
        }
        CertificateJudgmentV1::ValidateQuotientPackage { name, type_node } => {
            writer.u8(5);
            write_name(writer, name);
            write_node_id(writer, *type_node);
        }
    }
}

fn read_judgment(reader: &mut CanonReader<'_>) -> Result<CertificateJudgmentV1, CanonError> {
    match reader.u8()? {
        0 => Ok(CertificateJudgmentV1::CheckDeclaration {
            name: read_name(reader)?,
            kind: read_declaration_kind(reader)?,
            type_node: read_node_id(reader)?,
            value_node: read_optional_node_id(reader)?,
        }),
        1 => Ok(CertificateJudgmentV1::InferType {
            term_node: read_node_id(reader)?,
            inferred_type_node: read_node_id(reader)?,
        }),
        2 => Ok(CertificateJudgmentV1::DefinitionalEquality {
            left_node: read_node_id(reader)?,
            right_node: read_node_id(reader)?,
            type_node: read_optional_node_id(reader)?,
        }),
        3 => Ok(CertificateJudgmentV1::WeakHeadNormalForm {
            input_node: read_node_id(reader)?,
            output_node: read_node_id(reader)?,
        }),
        4 => Ok(CertificateJudgmentV1::ValidateInductiveGroup {
            names: read_vec(reader, read_name)?,
            type_nodes: read_vec(reader, read_node_id)?,
        }),
        5 => Ok(CertificateJudgmentV1::ValidateQuotientPackage {
            name: read_name(reader)?,
            type_node: read_node_id(reader)?,
        }),
        _ => Err(reader.reject("unknown certificate judgment tag")),
    }
}

fn write_claimed_result(writer: &mut CanonWriter, result: ClaimedResultV1) {
    match result {
        ClaimedResultV1::Accepted => writer.u8(0),
        ClaimedResultV1::Rejected(class) => {
            writer.u8(1);
            writer.u8(rejection_tag(class));
        }
    }
}

fn read_claimed_result(reader: &mut CanonReader<'_>) -> Result<ClaimedResultV1, CanonError> {
    match reader.u8()? {
        0 => Ok(ClaimedResultV1::Accepted),
        1 => Ok(ClaimedResultV1::Rejected(read_rejection(reader)?)),
        _ => Err(reader.reject("unknown certificate result tag")),
    }
}

fn write_hints(writer: &mut CanonWriter, hints: &[ReductionHintV1]) {
    writer.u64(hints.len() as u64);
    for hint in hints {
        match hint {
            ReductionHintV1::Unfold { declaration } => {
                writer.u8(0);
                write_name(writer, declaration);
            }
            ReductionHintV1::NatOperation {
                operation,
                inputs,
                result,
            } => {
                writer.u8(1);
                writer.u8(nat_operation_tag(*operation));
                write_nat(writer, &inputs[0]);
                write_nat(writer, &inputs[1]);
                match result {
                    NatHintResultV1::Nat(value) => {
                        writer.u8(0);
                        write_nat(writer, value);
                    }
                    NatHintResultV1::Bool(value) => {
                        writer.u8(1);
                        writer.bool(*value);
                    }
                }
            }
        }
    }
}

fn read_hints(reader: &mut CanonReader<'_>) -> Result<Vec<ReductionHintV1>, CanonError> {
    read_vec(reader, |reader| match reader.u8()? {
        0 => Ok(ReductionHintV1::Unfold {
            declaration: read_name(reader)?,
        }),
        1 => {
            let operation = read_nat_operation(reader)?;
            let inputs = [read_nat(reader)?, read_nat(reader)?];
            let result = match reader.u8()? {
                0 => NatHintResultV1::Nat(read_nat(reader)?),
                1 => NatHintResultV1::Bool(reader.bool()?),
                _ => return Err(reader.reject("unknown nat-hint result tag")),
            };
            Ok(ReductionHintV1::NatOperation {
                operation,
                inputs,
                result,
            })
        }
        _ => Err(reader.reject("unknown reduction-hint tag")),
    })
}

fn write_extensions(writer: &mut CanonWriter, extensions: &[CertificateExtensionV1]) {
    writer.u64(extensions.len() as u64);
    for extension in extensions {
        writer.u32(extension.id);
        writer.bool(extension.critical);
        writer.bytes(&extension.payload);
    }
}

fn read_extensions(
    reader: &mut CanonReader<'_>,
) -> Result<Vec<CertificateExtensionV1>, CanonError> {
    read_vec(reader, |reader| {
        Ok(CertificateExtensionV1 {
            id: reader.u32()?,
            critical: reader.bool()?,
            payload: reader.bytes()?.to_vec(),
        })
    })
}

fn write_name(writer: &mut CanonWriter, name: &Name) {
    writer.bytes(&name.to_canonical_bytes());
}

fn read_name(reader: &mut CanonReader<'_>) -> Result<Name, CanonError> {
    let bytes = reader.bytes()?;
    reader.charge_node()?;
    Name::from_canonical_bytes(bytes).map_err(|_| reader.reject("invalid nested name"))
}

fn write_level(writer: &mut CanonWriter, level: &Level) {
    writer.bytes(&level.to_canonical_bytes());
}

fn read_level(reader: &mut CanonReader<'_>) -> Result<Level, CanonError> {
    let bytes = reader.bytes()?;
    reader.charge_node()?;
    Level::from_canonical_bytes(bytes).map_err(|_| reader.reject("invalid nested level"))
}

fn write_nat(writer: &mut CanonWriter, value: &NatLit) {
    writer.u64(value.limbs_le().len() as u64);
    for limb in value.limbs_le() {
        writer.u64(*limb);
    }
}

fn read_nat(reader: &mut CanonReader<'_>) -> Result<NatLit, CanonError> {
    let limbs = read_vec(reader, |reader| reader.u64())?;
    if limbs.last() == Some(&0) {
        return Err(reader.reject("non-canonical natural literal"));
    }
    Ok(NatLit::from_limbs_le(limbs))
}

fn write_root(writer: &mut CanonWriter, root: ContentRoot) {
    writer.bytes(&root.bytes());
}

fn read_root(reader: &mut CanonReader<'_>) -> Result<ContentRoot, CanonError> {
    let bytes = reader.bytes()?;
    let bytes: [u8; 32] = bytes
        .try_into()
        .map_err(|_| reader.reject("certificate root must be 32 bytes"))?;
    Ok(ContentRoot::new(bytes))
}

fn write_u128(writer: &mut CanonWriter, value: u128) {
    writer.bytes(&value.to_le_bytes());
}

fn read_u128(reader: &mut CanonReader<'_>) -> Result<u128, CanonError> {
    let bytes = reader.bytes()?;
    let bytes: [u8; 16] = bytes
        .try_into()
        .map_err(|_| reader.reject("certificate id must be 16 bytes"))?;
    Ok(u128::from_le_bytes(bytes))
}

fn write_node_id(writer: &mut CanonWriter, node: TermNodeId) {
    writer.u32(node.get());
}

fn read_node_id(reader: &mut CanonReader<'_>) -> Result<TermNodeId, CanonError> {
    Ok(TermNodeId::new(reader.u32()?))
}

fn write_optional_node_id(writer: &mut CanonWriter, node: Option<TermNodeId>) {
    match node {
        None => writer.u8(0),
        Some(node) => {
            writer.u8(1);
            write_node_id(writer, node);
        }
    }
}

fn read_optional_node_id(reader: &mut CanonReader<'_>) -> Result<Option<TermNodeId>, CanonError> {
    match reader.u8()? {
        0 => Ok(None),
        1 => Ok(Some(read_node_id(reader)?)),
        _ => Err(reader.reject("non-canonical optional node id")),
    }
}

fn read_vec<T>(
    reader: &mut CanonReader<'_>,
    mut read_item: impl FnMut(&mut CanonReader<'_>) -> Result<T, CanonError>,
) -> Result<Vec<T>, CanonError> {
    let count = reader.u64()?;
    let mut values = Vec::new();
    for _ in 0..count {
        reader.charge_node()?;
        values.push(read_item(reader)?);
    }
    Ok(values)
}

const fn binder_info_tag(info: BinderInfo) -> u8 {
    match info {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

fn read_binder_info(reader: &mut CanonReader<'_>) -> Result<BinderInfo, CanonError> {
    match reader.u8()? {
        0 => Ok(BinderInfo::Default),
        1 => Ok(BinderInfo::Implicit),
        2 => Ok(BinderInfo::StrictImplicit),
        3 => Ok(BinderInfo::InstImplicit),
        _ => Err(reader.reject("unknown binder-info tag")),
    }
}

const fn declaration_kind_tag(kind: DeclarationKindV1) -> u8 {
    match kind {
        DeclarationKindV1::Axiom => 0,
        DeclarationKindV1::Definition => 1,
        DeclarationKindV1::Theorem => 2,
        DeclarationKindV1::Opaque => 3,
        DeclarationKindV1::Quotient => 4,
        DeclarationKindV1::Inductive => 5,
        DeclarationKindV1::Constructor => 6,
        DeclarationKindV1::Recursor => 7,
    }
}

fn read_declaration_kind(reader: &mut CanonReader<'_>) -> Result<DeclarationKindV1, CanonError> {
    match reader.u8()? {
        0 => Ok(DeclarationKindV1::Axiom),
        1 => Ok(DeclarationKindV1::Definition),
        2 => Ok(DeclarationKindV1::Theorem),
        3 => Ok(DeclarationKindV1::Opaque),
        4 => Ok(DeclarationKindV1::Quotient),
        5 => Ok(DeclarationKindV1::Inductive),
        6 => Ok(DeclarationKindV1::Constructor),
        7 => Ok(DeclarationKindV1::Recursor),
        _ => Err(reader.reject("unknown declaration-kind tag")),
    }
}

const fn consensus_policy_tag(policy: ConsensusPolicyV1) -> u8 {
    match policy {
        ConsensusPolicyV1::Standard => 0,
        ConsensusPolicyV1::Release => 1,
        ConsensusPolicyV1::Paranoid => 2,
        ConsensusPolicyV1::CompatibilityBenchmark => 3,
    }
}

fn read_consensus_policy(reader: &mut CanonReader<'_>) -> Result<ConsensusPolicyV1, CanonError> {
    match reader.u8()? {
        0 => Ok(ConsensusPolicyV1::Standard),
        1 => Ok(ConsensusPolicyV1::Release),
        2 => Ok(ConsensusPolicyV1::Paranoid),
        3 => Ok(ConsensusPolicyV1::CompatibilityBenchmark),
        _ => Err(reader.reject("unknown consensus-policy tag")),
    }
}

const fn rejection_tag(class: ClaimedRejectionV1) -> u8 {
    match class {
        ClaimedRejectionV1::IllTyped => 0,
        ClaimedRejectionV1::DefinitionalMismatch => 1,
        ClaimedRejectionV1::UniverseViolation => 2,
        ClaimedRejectionV1::PositivityViolation => 3,
        ClaimedRejectionV1::DeclarationConflict => 4,
        ClaimedRejectionV1::UnsafeDeclaration => 5,
    }
}

fn read_rejection(reader: &mut CanonReader<'_>) -> Result<ClaimedRejectionV1, CanonError> {
    match reader.u8()? {
        0 => Ok(ClaimedRejectionV1::IllTyped),
        1 => Ok(ClaimedRejectionV1::DefinitionalMismatch),
        2 => Ok(ClaimedRejectionV1::UniverseViolation),
        3 => Ok(ClaimedRejectionV1::PositivityViolation),
        4 => Ok(ClaimedRejectionV1::DeclarationConflict),
        5 => Ok(ClaimedRejectionV1::UnsafeDeclaration),
        _ => Err(reader.reject("unknown rejection-class tag")),
    }
}

const fn nat_operation_tag(operation: NatOperationV1) -> u8 {
    match operation {
        NatOperationV1::Add => 0,
        NatOperationV1::Sub => 1,
        NatOperationV1::Mul => 2,
        NatOperationV1::Div => 3,
        NatOperationV1::Mod => 4,
        NatOperationV1::Pow => 5,
        NatOperationV1::Gcd => 6,
        NatOperationV1::Equal => 7,
        NatOperationV1::LessEqual => 8,
        NatOperationV1::LessThan => 9,
        NatOperationV1::BitAnd => 10,
        NatOperationV1::BitOr => 11,
        NatOperationV1::BitXor => 12,
        NatOperationV1::ShiftLeft => 13,
        NatOperationV1::ShiftRight => 14,
    }
}

fn read_nat_operation(reader: &mut CanonReader<'_>) -> Result<NatOperationV1, CanonError> {
    match reader.u8()? {
        0 => Ok(NatOperationV1::Add),
        1 => Ok(NatOperationV1::Sub),
        2 => Ok(NatOperationV1::Mul),
        3 => Ok(NatOperationV1::Div),
        4 => Ok(NatOperationV1::Mod),
        5 => Ok(NatOperationV1::Pow),
        6 => Ok(NatOperationV1::Gcd),
        7 => Ok(NatOperationV1::Equal),
        8 => Ok(NatOperationV1::LessEqual),
        9 => Ok(NatOperationV1::LessThan),
        10 => Ok(NatOperationV1::BitAnd),
        11 => Ok(NatOperationV1::BitOr),
        12 => Ok(NatOperationV1::BitXor),
        13 => Ok(NatOperationV1::ShiftLeft),
        14 => Ok(NatOperationV1::ShiftRight),
        _ => Err(reader.reject("unknown nat-operation tag")),
    }
}

// ---------------------------------------------------------------------------
// Bounded Certificate Verifier & Governed Recomputation Fallback (W3, fln-eeyn)
// ---------------------------------------------------------------------------

/// Bounded verification budget for fast-path certificate verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifierBudget {
    pub decode_budget: DecodeBudget,
    pub max_steps: u64,
    pub max_extension_count: u32,
    pub max_extension_bytes: usize,
    pub steps_consumed: u64,
    pub cancelled: bool,
}

impl VerifierBudget {
    pub fn new(max_steps: u64) -> Self {
        Self {
            decode_budget: DecodeBudget::new(16 * 1024 * 1024, 1_000_000),
            max_steps,
            max_extension_count: 64,
            max_extension_bytes: 1024 * 1024,
            steps_consumed: 0,
            cancelled: false,
        }
    }

    pub fn with_decode_budget(mut self, decode_budget: DecodeBudget) -> Self {
        self.decode_budget = decode_budget;
        self
    }

    pub fn with_extension_limits(mut self, max_count: u32, max_bytes: usize) -> Self {
        self.max_extension_count = max_count;
        self.max_extension_bytes = max_bytes;
        self
    }

    pub fn cancel(&mut self) {
        self.cancelled = true;
    }

    pub fn is_cancelled(&self) -> bool {
        self.cancelled
    }

    pub fn consume_step(&mut self, count: u64) -> Result<(), Inconclusive> {
        if self.cancelled {
            return Err(Inconclusive::cancelled(
                "certificate verification cancelled",
            ));
        }
        self.steps_consumed = self.steps_consumed.saturating_add(count);
        if self.steps_consumed > self.max_steps {
            Err(Inconclusive::resource(ResourceUsage {
                reason: ResourceReason::ExecutionSteps,
                allowed: self.max_steps,
                observed: self.steps_consumed,
            }))
        } else {
            Ok(())
        }
    }
}

/// Verification context specifying the expected candidate binding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifierContext {
    pub expected_epoch: Option<EpochId>,
    pub expected_mode: Option<Mode>,
    pub expected_environment_root: Option<ContentRoot>,
    pub expected_declaration_root: Option<ContentRoot>,
    pub expected_build_profile: Option<BuildProfileId>,
    pub expected_consensus_policy: Option<ConsensusPolicyV1>,
    pub allow_advisory_extensions: bool,
    pub allow_rejections: bool,
}

impl Default for VerifierContext {
    fn default() -> Self {
        Self {
            expected_epoch: None,
            expected_mode: None,
            expected_environment_root: None,
            expected_declaration_root: None,
            expected_build_profile: None,
            expected_consensus_policy: None,
            allow_advisory_extensions: true,
            allow_rejections: false,
        }
    }
}

impl VerifierContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn matching_binding(binding: &CertificateBindingV1) -> Self {
        Self {
            expected_epoch: Some(binding.epoch),
            expected_mode: Some(binding.mode),
            expected_environment_root: Some(binding.environment_root),
            expected_declaration_root: Some(binding.declaration_root),
            expected_build_profile: Some(binding.build_profile),
            expected_consensus_policy: Some(binding.consensus_policy),
            allow_advisory_extensions: true,
            allow_rejections: false,
        }
    }

    pub fn with_epoch(mut self, epoch: EpochId) -> Self {
        self.expected_epoch = Some(epoch);
        self
    }

    pub fn with_mode(mut self, mode: Mode) -> Self {
        self.expected_mode = Some(mode);
        self
    }

    pub fn with_environment_root(mut self, root: ContentRoot) -> Self {
        self.expected_environment_root = Some(root);
        self
    }

    pub fn with_declaration_root(mut self, root: ContentRoot) -> Self {
        self.expected_declaration_root = Some(root);
        self
    }

    pub fn with_build_profile(mut self, profile: BuildProfileId) -> Self {
        self.expected_build_profile = Some(profile);
        self
    }

    pub fn with_consensus_policy(mut self, policy: ConsensusPolicyV1) -> Self {
        self.expected_consensus_policy = Some(policy);
        self
    }

    pub fn with_allow_advisory_extensions(mut self, allow: bool) -> Self {
        self.allow_advisory_extensions = allow;
        self
    }

    pub fn with_allow_rejections(mut self, allow: bool) -> Self {
        self.allow_rejections = allow;
        self
    }
}

/// Detailed refusal reason when a candidate certificate fails fast-path verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateVerificationRefusal {
    DecodeRefused(CertificateRefusalV1),
    StaleEpoch {
        expected: EpochId,
        seen: EpochId,
    },
    ModeMismatch {
        expected: Mode,
        seen: Mode,
    },
    EnvironmentRootMismatch {
        expected: ContentRoot,
        seen: ContentRoot,
    },
    DeclarationRootMismatch {
        expected: ContentRoot,
        seen: ContentRoot,
    },
    BuildProfileMismatch {
        expected: BuildProfileId,
        seen: BuildProfileId,
    },
    ConsensusPolicyMismatch {
        expected: ConsensusPolicyV1,
        seen: ConsensusPolicyV1,
    },
    TermRootMismatch {
        expected: ContentRoot,
        computed: ContentRoot,
    },
    InvalidJudgmentNode {
        detail: String,
        node_id: TermNodeId,
        total_nodes: usize,
    },
    InvalidReductionHint {
        hint_index: usize,
        detail: String,
    },
    AdvisoryExtensionsDisallowed {
        extension_ids: Vec<u32>,
    },
    TooManyExtensions {
        seen: usize,
        limit: usize,
    },
    ExtensionsPayloadTooLarge {
        seen_bytes: usize,
        limit_bytes: usize,
    },
    ClaimedResultRefused {
        claimed: ClaimedRejectionV1,
    },
}

/// Decision from the fast-path bounded certificate verifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FastPathVerificationDecision {
    Verified {
        certificate_digest: Digest,
        declaration_name: Option<Name>,
        judgment: CertificateJudgmentV1,
        claimed_result: ClaimedResultV1,
        steps_consumed: u64,
    },
    Refused(CertificateVerificationRefusal),
}

/// Fast-path bounded certificate verifier.
pub struct CertificateVerifier;

impl CertificateVerifier {
    /// Verify a decoded candidate certificate against the verification context and budget.
    pub fn verify_candidate(
        candidate: &DeclarationCertificateV1,
        context: &VerifierContext,
        budget: &mut VerifierBudget,
    ) -> Outcome<FastPathVerificationDecision> {
        if budget.is_cancelled() {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                "certificate verification cancelled",
            ));
        }

        // 1. Validate epoch binding
        if let Some(expected_epoch) = context.expected_epoch
            && candidate.binding.epoch != expected_epoch
        {
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::StaleEpoch {
                    expected: expected_epoch,
                    seen: candidate.binding.epoch,
                },
            ));
        }

        // 2. Validate mode binding
        if let Some(expected_mode) = context.expected_mode
            && candidate.binding.mode != expected_mode
        {
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::ModeMismatch {
                    expected: expected_mode,
                    seen: candidate.binding.mode,
                },
            ));
        }

        // 3. Validate environment root binding
        if let Some(expected_env) = context.expected_environment_root
            && candidate.binding.environment_root != expected_env
        {
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::EnvironmentRootMismatch {
                    expected: expected_env,
                    seen: candidate.binding.environment_root,
                },
            ));
        }

        // 4. Validate declaration root binding
        if let Some(expected_decl) = context.expected_declaration_root
            && candidate.binding.declaration_root != expected_decl
        {
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::DeclarationRootMismatch {
                    expected: expected_decl,
                    seen: candidate.binding.declaration_root,
                },
            ));
        }

        // 5. Validate build profile binding
        if let Some(expected_profile) = context.expected_build_profile
            && candidate.binding.build_profile != expected_profile
        {
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::BuildProfileMismatch {
                    expected: expected_profile,
                    seen: candidate.binding.build_profile,
                },
            ));
        }

        // 6. Validate consensus policy binding
        if let Some(expected_policy) = context.expected_consensus_policy
            && candidate.binding.consensus_policy != expected_policy
        {
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::ConsensusPolicyMismatch {
                    expected: expected_policy,
                    seen: candidate.binding.consensus_policy,
                },
            ));
        }

        // 7. Validate term root
        let computed_term_root = candidate.term_dag.content_root();
        if computed_term_root != candidate.binding.term_root {
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::TermRootMismatch {
                    expected: candidate.binding.term_root,
                    computed: computed_term_root,
                },
            ));
        }

        // 8. Validate extension limits and policy
        if candidate.extensions.len() > budget.max_extension_count as usize {
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::TooManyExtensions {
                    seen: candidate.extensions.len(),
                    limit: budget.max_extension_count as usize,
                },
            ));
        }
        let total_ext_bytes: usize = candidate.extensions.iter().map(|e| e.payload.len()).sum();
        if total_ext_bytes > budget.max_extension_bytes {
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::ExtensionsPayloadTooLarge {
                    seen_bytes: total_ext_bytes,
                    limit_bytes: budget.max_extension_bytes,
                },
            ));
        }
        if !context.allow_advisory_extensions && !candidate.extensions.is_empty() {
            let extension_ids = candidate.extensions.iter().map(|e| e.id).collect();
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::AdvisoryExtensionsDisallowed { extension_ids },
            ));
        }

        // 9. Validate judgment node references
        let total_nodes = candidate.term_dag.nodes.len();
        match &candidate.judgment {
            CertificateJudgmentV1::CheckDeclaration {
                type_node,
                value_node,
                ..
            } => {
                if type_node.get() as usize >= total_nodes {
                    return Outcome::Complete(FastPathVerificationDecision::Refused(
                        CertificateVerificationRefusal::InvalidJudgmentNode {
                            detail: "type_node out of bounds".to_string(),
                            node_id: *type_node,
                            total_nodes,
                        },
                    ));
                }
                if let Some(val) = value_node
                    && val.get() as usize >= total_nodes
                {
                    return Outcome::Complete(FastPathVerificationDecision::Refused(
                        CertificateVerificationRefusal::InvalidJudgmentNode {
                            detail: "value_node out of bounds".to_string(),
                            node_id: *val,
                            total_nodes,
                        },
                    ));
                }
            }
            CertificateJudgmentV1::InferType {
                term_node,
                inferred_type_node,
            } => {
                if term_node.get() as usize >= total_nodes {
                    return Outcome::Complete(FastPathVerificationDecision::Refused(
                        CertificateVerificationRefusal::InvalidJudgmentNode {
                            detail: "term_node out of bounds".to_string(),
                            node_id: *term_node,
                            total_nodes,
                        },
                    ));
                }
                if inferred_type_node.get() as usize >= total_nodes {
                    return Outcome::Complete(FastPathVerificationDecision::Refused(
                        CertificateVerificationRefusal::InvalidJudgmentNode {
                            detail: "inferred_type_node out of bounds".to_string(),
                            node_id: *inferred_type_node,
                            total_nodes,
                        },
                    ));
                }
            }
            CertificateJudgmentV1::DefinitionalEquality {
                left_node,
                right_node,
                type_node,
            } => {
                if left_node.get() as usize >= total_nodes {
                    return Outcome::Complete(FastPathVerificationDecision::Refused(
                        CertificateVerificationRefusal::InvalidJudgmentNode {
                            detail: "left_node out of bounds".to_string(),
                            node_id: *left_node,
                            total_nodes,
                        },
                    ));
                }
                if right_node.get() as usize >= total_nodes {
                    return Outcome::Complete(FastPathVerificationDecision::Refused(
                        CertificateVerificationRefusal::InvalidJudgmentNode {
                            detail: "right_node out of bounds".to_string(),
                            node_id: *right_node,
                            total_nodes,
                        },
                    ));
                }
                if let Some(tn) = type_node
                    && tn.get() as usize >= total_nodes
                {
                    return Outcome::Complete(FastPathVerificationDecision::Refused(
                        CertificateVerificationRefusal::InvalidJudgmentNode {
                            detail: "type_node out of bounds".to_string(),
                            node_id: *tn,
                            total_nodes,
                        },
                    ));
                }
            }
            CertificateJudgmentV1::WeakHeadNormalForm {
                input_node,
                output_node,
            } => {
                if input_node.get() as usize >= total_nodes {
                    return Outcome::Complete(FastPathVerificationDecision::Refused(
                        CertificateVerificationRefusal::InvalidJudgmentNode {
                            detail: "input_node out of bounds".to_string(),
                            node_id: *input_node,
                            total_nodes,
                        },
                    ));
                }
                if output_node.get() as usize >= total_nodes {
                    return Outcome::Complete(FastPathVerificationDecision::Refused(
                        CertificateVerificationRefusal::InvalidJudgmentNode {
                            detail: "output_node out of bounds".to_string(),
                            node_id: *output_node,
                            total_nodes,
                        },
                    ));
                }
            }
            CertificateJudgmentV1::ValidateInductiveGroup { type_nodes, .. } => {
                for node in type_nodes {
                    if node.get() as usize >= total_nodes {
                        return Outcome::Complete(FastPathVerificationDecision::Refused(
                            CertificateVerificationRefusal::InvalidJudgmentNode {
                                detail: "inductive type_node out of bounds".to_string(),
                                node_id: *node,
                                total_nodes,
                            },
                        ));
                    }
                }
            }
            CertificateJudgmentV1::ValidateQuotientPackage { type_node, .. } => {
                if type_node.get() as usize >= total_nodes {
                    return Outcome::Complete(FastPathVerificationDecision::Refused(
                        CertificateVerificationRefusal::InvalidJudgmentNode {
                            detail: "quotient type_node out of bounds".to_string(),
                            node_id: *type_node,
                            total_nodes,
                        },
                    ));
                }
            }
        }

        // 10. Validate reduction hints
        if let Err(reason) = budget.consume_step(candidate.term_dag.nodes.len() as u64) {
            return Outcome::Inconclusive(reason);
        }

        for (idx, hint) in candidate.reduction_hints.iter().enumerate() {
            if let Err(reason) = budget.consume_step(1) {
                return Outcome::Inconclusive(reason);
            }
            match hint {
                ReductionHintV1::NatOperation {
                    operation,
                    inputs,
                    result,
                } => match evaluate_nat_operation(*operation, &inputs[0], &inputs[1]) {
                    Some(expected_result) => {
                        if expected_result != *result {
                            return Outcome::Complete(FastPathVerificationDecision::Refused(
                                CertificateVerificationRefusal::InvalidReductionHint {
                                    hint_index: idx,
                                    detail: format!(
                                        "nat operation {:?} on inputs gave {:?}, but hint claimed {:?}",
                                        operation, expected_result, result
                                    ),
                                },
                            ));
                        }
                    }
                    None => {
                        return Outcome::Complete(FastPathVerificationDecision::Refused(
                            CertificateVerificationRefusal::InvalidReductionHint {
                                hint_index: idx,
                                detail: format!(
                                    "nat operation {:?} exceeded bounded arithmetic capacity",
                                    operation
                                ),
                            },
                        ));
                    }
                },
                ReductionHintV1::Unfold { declaration } => {
                    if declaration.is_anonymous() {
                        return Outcome::Complete(FastPathVerificationDecision::Refused(
                            CertificateVerificationRefusal::InvalidReductionHint {
                                hint_index: idx,
                                detail: "unfold hint references anonymous declaration".to_string(),
                            },
                        ));
                    }
                }
            }
        }

        // 11. Validate claimed result
        if let ClaimedResultV1::Rejected(rejection) = candidate.claimed_result
            && !context.allow_rejections
        {
            return Outcome::Complete(FastPathVerificationDecision::Refused(
                CertificateVerificationRefusal::ClaimedResultRefused { claimed: rejection },
            ));
        }

        // 12. Compute digest and return verification
        let cert_digest = match candidate.digest() {
            Ok(d) => d,
            Err(refusal) => {
                return Outcome::Complete(FastPathVerificationDecision::Refused(
                    CertificateVerificationRefusal::DecodeRefused(refusal),
                ));
            }
        };

        let declaration_name = match &candidate.judgment {
            CertificateJudgmentV1::CheckDeclaration { name, .. } => Some(name.clone()),
            CertificateJudgmentV1::ValidateQuotientPackage { name, .. } => Some(name.clone()),
            _ => None,
        };

        Outcome::Complete(FastPathVerificationDecision::Verified {
            certificate_digest: cert_digest,
            declaration_name,
            judgment: candidate.judgment.clone(),
            claimed_result: candidate.claimed_result,
            steps_consumed: budget.steps_consumed,
        })
    }

    /// Verify raw certificate bytes against context and budget.
    pub fn verify_bytes(
        bytes: &[u8],
        context: &VerifierContext,
        budget: &mut VerifierBudget,
    ) -> Outcome<FastPathVerificationDecision> {
        if budget.is_cancelled() {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                "certificate verification cancelled",
            ));
        }

        let decode_outcome =
            DeclarationCertificateV1::from_canonical_bytes_budgeted(bytes, budget.decode_budget);
        match decode_outcome {
            Outcome::Complete(Ok(candidate)) => Self::verify_candidate(&candidate, context, budget),
            Outcome::Complete(Err(refusal)) => {
                Outcome::Complete(FastPathVerificationDecision::Refused(
                    CertificateVerificationRefusal::DecodeRefused(refusal),
                ))
            }
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        }
    }
}

// ---------------------------------------------------------------------------
// Multi-precision Nat arithmetic for bounded verification
// ---------------------------------------------------------------------------

pub fn nat_add(a: &NatLit, b: &NatLit) -> NatLit {
    let a_limbs = a.limbs_le();
    let b_limbs = b.limbs_le();
    let max_len = a_limbs.len().max(b_limbs.len());
    let mut result = Vec::with_capacity(max_len + 1);
    let mut carry = 0u64;
    for i in 0..max_len {
        let al = a_limbs.get(i).copied().unwrap_or(0);
        let bl = b_limbs.get(i).copied().unwrap_or(0);
        let (sum1, c1) = al.overflowing_add(bl);
        let (sum2, c2) = sum1.overflowing_add(carry);
        result.push(sum2);
        carry = (c1 as u64) + (c2 as u64);
    }
    if carry > 0 {
        result.push(carry);
    }
    NatLit::from_limbs_le(result)
}

pub fn nat_sub(a: &NatLit, b: &NatLit) -> NatLit {
    if a < b {
        return NatLit::from_u64(0);
    }
    let a_limbs = a.limbs_le();
    let b_limbs = b.limbs_le();
    let mut result = Vec::with_capacity(a_limbs.len());
    let mut borrow = 0u64;
    for (i, &al) in a_limbs.iter().enumerate() {
        let bl = b_limbs.get(i).copied().unwrap_or(0);
        let (diff1, b1) = al.overflowing_sub(bl);
        let (diff2, b2) = diff1.overflowing_sub(borrow);
        result.push(diff2);
        borrow = (b1 as u64) + (b2 as u64);
    }
    NatLit::from_limbs_le(result)
}

pub fn nat_mul(a: &NatLit, b: &NatLit) -> NatLit {
    let a_limbs = a.limbs_le();
    let b_limbs = b.limbs_le();
    if a_limbs.is_empty() || b_limbs.is_empty() {
        return NatLit::from_u64(0);
    }
    let mut result = vec![0u64; a_limbs.len() + b_limbs.len()];
    for (i, &al) in a_limbs.iter().enumerate() {
        let mut carry = 0u64;
        for (j, &bl) in b_limbs.iter().enumerate() {
            let prod = (al as u128) * (bl as u128) + (result[i + j] as u128) + (carry as u128);
            result[i + j] = prod as u64;
            carry = (prod >> 64) as u64;
        }
        let mut k = i + b_limbs.len();
        while carry > 0 {
            let sum = (result[k] as u128) + (carry as u128);
            result[k] = sum as u64;
            carry = (sum >> 64) as u64;
            k += 1;
        }
    }
    NatLit::from_limbs_le(result)
}

fn nat_bit_length(n: &NatLit) -> usize {
    let limbs = n.limbs_le();
    if limbs.is_empty() {
        return 0;
    }
    let top = limbs[limbs.len() - 1];
    (limbs.len() - 1) * 64 + (64 - top.leading_zeros() as usize)
}

fn nat_get_bit(n: &NatLit, bit_idx: usize) -> bool {
    let limb_i = bit_idx / 64;
    let bit_i = bit_idx % 64;
    n.limbs_le()
        .get(limb_i)
        .is_some_and(|&limb| (limb & (1u64 << bit_i)) != 0)
}

fn nat_shift_left_1(n: &NatLit) -> NatLit {
    let limbs = n.limbs_le();
    if limbs.is_empty() {
        return NatLit::from_u64(0);
    }
    let mut out = Vec::with_capacity(limbs.len() + 1);
    let mut carry = 0u64;
    for &l in limbs {
        out.push((l << 1) | carry);
        carry = l >> 63;
    }
    if carry > 0 {
        out.push(carry);
    }
    NatLit::from_limbs_le(out)
}

fn nat_set_bit_0(n: &NatLit) -> NatLit {
    let limbs = n.limbs_le();
    if limbs.is_empty() {
        NatLit::from_u64(1)
    } else {
        let mut out = limbs.to_vec();
        out[0] |= 1;
        NatLit::from_limbs_le(out)
    }
}

pub fn nat_div_rem(a: &NatLit, b: &NatLit) -> (NatLit, NatLit) {
    if b.limbs_le().is_empty() {
        return (NatLit::from_u64(0), a.clone());
    }
    if a < b {
        return (NatLit::from_u64(0), a.clone());
    }
    if b.limbs_le().len() == 1 {
        let divisor = b.limbs_le()[0];
        let mut rem = 0u128;
        let mut quot = vec![0u64; a.limbs_le().len()];
        for i in (0..a.limbs_le().len()).rev() {
            let cur = (rem << 64) | (a.limbs_le()[i] as u128);
            quot[i] = (cur / (divisor as u128)) as u64;
            rem = cur % (divisor as u128);
        }
        return (NatLit::from_limbs_le(quot), NatLit::from_u64(rem as u64));
    }
    let a_bits = nat_bit_length(a);
    let mut rem = NatLit::from_u64(0);
    let mut quot_limbs = vec![0u64; a_bits.div_ceil(64)];
    for bit_idx in (0..a_bits).rev() {
        rem = nat_shift_left_1(&rem);
        if nat_get_bit(a, bit_idx) {
            rem = nat_set_bit_0(&rem);
        }
        if rem >= *b {
            rem = nat_sub(&rem, b);
            let limb_i = bit_idx / 64;
            let bit_i = bit_idx % 64;
            quot_limbs[limb_i] |= 1u64 << bit_i;
        }
    }
    (NatLit::from_limbs_le(quot_limbs), rem)
}

pub fn nat_pow(a: &NatLit, b: &NatLit, max_limbs: usize) -> Option<NatLit> {
    if b.limbs_le().is_empty() {
        return Some(NatLit::from_u64(1));
    }
    if a.limbs_le().is_empty() {
        return Some(NatLit::from_u64(0));
    }
    let mut base = a.clone();
    let mut res = NatLit::from_u64(1);
    let b_bits = nat_bit_length(b);
    for bit_idx in 0..b_bits {
        if nat_get_bit(b, bit_idx) {
            res = nat_mul(&res, &base);
            if res.limbs_le().len() > max_limbs {
                return None;
            }
        }
        if bit_idx + 1 < b_bits {
            base = nat_mul(&base, &base);
            if base.limbs_le().len() > max_limbs {
                return None;
            }
        }
    }
    Some(res)
}

pub fn nat_gcd(mut a: NatLit, mut b: NatLit) -> NatLit {
    while !b.limbs_le().is_empty() {
        let (_, rem) = nat_div_rem(&a, &b);
        a = b;
        b = rem;
    }
    a
}

pub fn nat_land(a: &NatLit, b: &NatLit) -> NatLit {
    let min_len = a.limbs_le().len().min(b.limbs_le().len());
    let mut result = Vec::with_capacity(min_len);
    for i in 0..min_len {
        result.push(a.limbs_le()[i] & b.limbs_le()[i]);
    }
    NatLit::from_limbs_le(result)
}

pub fn nat_lor(a: &NatLit, b: &NatLit) -> NatLit {
    let max_len = a.limbs_le().len().max(b.limbs_le().len());
    let mut result = Vec::with_capacity(max_len);
    for i in 0..max_len {
        let al = a.limbs_le().get(i).copied().unwrap_or(0);
        let bl = b.limbs_le().get(i).copied().unwrap_or(0);
        result.push(al | bl);
    }
    NatLit::from_limbs_le(result)
}

pub fn nat_lxor(a: &NatLit, b: &NatLit) -> NatLit {
    let max_len = a.limbs_le().len().max(b.limbs_le().len());
    let mut result = Vec::with_capacity(max_len);
    for i in 0..max_len {
        let al = a.limbs_le().get(i).copied().unwrap_or(0);
        let bl = b.limbs_le().get(i).copied().unwrap_or(0);
        result.push(al ^ bl);
    }
    NatLit::from_limbs_le(result)
}

pub fn nat_shift_left(a: &NatLit, b: &NatLit, max_limbs: usize) -> Option<NatLit> {
    if a.limbs_le().is_empty() {
        return Some(NatLit::from_u64(0));
    }
    let shift = match b.to_u64() {
        Some(s) if (s / 64) as usize <= max_limbs => s as usize,
        _ => return None,
    };
    let limb_shift = shift / 64;
    let bit_shift = shift % 64;
    let a_limbs = a.limbs_le();
    if a_limbs.len() + limb_shift > max_limbs + 1 {
        return None;
    }
    let mut out = vec![0u64; limb_shift];
    if bit_shift == 0 {
        out.extend_from_slice(a_limbs);
    } else {
        let mut carry = 0u64;
        for &l in a_limbs {
            out.push((l << bit_shift) | carry);
            carry = l >> (64 - bit_shift);
        }
        if carry > 0 {
            out.push(carry);
        }
    }
    if out.len() > max_limbs {
        return None;
    }
    Some(NatLit::from_limbs_le(out))
}

pub fn nat_shift_right(a: &NatLit, b: &NatLit) -> NatLit {
    let a_limbs = a.limbs_le();
    if a_limbs.is_empty() {
        return NatLit::from_u64(0);
    }
    let shift = match b.to_u64() {
        Some(s) => s as usize,
        None => return NatLit::from_u64(0),
    };
    let limb_shift = shift / 64;
    let bit_shift = shift % 64;
    if limb_shift >= a_limbs.len() {
        return NatLit::from_u64(0);
    }
    let slice = &a_limbs[limb_shift..];
    if bit_shift == 0 {
        return NatLit::from_limbs_le(slice.to_vec());
    }
    let mut out = Vec::with_capacity(slice.len());
    for i in 0..slice.len() {
        let cur = slice[i] >> bit_shift;
        let high = slice.get(i + 1).map_or(0, |&next| next << (64 - bit_shift));
        out.push(cur | high);
    }
    NatLit::from_limbs_le(out)
}

pub fn evaluate_nat_operation(
    op: NatOperationV1,
    a: &NatLit,
    b: &NatLit,
) -> Option<NatHintResultV1> {
    const MAX_LIMBS: usize = 4096;
    match op {
        NatOperationV1::Add => Some(NatHintResultV1::Nat(nat_add(a, b))),
        NatOperationV1::Sub => Some(NatHintResultV1::Nat(nat_sub(a, b))),
        NatOperationV1::Mul => Some(NatHintResultV1::Nat(nat_mul(a, b))),
        NatOperationV1::Div => Some(NatHintResultV1::Nat(nat_div_rem(a, b).0)),
        NatOperationV1::Mod => Some(NatHintResultV1::Nat(nat_div_rem(a, b).1)),
        NatOperationV1::Pow => nat_pow(a, b, MAX_LIMBS).map(NatHintResultV1::Nat),
        NatOperationV1::Gcd => Some(NatHintResultV1::Nat(nat_gcd(a.clone(), b.clone()))),
        NatOperationV1::Equal => Some(NatHintResultV1::Bool(a == b)),
        NatOperationV1::LessEqual => Some(NatHintResultV1::Bool(a <= b)),
        NatOperationV1::LessThan => Some(NatHintResultV1::Bool(a < b)),
        NatOperationV1::BitAnd => Some(NatHintResultV1::Nat(nat_land(a, b))),
        NatOperationV1::BitOr => Some(NatHintResultV1::Nat(nat_lor(a, b))),
        NatOperationV1::BitXor => Some(NatHintResultV1::Nat(nat_lxor(a, b))),
        NatOperationV1::ShiftLeft => nat_shift_left(a, b, MAX_LIMBS).map(NatHintResultV1::Nat),
        NatOperationV1::ShiftRight => Some(NatHintResultV1::Nat(nat_shift_right(a, b))),
    }
}

// ---------------------------------------------------------------------------
// Governed Recomputation Fallback Framework
// ---------------------------------------------------------------------------

/// Policy governing whether and how recomputation fallback is attempted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FallbackPolicy {
    /// Recomputation is strictly forbidden (air-gapped receipt-only verifier).
    StrictCertificateOnly,
    /// If fast-path verification is refused, attempt governed recomputation with the budget.
    RecomputeIfRefused { recomputation_budget: u64 },
    /// Run both verifier and recomputation engine, ensuring both agree (paranoid consensus).
    ConsensusCrossCheck { recomputation_budget: u64 },
}

/// Final outcome of governed verification with recomputation fallback.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GovernedVerificationOutcome<R, E> {
    /// Fast-path certificate verification succeeded.
    VerifiedFastPath {
        certificate_digest: Digest,
        declaration_name: Option<Name>,
        judgment: CertificateJudgmentV1,
        steps_consumed: u64,
    },
    /// Fast-path was refused, and recomputation succeeded with a verdict.
    RecomputedFallback {
        previous_refusal: CertificateVerificationRefusal,
        verdict: R,
        recomputation_steps_consumed: u64,
    },
    /// Fast-path verified and recomputation agreed (for ConsensusCrossCheck).
    ConsensusVerified {
        certificate_digest: Digest,
        verdict: R,
        total_steps_consumed: u64,
    },
    /// Recomputation was attempted but failed/refused.
    RecomputationFailed {
        certificate_refusal: CertificateVerificationRefusal,
        recomputation_error: E,
    },
    /// Fast-path was refused and no recomputation was permitted by policy.
    RefusedNoFallback {
        refusal: CertificateVerificationRefusal,
    },
    /// Consensus cross-check divergence (fast path and recomputation gave conflicting results).
    ConsensusDivergence {
        certificate_digest: Digest,
        certificate_claimed: ClaimedResultV1,
        recomputation_error: E,
    },
}

/// Governed verification runner that integrates fast-path verifier and recomputation engine.
pub struct GovernedRecomputeVerifier;

impl GovernedRecomputeVerifier {
    /// Run governed certificate verification with recomputation fallback under FL-INV-07 laws.
    pub fn verify_and_govern<R, E, F>(
        certificate_bytes: &[u8],
        context: &VerifierContext,
        verifier_budget: &mut VerifierBudget,
        fallback_policy: FallbackPolicy,
        recompute_fn: F,
    ) -> Outcome<GovernedVerificationOutcome<R, E>>
    where
        F: FnOnce(&Option<Name>, u64) -> Outcome<Result<R, E>>,
        R: PartialEq + Eq,
    {
        if verifier_budget.is_cancelled() {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                "governed verification cancelled",
            ));
        }

        let fast_path =
            CertificateVerifier::verify_bytes(certificate_bytes, context, verifier_budget);
        match fast_path {
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            Outcome::Complete(FastPathVerificationDecision::Verified {
                certificate_digest,
                declaration_name,
                judgment,
                claimed_result,
                steps_consumed,
            }) => match fallback_policy {
                FallbackPolicy::StrictCertificateOnly
                | FallbackPolicy::RecomputeIfRefused { .. } => {
                    Outcome::Complete(GovernedVerificationOutcome::VerifiedFastPath {
                        certificate_digest,
                        declaration_name,
                        judgment,
                        steps_consumed,
                    })
                }
                FallbackPolicy::ConsensusCrossCheck {
                    recomputation_budget,
                } => {
                    let recompute_outcome = recompute_fn(&declaration_name, recomputation_budget);
                    match recompute_outcome {
                        Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                        Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                        Outcome::Complete(Ok(verdict)) => {
                            Outcome::Complete(GovernedVerificationOutcome::ConsensusVerified {
                                certificate_digest,
                                verdict,
                                total_steps_consumed: steps_consumed
                                    .saturating_add(recomputation_budget),
                            })
                        }
                        Outcome::Complete(Err(recomputation_error)) => {
                            Outcome::Complete(GovernedVerificationOutcome::ConsensusDivergence {
                                certificate_digest,
                                certificate_claimed: claimed_result,
                                recomputation_error,
                            })
                        }
                    }
                }
            },
            Outcome::Complete(FastPathVerificationDecision::Refused(refusal)) => {
                match fallback_policy {
                    FallbackPolicy::StrictCertificateOnly => {
                        Outcome::Complete(GovernedVerificationOutcome::RefusedNoFallback {
                            refusal,
                        })
                    }
                    FallbackPolicy::RecomputeIfRefused {
                        recomputation_budget,
                    }
                    | FallbackPolicy::ConsensusCrossCheck {
                        recomputation_budget,
                    } => {
                        let recompute_outcome = recompute_fn(&None, recomputation_budget);
                        match recompute_outcome {
                            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                            Outcome::Complete(Ok(verdict)) => {
                                Outcome::Complete(GovernedVerificationOutcome::RecomputedFallback {
                                    previous_refusal: refusal,
                                    verdict,
                                    recomputation_steps_consumed: recomputation_budget,
                                })
                            }
                            Outcome::Complete(Err(recomputation_error)) => Outcome::Complete(
                                GovernedVerificationOutcome::RecomputationFailed {
                                    certificate_refusal: refusal,
                                    recomputation_error,
                                },
                            ),
                        }
                    }
                }
            }
        }
    }
}
