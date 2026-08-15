//! **fln** — the embeddable library facade (plan §17.2).
//!
//! The first live surfaces are the typed diagnostic return adapter (bead
//! `franken_lean-wlan`) and a bounded, real engine path (bead `franken_lean-7kc`)
//! from a bounded exact Nat/String/Bool definition, checked scalar intrinsics, or first-order application
//! source, or from an already-elaborated definition, through Crucible, the compiler's validated
//! FIR and canonical FLBC, and Golem. The source path is deliberately the
//! implemented grammar subset, not a claim of general Lean elaboration or
//! Prelude support. Already-elaborated axioms, definitions, theorems, opaques,
//! and non-safe mutual definition blocks can also advance an immutable engine
//! snapshot through admission and publication without compiling or executing a
//! body. Embedders can also validate and execute an existing canonical FLBC
//! artifact without reaching into the compiler or VM crates, and inspect or
//! re-derive a real pinned-format `.olean` through the codec's audited reader.
//! Verdict's proof-producing `bv_decide` pipeline is also available through an
//! atomic engine transition whose theorem must survive both Verdict's proof
//! replay/K1 path and the facade's independent-checker council. Lantern's typed
//! LSP diagnostic projection is reachable here as a pure protocol adapter; the
//! long-lived server transport remains a separate, unfinished product surface.

#![forbid(unsafe_code)]

pub use fln_checker::admit::{
    AdmissionBudget as CheckerAdmissionBudget, AdmissionGround as CheckerAdmissionGround,
};
use fln_checker::admit::{BlockVerdict as CheckerBlockVerdict, Verdict as CheckerVerdict};
pub use fln_checker::environment::EnvironmentBudget as CheckerEnvironmentBudget;
use fln_checker::environment::{
    ConstantDeclaration as CheckerConstantDeclaration, ConstantEntry as CheckerConstantEntry,
    ConstantEnvironment as CheckerConstantEnvironment, ConstantKind as CheckerConstantKind,
    ConstantSafety as CheckerConstantSafety, DefinitionBody as CheckerDefinitionBody,
    DefinitionSafety as CheckerDefinitionSafety, EnvironmentOutcome as CheckerEnvironmentOutcome,
    ReducibilityHint as CheckerReducibilityHint,
};
pub use fln_checker::wire::DecodeBudget as CheckerDecodeBudget;
use fln_checker::wire::{
    DecodeOutcome as CheckerDecodeOutcome, WireExpr as CheckerExpr, WireName as CheckerName,
    decode_expr as checker_decode_expr, decode_name as checker_decode_name,
};
pub use fln_comp::fir::LoweringError;
use fln_comp::fir::ValueType;
use fln_comp::flbc::CallableResultOwnership;
pub use fln_comp::flbc::{CodecError, CodecLimits};
use fln_comp::ingress::{
    FunctionBinding, IngressResource, IntrinsicBinding, LambdaBinding, LambdaRecursion,
};
pub use fln_comp::ingress::{IngressError, IngressLimits};
pub use fln_core::diag::{
    DiagnosticChannel, DiagnosticColorPolicy, DiagnosticEpoch, DiagnosticFormat,
    DiagnosticFrontend, DiagnosticOrderPolicy, DiagnosticPathPolicy, ExitClass, ProjectionRefusal,
    ProjectionRequest, ProjectionSnapshot, RelatedSpan, Severity, StructuredDiagnostic,
    StructuredInconclusive, StructuredInternalFault,
};
pub use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
pub use fln_core::level::Level;
pub use fln_core::mode::{
    BuildProfileId, CgsePolicyId, ClosureComponent, ContentRoot, DeterminismClass, EpochId, Mode,
    ReproducibilityProfile, TargetId,
};
pub use fln_core::name::Name;
pub use fln_core::options::KVMap;
pub use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
pub use fln_elab::{
    DefinitionFrontendError, NatDefinitionFrontendError, seed::SeedEnvironmentError,
};
pub use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, OpaqueVal,
    ReducibilityHints, TheoremVal,
};
use fln_env::environment::DeclarationCommitted;
pub use fln_env::environment::{DeclarationBudget, Environment};
pub use fln_env::modules::CancellationProbe;
pub use fln_env::pmap::CollisionBudget;
pub use fln_hash::canon::CanonError as FlbcProductSidecarCodecError;
use fln_hash::canon::{CanonWriter, Canonical};
pub use fln_hash::product::{
    ClosureMaterialV1, FlbcProductSidecarV1, ProductSidecarBuildRefusal, ProductSidecarRefusal,
    StandardProductCoordinatesV1, flbc_product_root,
};
pub use fln_hash::root::LogicalRoot;
pub use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{
    Council, CouncilOutcome, Seat, SeatBounds, SeatOrigin, SeatVerdict, convene,
};
pub use fln_kernel::verdict::{Budget, RejectClass};
pub use fln_olean::artifact::{
    ArtifactByteHash, ArtifactError, ArtifactIdentityPlane, ArtifactLimits, ArtifactMemberInput,
    ArtifactMemberRecord, ArtifactPointer, ArtifactPublication, ArtifactResource,
    ArtifactSemanticHash, ArtifactSetManifest, ArtifactSetRoot, ArtifactStore,
    ArtifactStoreDirectory, AtomicCreateError, AtomicCreateStep, BoundArtifactSet, InjectedIoError,
    PublicationControl, PublicationIoPoint, PublicationPoint, ResolvedArtifactSet,
    SCHEMA_ARTIFACT_SET_MANIFEST, StagedArtifactSet, artifact_byte_hash, artifact_semantic_hash,
    publish_file_atomic, publish_file_atomic_new,
};
use fln_olean::decl::DeclDecoder;
pub use fln_olean::decl::DeclError as OleanDeclarationError;
pub use fln_olean::format::{
    ILEAN_VERSION, OLEAN_ACCEPTED_VERSIONS, PIN_COMMIT as OLEAN_PIN_COMMIT,
    PIN_TAG as OLEAN_PIN_TAG, REGION_ALIGN as OLEAN_REGION_ALIGN,
};
pub use fln_olean::ilean::{
    Ilean, IleanBudget, IleanDeclInfo, IleanError, IleanImport, IleanLocation, IleanRefIdent,
    IleanRefInfo, decode_ilean, encode_ilean,
};
pub use fln_olean::rebuild::RebuildReport as OleanRebuildReport;
use fln_olean::region::OleanView;
pub use fln_olean::region::{
    ModuleDataView as OleanModuleData, ModuleImport as OleanModuleImport, OleanHeader,
    RegionError as OleanRegionError, WalkBudget as OleanWalkBudget, WalkReport as OleanWalkReport,
};
pub use fln_olean::write::{
    EncodedExprRegion as EncodedOleanExprRegion, EncodedModule as EncodedOleanModule,
    ExprWriteReport as OleanExprWriteReport, ModuleWriteInput as OleanModuleWriteInput,
    ModuleWriteReport as OleanModuleWriteReport, OleanWriteHeader, WriteBudget as OleanWriteBudget,
    WriteError as OleanWriteError, WriteResource as OleanWriteResource,
    encode_expr_region as encode_olean_expr_region, encode_module as encode_olean_module,
};
pub use fln_server::LspProjection;
pub use fln_verdict as verdict;
pub use fln_verdict::{
    BitblastSymbol, BoolBinaryOp, BoolExpr, BvBinaryOp, BvComparison, BvDecideCandidate,
    BvDecideCounterexample, BvDecideInconclusive, BvDecideInputAssignment, BvDecideInputValue,
    BvDecideInternalFault, BvDecideLimits, BvDecideRefusal, BvDecideRequest, BvDecideTelemetry,
    BvExpr, BvShiftOp, BvUnaryOp, UnsupportedBvOp,
};
use fln_vm::interpreter::CommandExecutionContext;
pub use fln_vm::interpreter::{
    ExecutionLimits as VmExecutionLimits, ValueKind as VmValueKind, VmExit, nat_decimal,
    value_kind as vm_value_kind,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LibraryProjection {
    pub request: ProjectionRequest,
    pub disposition: ExitClass,
    pub semantic: ProjectionSnapshot,
}

pub fn project_diagnostics(
    request: ProjectionRequest,
    snapshot: &ProjectionSnapshot,
) -> Result<LibraryProjection, ProjectionRefusal> {
    request
        .validated_product_class()
        .map_err(ProjectionRefusal::Mode)?;
    if request.frontend != DiagnosticFrontend::Library {
        return Err(ProjectionRefusal::Frontend {
            expected: DiagnosticFrontend::Library,
            actual: request.frontend,
        });
    }
    if request.format != DiagnosticFormat::Typed {
        return Err(ProjectionRefusal::UnsupportedFormat {
            frontend: request.frontend,
            format: request.format,
        });
    }
    if request.channel != DiagnosticChannel::ReturnValue {
        return Err(ProjectionRefusal::UnsupportedChannel {
            frontend: request.frontend,
            channel: request.channel,
        });
    }
    if request.color != DiagnosticColorPolicy::Never {
        return Err(ProjectionRefusal::UnsupportedColor {
            frontend: request.frontend,
            color: request.color,
        });
    }
    Ok(LibraryProjection {
        request,
        disposition: snapshot.exit_class(),
        semantic: snapshot.clone(),
    })
}

/// Project one typed diagnostic snapshot to canonical LSP notifications.
///
/// This exposes Lantern's existing diagnostic adapter through the embeddable
/// product facade. It is a pure protocol projection, not a long-lived server,
/// transport loop, request parser, or claim that the broader LSP surface is
/// complete. Inconclusive and internal-fault snapshots remain on the distinct
/// `$/lean/diagnosticOutcome` channel defined by `fln-server`.
pub fn project_lsp_diagnostics(
    request: ProjectionRequest,
    snapshot: &ProjectionSnapshot,
) -> Result<LspProjection, ProjectionRefusal> {
    fln_server::project(request, snapshot)
}

/// Independent resource ceilings for canonical FLBC decoding and execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FlbcExecutionLimits {
    pub codec: CodecLimits,
    pub vm: VmExecutionLimits,
}

/// Owned projection of the simple closed values supported by the current
/// source facade.
///
/// A scalar is intentionally not labeled `Nat` here: canonical FLBC can carry
/// other scalar conventions, while the source frontend is what proves its own
/// result type. A nonnegative mpz is projected to exact decimal text without
/// assuming whether its source type was `Nat` or `Int`, so an
/// arbitrary-precision source `Nat` is not narrowed through `usize`. Heap
/// values other than positive mpz and `String` are outside this projection and
/// return `Ok(None)` from [`closed_vm_value`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClosedVmValue {
    Scalar(usize),
    NonnegativeMpz(String),
    String(String),
}

/// A returned runtime value claimed to be a `String` but violated Marrow's
/// public String representation, or a non-returning exit sent to the value
/// projector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClosedVmValueError {
    NonReturningExit,
    InconsistentStringHeader,
    StringMissingTrailingNul,
    StringSizeExceedsBuffer { size: usize, buffer: usize },
    StringPayloadIsNotUtf8,
}

impl fmt::Display for ClosedVmValueError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonReturningExit => {
                formatter.write_str("non-returning VM exit has no closed return value")
            }
            Self::InconsistentStringHeader => {
                formatter.write_str("returned String header is inconsistent")
            }
            Self::StringMissingTrailingNul => {
                formatter.write_str("returned String did not contain its required trailing NUL")
            }
            Self::StringSizeExceedsBuffer { size, buffer } => write!(
                formatter,
                "returned String size {size} exceeded its {buffer}-byte runtime buffer"
            ),
            Self::StringPayloadIsNotUtf8 => {
                formatter.write_str("returned String payload was not UTF-8")
            }
        }
    }
}

impl std::error::Error for ClosedVmValueError {}

/// Copy one returned scalar, nonnegative mpz, or String out of Marrow's runtime
/// representation.
///
/// This is the value-level companion to [`execute_flbc_artifact`]. It keeps
/// embedders from depending on the ABI String header and trailing-NUL rules.
/// Other valid runtime object kinds return `Ok(None)` and remain available via
/// the original [`VmExit`] for callers with a richer domain decoder.
pub fn closed_vm_value(exit: &VmExit) -> Result<Option<ClosedVmValue>, ClosedVmValueError> {
    let VmExit::Returned(returned) = exit else {
        return Err(ClosedVmValueError::NonReturningExit);
    };
    if returned.value.is_scalar() {
        return Ok(Some(ClosedVmValue::Scalar(returned.value.unbox())));
    }
    if vm_value_kind(&returned.value) == VmValueKind::Mpz {
        return Ok(nat_decimal(&returned.value).map(ClosedVmValue::NonnegativeMpz));
    }
    if vm_value_kind(&returned.value) != VmValueKind::String {
        return Ok(None);
    }

    // `string_view` asserts. This door is embedder-facing: a hostile
    // header must be a typed `ClosedVmValueError`, never a process death.
    let Some((size, _, _, bytes)) = returned.value.try_string_view() else {
        return Err(ClosedVmValueError::InconsistentStringHeader);
    };
    let Some(content_size) = size.checked_sub(1) else {
        return Err(ClosedVmValueError::StringMissingTrailingNul);
    };
    if size > bytes.len() {
        return Err(ClosedVmValueError::StringSizeExceedsBuffer {
            size,
            buffer: bytes.len(),
        });
    }
    if bytes.get(content_size) != Some(&0) {
        return Err(ClosedVmValueError::StringMissingTrailingNul);
    }
    let content = std::str::from_utf8(&bytes[..content_size])
        .map_err(|_| ClosedVmValueError::StringPayloadIsNotUtf8)?;
    Ok(Some(ClosedVmValue::String(content.to_owned())))
}

/// Validates and executes one canonical FLBC artifact through Golem.
///
/// Malformed or over-budget bytes are refused before execution. A valid
/// artifact that exhausts a VM resource returns a typed non-answer. This door
/// executes code only: it does not admit declarations, prove compiler
/// provenance, or advance an [`Engine`] snapshot.
pub fn execute_flbc_artifact(
    artifact: &[u8],
    options: &KVMap,
    limits: FlbcExecutionLimits,
) -> Result<Outcome<VmExit>, CodecError> {
    let executable = fln_comp::flbc::decode_canonical(artifact, limits.codec)?;
    Ok(execute_golem_with_options(&executable, options, limits.vm))
}

/// Canonical bytes of one already-built FLBC product sidecar.
pub fn encode_flbc_product_sidecar(sidecar: &FlbcProductSidecarV1) -> Vec<u8> {
    sidecar.to_canonical_bytes()
}

/// Decode and structurally validate one FLBC product sidecar.
pub fn decode_flbc_product_sidecar(
    bytes: &[u8],
) -> Result<FlbcProductSidecarV1, FlbcProductSidecarCodecError> {
    FlbcProductSidecarV1::from_canonical_bytes(bytes)
}

/// Failure to derive the current bounded source runner's standard product closure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceRunSidecarBuildError {
    EmptyExecutionBatch,
    UnsupportedTarget { target: String },
    Closure(ProductSidecarBuildRefusal),
}

impl std::fmt::Display for SourceRunSidecarBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyExecutionBatch => {
                f.write_str("cannot bind a sidecar to an empty execution batch")
            }
            Self::UnsupportedTarget { target } => {
                write!(
                    f,
                    "the source-run product sidecar has no registered target for {target}"
                )
            }
            Self::Closure(refusal) => refusal.fmt(f),
        }
    }
}

/// Failure to bind a sidecar to actual bytes and the current bounded source runner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceRunSidecarVerificationError {
    Codec(FlbcProductSidecarCodecError),
    UnsupportedTarget { target: String },
    Binding(ProductSidecarRefusal),
}

impl std::fmt::Display for SourceRunSidecarVerificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Codec(error) => error.fmt(f),
            Self::UnsupportedTarget { target } => {
                write!(
                    f,
                    "the source-run product sidecar has no registered target for {target}"
                )
            }
            Self::Binding(refusal) => refusal.fmt(f),
        }
    }
}

/// Independent resource ceilings for pinned-format `.olean` inspection.
///
/// The byte ceiling is checked before any parsing or whole-file auditing.
/// Each object budget applies to its named pass rather than being silently
/// shared across passes.
#[derive(Debug, Clone, Copy)]
pub struct OleanDecodeLimits {
    pub max_bytes: usize,
    pub graph: OleanWalkBudget,
    pub module: OleanWalkBudget,
    pub declarations: OleanWalkBudget,
}

impl OleanDecodeLimits {
    /// Construct limits with an explicit whole-artifact ceiling and the
    /// codec's conservative default object budgets.
    pub fn new(max_bytes: usize) -> Self {
        let objects = OleanWalkBudget::default();
        Self {
            max_bytes,
            graph: objects,
            module: objects,
            declarations: objects,
        }
    }
}

/// A fully decoded, by-value view of one pinned-format `.olean` artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedOlean {
    pub header: OleanHeader,
    pub walk: OleanWalkReport,
    pub module: OleanModuleData,
    pub constants: Vec<ConstantInfo>,
    /// Whether the authoritative module-system server and private parts were
    /// loaded in addition to the exported public part.
    pub companion_parts_loaded: bool,
}

/// One non-public compacted region in a module-system `.olean` chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OleanCompanionPart {
    Server,
    Private,
}

impl fmt::Display for OleanCompanionPart {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Server => ".olean.server",
            Self::Private => ".olean.private",
        })
    }
}

/// Typed refusal from the public `.olean` read path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OleanDecodeError {
    ArtifactTooLarge {
        bytes: usize,
        limit: usize,
    },
    UnexpectedCompanionParts,
    CompanionHeaderMismatch {
        part: OleanCompanionPart,
    },
    CompanionRegion {
        part: OleanCompanionPart,
        error: OleanRegionError,
    },
    CompanionDeclaration {
        part: OleanCompanionPart,
        error: OleanDeclarationError,
    },
    Region(OleanRegionError),
    Declaration(OleanDeclarationError),
}

impl fmt::Display for OleanDecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ArtifactTooLarge { bytes, limit } => {
                write!(f, ".olean artifact has {bytes} bytes; limit is {limit}")
            }
            Self::UnexpectedCompanionParts => write!(
                f,
                "standalone .olean artifact must not have module-system companion parts"
            ),
            Self::CompanionHeaderMismatch { part } => write!(
                f,
                "{part} identity fields do not match the exported .olean part"
            ),
            Self::CompanionRegion { part, error } => {
                write!(f, "{part} region: {error}")
            }
            Self::CompanionDeclaration { part, error } => {
                write!(f, "{part} declaration: {error}")
            }
            Self::Region(error) => write!(f, ".olean region: {error}"),
            Self::Declaration(error) => write!(f, ".olean declaration: {error}"),
        }
    }
}

impl std::error::Error for OleanDecodeError {}

impl OleanDecodeError {
    /// Whether this refusal is solely an explicit byte/object budget rather
    /// than malformed input or a companion-chain identity failure.
    pub const fn is_resource_exhaustion(&self) -> bool {
        matches!(
            self,
            Self::ArtifactTooLarge { .. }
                | Self::Region(OleanRegionError::BudgetExhausted { .. })
                | Self::Declaration(OleanDeclarationError::Budget { .. })
                | Self::Declaration(OleanDeclarationError::Region(
                    OleanRegionError::BudgetExhausted { .. }
                ))
                | Self::CompanionRegion {
                    error: OleanRegionError::BudgetExhausted { .. },
                    ..
                }
                | Self::CompanionDeclaration {
                    error: OleanDeclarationError::Budget { .. },
                    ..
                }
                | Self::CompanionDeclaration {
                    error: OleanDeclarationError::Region(OleanRegionError::BudgetExhausted { .. }),
                    ..
                }
        )
    }
}

impl From<OleanRegionError> for OleanDecodeError {
    fn from(error: OleanRegionError) -> Self {
        Self::Region(error)
    }
}

impl From<OleanDeclarationError> for OleanDecodeError {
    fn from(error: OleanDeclarationError) -> Self {
        Self::Declaration(error)
    }
}

/// Typed refusal from the public pinned `.olean` rebuild path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OleanRebuildError {
    ArtifactTooLarge { bytes: usize, limit: usize },
    Region(OleanRegionError),
}

impl fmt::Display for OleanRebuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ArtifactTooLarge { bytes, limit } => {
                write!(f, ".olean artifact has {bytes} bytes; limit is {limit}")
            }
            Self::Region(error) => write!(f, ".olean rebuild: {error}"),
        }
    }
}

impl std::error::Error for OleanRebuildError {}

impl From<OleanRegionError> for OleanRebuildError {
    fn from(error: OleanRegionError) -> Self {
        Self::Region(error)
    }
}

/// Re-derive a pinned `.olean` artifact from its parsed object graph.
///
/// This is the bounded embeddable door over Grimoire's read-to-rebuild lane.
/// It reconstructs every understood structural byte from semantic fields and
/// copies only declared content classes. Callers compare the returned bytes to
/// the input and inspect the accounting report. It is not fresh `.olean`
/// emission and does not resolve imports or kernel-check declarations.
pub fn rebuild_olean_artifact(
    artifact: &[u8],
    max_bytes: usize,
) -> Result<(Vec<u8>, OleanRebuildReport), OleanRebuildError> {
    if artifact.len() > max_bytes {
        return Err(OleanRebuildError::ArtifactTooLarge {
            bytes: artifact.len(),
            limit: max_bytes,
        });
    }
    fln_olean::rebuild::rebuild(artifact).map_err(OleanRebuildError::from)
}

/// Audit and decode one `.olean` produced by the pinned Reference epoch.
///
/// This is the existing Grimoire reader behind the embeddable facade: it
/// validates the entire compacted region through the shared runtime audit,
/// walks the reachable object graph, decodes `ModuleData`, and cross-checks
/// every decoded declaration's stored computed fields. The returned values
/// own their data and do not borrow the artifact.
///
/// This function does not resolve imports, admit or kernel-check declarations,
/// advance an [`Engine`], or write/re-emit `.olean` bytes.
pub fn decode_olean_artifact(
    artifact: &[u8],
    limits: OleanDecodeLimits,
) -> Result<DecodedOlean, OleanDecodeError> {
    if artifact.len() > limits.max_bytes {
        return Err(OleanDecodeError::ArtifactTooLarge {
            bytes: artifact.len(),
            limit: limits.max_bytes,
        });
    }

    let view = OleanView::parse(artifact)?;
    view.shared_audit()?;
    let walk = view.walk(limits.graph)?;
    let module = view.module_data(limits.module)?;
    let constants = DeclDecoder::new(&view, limits.declarations).decode_module_constants()?;

    Ok(DecodedOlean {
        header: view.header.clone(),
        walk,
        module,
        constants,
        companion_parts_loaded: false,
    })
}

/// Audit and decode one complete module-system `.olean` artifact chain.
///
/// The exported part supplies the import graph and public module metadata.
/// The private part supplies the authoritative constant array used by Lean's
/// `import all` path, including definition bodies and private equation-compiler
/// auxiliaries. The server and private regions are parsed in their original
/// compacted address spaces, walked through their dependency-aware object
/// graphs, and declaration-decoded before any result is returned. The shared
/// runtime's full-surface auditor is single-region, so it audits the exported
/// part only; extending that auditor across dependency regions remains a
/// separate integrity obligation. This function does not resolve imports or
/// admit any declaration into an [`Engine`].
pub fn decode_olean_module_artifacts(
    artifact: &[u8],
    server_artifact: &[u8],
    private_artifact: &[u8],
    limits: OleanDecodeLimits,
) -> Result<DecodedOlean, OleanDecodeError> {
    let bytes = artifact
        .len()
        .checked_add(server_artifact.len())
        .and_then(|total| total.checked_add(private_artifact.len()))
        .ok_or(OleanDecodeError::ArtifactTooLarge {
            bytes: usize::MAX,
            limit: limits.max_bytes,
        })?;
    if bytes > limits.max_bytes {
        return Err(OleanDecodeError::ArtifactTooLarge {
            bytes,
            limit: limits.max_bytes,
        });
    }

    let public_view = OleanView::parse(artifact)?;
    public_view.shared_audit()?;
    public_view.walk(limits.graph)?;
    let module = public_view.module_data(limits.module)?;
    if !module.is_module {
        return Err(OleanDecodeError::UnexpectedCompanionParts);
    }
    DeclDecoder::new(&public_view, limits.declarations).decode_module_constants()?;

    let same_identity = |header: &OleanHeader| {
        header.version == public_view.header.version
            && header.flags == public_view.header.flags
            && header.lean_version == public_view.header.lean_version
            && header.githash == public_view.header.githash
    };

    let server_part = OleanCompanionPart::Server;
    let server_view =
        OleanView::parse_with_dependencies(server_artifact, &[artifact]).map_err(|error| {
            OleanDecodeError::CompanionRegion {
                part: server_part,
                error,
            }
        })?;
    if !same_identity(&server_view.header) {
        return Err(OleanDecodeError::CompanionHeaderMismatch { part: server_part });
    }
    server_view
        .walk(limits.graph)
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: server_part,
            error,
        })?;
    server_view
        .module_data(limits.module)
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: server_part,
            error,
        })?;
    DeclDecoder::new(&server_view, limits.declarations)
        .decode_module_constants()
        .map_err(|error| OleanDecodeError::CompanionDeclaration {
            part: server_part,
            error,
        })?;

    let private_part = OleanCompanionPart::Private;
    let private_view =
        OleanView::parse_with_dependencies(private_artifact, &[artifact, server_artifact])
            .map_err(|error| OleanDecodeError::CompanionRegion {
                part: private_part,
                error,
            })?;
    if !same_identity(&private_view.header) {
        return Err(OleanDecodeError::CompanionHeaderMismatch { part: private_part });
    }
    let walk =
        private_view
            .walk(limits.graph)
            .map_err(|error| OleanDecodeError::CompanionRegion {
                part: private_part,
                error,
            })?;
    private_view
        .module_data(limits.module)
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: private_part,
            error,
        })?;
    let constants = DeclDecoder::new(&private_view, limits.declarations)
        .decode_module_constants()
        .map_err(|error| OleanDecodeError::CompanionDeclaration {
            part: private_part,
            error,
        })?;

    Ok(DecodedOlean {
        header: public_view.header.clone(),
        walk,
        module,
        constants,
        companion_parts_loaded: true,
    })
}

/// Independent ceilings for decoding and checking standalone `.olean` input.
///
/// `max_declarations` bounds the planning tables before they are allocated;
/// `max_dependency_presentations` bounds the iterative walk used to recover a
/// deterministic declaration order. The kernel and independent checker retain
/// their own, separate limits in [`EngineAdmissionLimits`].
#[derive(Debug, Clone, Copy)]
pub struct OleanCheckLimits {
    pub decode: OleanDecodeLimits,
    pub admission: EngineAdmissionLimits,
    pub max_modules: usize,
    pub max_total_bytes: usize,
    pub max_declarations: usize,
    pub max_dependency_presentations: usize,
}

impl OleanCheckLimits {
    /// Construct conservative product limits around explicit artifact and
    /// kernel-stack ceilings.
    pub fn new(max_bytes: usize, kernel: Budget) -> Self {
        Self {
            decode: OleanDecodeLimits::new(max_bytes),
            admission: EngineAdmissionLimits::new(kernel),
            max_modules: 100_000,
            max_total_bytes: max_bytes,
            max_declarations: 1_000_000,
            max_dependency_presentations: 100_000_000,
        }
    }
}

/// One declaration whose K1 verdict and independent-checker veto both
/// completed while checking an `.olean`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OleanCheckedDeclaration {
    pub name: Name,
    pub checker: CheckerAgreement,
}

/// Authoritative result of checking every decoded declaration in one
/// standalone `.olean`.
///
/// The returned engine is the only successor. Every error or non-answer
/// exposes no partially advanced snapshot, so checking is atomic from the
/// caller's point of view.
#[derive(Debug)]
pub struct CheckedOlean {
    pub engine: Engine,
    pub decoded: DecodedOlean,
    pub base_logical_root: LogicalRoot,
    pub result_logical_root: LogicalRoot,
    pub declarations: Vec<OleanCheckedDeclaration>,
}

/// Borrowed bytes and their authoritative module name in a closed import set.
#[derive(Debug, Clone, Copy)]
pub struct OleanModuleInput<'a> {
    pub name: &'a Name,
    pub artifact: &'a [u8],
    pub server_artifact: Option<&'a [u8]>,
    pub private_artifact: Option<&'a [u8]>,
}

/// One checked module inside a closed `.olean` import set.
#[derive(Debug)]
pub struct CheckedOleanModule {
    pub name: Name,
    pub decoded: DecodedOlean,
    pub base_logical_root: LogicalRoot,
    pub result_logical_root: LogicalRoot,
    pub declarations: Vec<OleanCheckedDeclaration>,
}

/// Atomic result of checking a closed set of named `.olean` modules.
#[derive(Debug)]
pub struct CheckedOleanSet {
    pub engine: Engine,
    pub base_logical_root: LogicalRoot,
    pub result_logical_root: LogicalRoot,
    pub modules: Vec<CheckedOleanModule>,
}

/// Typed non-success from the `.olean` declaration-checking doors.
///
/// This first production slice intentionally refuses imports, complete
/// inductive/quotient units, and mutual declaration envelopes. Those are not
/// silently inserted as trusted context. Environment extensions are decoded
/// and counted by [`DecodedOlean`] but are not interpreted by this
/// declaration-only operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OleanCheckError {
    Decode(OleanDecodeError),
    EmptyModuleSet,
    ModuleLimit {
        observed: usize,
        limit: usize,
    },
    TotalBytesLimit {
        observed: usize,
        limit: usize,
    },
    MissingCompanionParts {
        module: Option<Name>,
        missing_server: bool,
        missing_private: bool,
    },
    ImportsRequireResolver {
        imports: Vec<Name>,
    },
    DuplicateModule {
        module: Name,
    },
    ModuleDecode {
        module: Name,
        error: OleanDecodeError,
    },
    MissingModuleImports {
        module: Name,
        imports: Vec<Name>,
    },
    ModuleImportCycle {
        modules: Vec<Name>,
    },
    InternalInvariant {
        detail: &'static str,
    },
    DeclarationLimit {
        observed: usize,
        limit: usize,
    },
    DependencyPresentationLimit {
        observed: usize,
        limit: usize,
    },
    AllocationFailure {
        resource: &'static str,
        requested: usize,
    },
    DuplicateDeclaration {
        name: Name,
    },
    UnsupportedDeclaration {
        name: Name,
        kind: &'static str,
    },
    MutualEnvelopeUnsupported {
        name: Name,
        members: Vec<Name>,
    },
    MissingConstants {
        declaration: Name,
        names: Vec<Name>,
    },
    DependencyCycle {
        declarations: Vec<Name>,
    },
    Admission(EngineAdmissionError),
}

impl fmt::Display for OleanCheckError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Decode(error) => error.fmt(formatter),
            Self::EmptyModuleSet => write!(formatter, ".olean module set must not be empty"),
            Self::ModuleLimit { observed, limit } => write!(
                formatter,
                ".olean set contains {observed} modules; planning limit is {limit}"
            ),
            Self::TotalBytesLimit { observed, limit } => write!(
                formatter,
                ".olean set contains {observed} bytes; aggregate limit is {limit}"
            ),
            Self::MissingCompanionParts {
                module,
                missing_server,
                missing_private,
            } => {
                let subject = module.as_ref().map_or_else(
                    || "module-system .olean artifact".to_owned(),
                    |name| format!("module `{}`", name.to_display_string()),
                );
                let missing = match (*missing_server, *missing_private) {
                    (true, true) => ".olean.server and .olean.private",
                    (true, false) => ".olean.server",
                    (false, true) => ".olean.private",
                    (false, false) => "no companion parts",
                };
                write!(formatter, "{subject} is missing {missing}")
            }
            Self::ImportsRequireResolver { imports } => write!(
                formatter,
                "standalone declaration checking cannot resolve imports: {}",
                display_names(imports)
            ),
            Self::DuplicateModule { module } => write!(
                formatter,
                ".olean set repeats module `{}`",
                module.to_display_string()
            ),
            Self::ModuleDecode { module, error } => write!(
                formatter,
                "module `{}` failed to decode: {error}",
                module.to_display_string()
            ),
            Self::MissingModuleImports { module, imports } => write!(
                formatter,
                "module `{}` imports modules absent from the closed set: {}",
                module.to_display_string(),
                display_names(imports)
            ),
            Self::ModuleImportCycle { modules } => write!(
                formatter,
                "module import graph contains a cycle: {}",
                display_names(modules)
            ),
            Self::InternalInvariant { detail } => {
                write!(
                    formatter,
                    "internal .olean checking invariant failed: {detail}"
                )
            }
            Self::DeclarationLimit { observed, limit } => write!(
                formatter,
                ".olean contains {observed} declarations; planning limit is {limit}"
            ),
            Self::DependencyPresentationLimit { observed, limit } => write!(
                formatter,
                ".olean dependency walk reached {observed} expression presentations; limit is {limit}"
            ),
            Self::AllocationFailure {
                resource,
                requested,
            } => write!(
                formatter,
                "could not reserve {requested} entries for {resource}"
            ),
            Self::DuplicateDeclaration { name } => write!(
                formatter,
                ".olean repeats declaration `{}`",
                name.to_display_string()
            ),
            Self::UnsupportedDeclaration { name, kind } => write!(
                formatter,
                "cannot check {kind} `{}` through the independent-checker facade yet",
                name.to_display_string()
            ),
            Self::MutualEnvelopeUnsupported { name, members } => write!(
                formatter,
                "cannot reconstruct the mutual declaration envelope for `{}` with members {}",
                name.to_display_string(),
                display_names(members)
            ),
            Self::MissingConstants { declaration, names } => write!(
                formatter,
                "declaration `{}` references constants absent from the base environment and artifact: {}",
                declaration.to_display_string(),
                display_names(names)
            ),
            Self::DependencyCycle { declarations } => write!(
                formatter,
                "cannot reconstruct declaration units for dependency cycle: {}",
                display_names(declarations)
            ),
            Self::Admission(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for OleanCheckError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Decode(error) => Some(error),
            Self::ModuleDecode { error, .. } => Some(error),
            Self::Admission(error) => Some(error),
            _ => None,
        }
    }
}

impl From<OleanDecodeError> for OleanCheckError {
    fn from(error: OleanDecodeError) -> Self {
        Self::Decode(error)
    }
}

fn display_names(names: &[Name]) -> String {
    names
        .iter()
        .map(Name::to_display_string)
        .collect::<Vec<_>>()
        .join(", ")
}

fn checked_olean_declaration(info: &ConstantInfo) -> Result<Declaration, OleanCheckError> {
    let name = info.name().clone();
    match info {
        ConstantInfo::Axiom(value) => Ok(Declaration::Axiom(value.clone())),
        ConstantInfo::Defn(value) => {
            if value.all.len() > 1 {
                return Err(OleanCheckError::MutualEnvelopeUnsupported {
                    name,
                    members: value.all.clone(),
                });
            }
            Ok(Declaration::Defn(value.clone()))
        }
        ConstantInfo::Thm(value) => {
            if value.all.len() > 1 {
                return Err(OleanCheckError::MutualEnvelopeUnsupported {
                    name,
                    members: value.all.clone(),
                });
            }
            Ok(Declaration::Thm(value.clone()))
        }
        ConstantInfo::Opaque(value) => {
            if value.all.len() > 1 {
                return Err(OleanCheckError::MutualEnvelopeUnsupported {
                    name,
                    members: value.all.clone(),
                });
            }
            Ok(Declaration::Opaque(value.clone()))
        }
        ConstantInfo::Quot(_)
        | ConstantInfo::Induct(_)
        | ConstantInfo::Ctor(_)
        | ConstantInfo::Rec(_) => Err(OleanCheckError::UnsupportedDeclaration {
            name,
            kind: info.kind_name(),
        }),
    }
}

fn collect_olean_dependencies(
    expression: &Expr,
    names: &mut BTreeSet<Name>,
    presentations: &mut usize,
    limit: usize,
) -> Result<(), OleanCheckError> {
    use fln_core::expr::ExprNode;

    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| OleanCheckError::AllocationFailure {
            resource: ".olean dependency worklist",
            requested: 1,
        })?;
    pending.push(expression);
    while let Some(expression) = pending.pop() {
        *presentations = presentations.saturating_add(1);
        if *presentations > limit {
            return Err(OleanCheckError::DependencyPresentationLimit {
                observed: *presentations,
                limit,
            });
        }
        match expression.node() {
            ExprNode::Const { name, .. } => {
                names.insert(name.clone());
            }
            ExprNode::App { f, a } => {
                pending
                    .try_reserve(2)
                    .map_err(|_| OleanCheckError::AllocationFailure {
                        resource: ".olean dependency worklist",
                        requested: pending.len().saturating_add(2),
                    })?;
                pending.push(a);
                pending.push(f);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending
                    .try_reserve(2)
                    .map_err(|_| OleanCheckError::AllocationFailure {
                        resource: ".olean dependency worklist",
                        requested: pending.len().saturating_add(2),
                    })?;
                pending.push(body);
                pending.push(binder_type);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending
                    .try_reserve(3)
                    .map_err(|_| OleanCheckError::AllocationFailure {
                        resource: ".olean dependency worklist",
                        requested: pending.len().saturating_add(3),
                    })?;
                pending.push(body);
                pending.push(value);
                pending.push(type_);
            }
            ExprNode::MData { expr, .. } => pending.push(expr),
            ExprNode::Proj {
                struct_name, expr, ..
            } => {
                names.insert(struct_name.clone());
                pending.push(expr);
            }
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    Ok(())
}

fn olean_dependencies(
    info: &ConstantInfo,
    presentations: &mut usize,
    limit: usize,
) -> Result<BTreeSet<Name>, OleanCheckError> {
    let mut names = BTreeSet::new();
    collect_olean_dependencies(&info.constant_val().type_, &mut names, presentations, limit)?;
    match info {
        ConstantInfo::Defn(value) => {
            collect_olean_dependencies(&value.value, &mut names, presentations, limit)?
        }
        ConstantInfo::Thm(value) => {
            collect_olean_dependencies(&value.value, &mut names, presentations, limit)?
        }
        ConstantInfo::Opaque(value) => {
            collect_olean_dependencies(&value.value, &mut names, presentations, limit)?
        }
        ConstantInfo::Axiom(_)
        | ConstantInfo::Quot(_)
        | ConstantInfo::Induct(_)
        | ConstantInfo::Ctor(_)
        | ConstantInfo::Rec(_) => {}
    }
    Ok(names)
}

fn plan_olean_declarations(
    base: &Environment,
    constants: &[ConstantInfo],
    limits: OleanCheckLimits,
) -> Result<Vec<usize>, OleanCheckError> {
    if constants.len() > limits.max_declarations {
        return Err(OleanCheckError::DeclarationLimit {
            observed: constants.len(),
            limit: limits.max_declarations,
        });
    }
    let mut owners = BTreeMap::new();
    for (index, info) in constants.iter().enumerate() {
        checked_olean_declaration(info)?;
        if owners.insert(info.name().clone(), index).is_some() {
            return Err(OleanCheckError::DuplicateDeclaration {
                name: info.name().clone(),
            });
        }
    }

    let mut remaining = vec![0_usize; constants.len()];
    let mut dependents = vec![Vec::new(); constants.len()];
    let mut presentations = 0_usize;
    for (index, info) in constants.iter().enumerate() {
        let mut missing = Vec::new();
        for dependency in olean_dependencies(
            info,
            &mut presentations,
            limits.max_dependency_presentations,
        )? {
            match owners.get(&dependency).copied() {
                Some(owner) if owner != index => {
                    remaining[index] = remaining[index].saturating_add(1);
                    dependents[owner].push(index);
                }
                Some(_) => {}
                None if base.find(&dependency).is_some() => {}
                None => missing.push(dependency),
            }
        }
        if !missing.is_empty() {
            return Err(OleanCheckError::MissingConstants {
                declaration: info.name().clone(),
                names: missing,
            });
        }
    }

    let mut ready: BTreeSet<Name> = constants
        .iter()
        .enumerate()
        .filter(|(index, _)| remaining[*index] == 0)
        .map(|(_, info)| info.name().clone())
        .collect();
    let mut order = Vec::new();
    order
        .try_reserve_exact(constants.len())
        .map_err(|_| OleanCheckError::AllocationFailure {
            resource: ".olean declaration order",
            requested: constants.len(),
        })?;
    while let Some(name) = ready.pop_first() {
        let Some(&index) = owners.get(&name) else {
            return Err(OleanCheckError::InternalInvariant {
                detail: "ready declaration has no owner",
            });
        };
        order.push(index);
        let Some(next) = dependents.get(index) else {
            return Err(OleanCheckError::InternalInvariant {
                detail: "declaration owner is outside the dependent table",
            });
        };
        for dependent in next {
            let Some(count) = remaining.get_mut(*dependent) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "dependent declaration is outside the remaining table",
                });
            };
            *count = count
                .checked_sub(1)
                .ok_or(OleanCheckError::InternalInvariant {
                    detail: "declaration dependency count underflowed",
                })?;
            if *count == 0 {
                let Some(constant) = constants.get(*dependent) else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "ready dependent is outside the constant table",
                    });
                };
                ready.insert(constant.name().clone());
            }
        }
    }
    if order.len() != constants.len() {
        let declarations = constants
            .iter()
            .enumerate()
            .filter(|(index, _)| remaining[*index] != 0)
            .map(|(_, info)| info.name().clone())
            .collect();
        return Err(OleanCheckError::DependencyCycle { declarations });
    }
    Ok(order)
}

/// Caller-supplied bounds for one proof-producing bitvector decision and its
/// publication into an immutable [`Engine`] successor.
///
/// Verdict and the facade council have separate kernel budgets because the
/// exact reflected theorem is deliberately checked on both authority paths.
/// [`Self::new`] initializes both from one calibrated native-stack budget;
/// callers can then tighten either phase independently.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineBvDecideLimits {
    pub verdict: BvDecideLimits,
    pub admission: EngineAdmissionLimits,
}

impl EngineBvDecideLimits {
    pub fn new(kernel: Budget) -> Self {
        let mut verdict = BvDecideLimits::default();
        verdict.reflection.kernel = kernel;
        Self {
            verdict,
            admission: EngineAdmissionLimits::new(kernel),
        }
    }
}

/// A completed theorem publication that survived Verdict's proof replay and
/// the embeddable facade's independent-checker council.
#[derive(Debug)]
pub struct EngineBvDecidePublication {
    pub engine: Engine,
    pub verdict: BvDecideCandidate,
    pub base_logical_root: LogicalRoot,
    pub result_logical_root: LogicalRoot,
    pub checker: CheckerAgreement,
}

/// A resource or cancellation stop in either authority path. It is never a
/// negative theorem verdict and carries no successor engine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineBvDecideInconclusive {
    Verdict(BvDecideInconclusive),
    Admission(Inconclusive),
}

/// An invariant failure in either authority path. It carries no successor
/// engine or partially reviewed publication.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineBvDecideInternalFault {
    Verdict(BvDecideInternalFault),
    Admission(InternalFault),
}

/// Disjoint terminal classes for the embeddable `bv_decide` door.
///
/// Only [`Self::Proved`] contains an engine successor. In particular, a SAT
/// counterexample is a completed negative answer about the proposition but has
/// no declaration-publication authority.
#[derive(Debug)]
#[must_use]
pub enum EngineBvDecideOutcome {
    Proved(Box<EngineBvDecidePublication>),
    Counterexample(Box<BvDecideCounterexample>),
    Refused(BvDecideRefusal),
    Inconclusive(EngineBvDecideInconclusive),
    InternalFault(EngineBvDecideInternalFault),
}

impl EngineBvDecideOutcome {
    pub const fn publication(&self) -> Option<&EngineBvDecidePublication> {
        match self {
            Self::Proved(publication) => Some(publication),
            Self::Counterexample(_)
            | Self::Refused(_)
            | Self::Inconclusive(_)
            | Self::InternalFault(_) => None,
        }
    }

    pub const fn counterexample(&self) -> Option<&BvDecideCounterexample> {
        match self {
            Self::Counterexample(counterexample) => Some(counterexample),
            Self::Proved(_) | Self::Refused(_) | Self::Inconclusive(_) | Self::InternalFault(_) => {
                None
            }
        }
    }
}

/// A completed integration refusal. Verdict's domain refusals remain inside
/// [`EngineBvDecideOutcome`]; these variants mean its non-authoritative
/// candidate could not pass the facade publication door.
#[derive(Debug)]
pub enum EngineBvDecideError {
    CandidateTheoremMismatch { expected: Name, actual: Name },
    Admission(EngineAdmissionError),
}

impl fmt::Display for EngineBvDecideError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CandidateTheoremMismatch { expected, actual } => write!(
                formatter,
                "Verdict returned candidate {} for requested theorem {}",
                actual.to_display_string(),
                expected.to_display_string()
            ),
            Self::Admission(error) => {
                write!(
                    formatter,
                    "facade council refused Verdict publication: {error}"
                )
            }
        }
    }
}

impl std::error::Error for EngineBvDecideError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Admission(error) => Some(error),
            Self::CandidateTheoremMismatch { .. } => None,
        }
    }
}

/// One immutable embeddable engine snapshot.
///
/// The live source constructors seed only the opaque type names needed by their
/// bounded frontends: `Nat : Sort 1`, or exact `Nat` plus `String` and the
/// checked Nat arithmetic and `String.append` extern signatures. Neither seed is the
/// real Prelude. Successful admission or execution returns a new `Engine`
/// snapshot containing the published declaration; the receiver is never
/// mutated.
#[derive(Debug, Clone)]
pub struct Engine {
    environment: Environment,
    checker_environment: Option<CheckerConstantEnvironment>,
}

impl Engine {
    /// Attach the embeddable facade to an existing immutable environment
    /// produced by an importer, module transaction, or earlier engine session.
    /// This performs no admission and grants no new authority. The independent
    /// checker projection is constructed lazily on the first admission or
    /// execution because this constructor intentionally accepts no resource
    /// budget.
    pub fn from_environment(environment: Environment) -> Self {
        Self {
            environment,
            checker_environment: None,
        }
    }

    /// Construct the bounded natural-definition engine through the same K1 and
    /// independent-checker council used for ordinary declarations.
    ///
    /// The completed successor retains the checker's one-row projection, so a
    /// later admission need not reconstruct the seed under the candidate's
    /// resource budget. Kernel resource stops remain typed non-answers and an
    /// independent-checker non-answer halts the council without exposing a
    /// successor.
    pub fn with_nat_seed(
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<Self>, EngineAdmissionError> {
        Self::from_environment(Environment::new())
            .admit_declaration(
                fln_elab::seed::nat_seed_declaration(),
                &KVMap::new(),
                limits,
            )
            .map(|outcome| outcome.map_complete(|admission| admission.engine))
    }

    /// Construct the bounded Nat/String/Bool source engine through the ordinary K1
    /// and independent-checker council, retaining every checker projection.
    ///
    /// The three opaque type names check literals, Bool comparison results, and
    /// exact first-order signatures. The remaining declarations are an exact
    /// allowlist of checked Nat operations with scalar-or-mpz results plus
    /// String operations recognized by the compiler's generated-row bridge.
    /// This is not a Prelude substitute and grants no constructors or
    /// eliminators.
    pub fn with_source_seed(
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<Self>, EngineAdmissionError> {
        let mut engine = Self::from_environment(Environment::new());
        for declaration in fln_elab::seed::source_seed_declarations() {
            let admission = engine.admit_declaration(declaration, &KVMap::new(), limits)?;
            match admission {
                Outcome::Complete(admission) => engine = admission.engine,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
        }
        Ok(Outcome::Complete(engine))
    }

    /// The immutable environment snapshot against which the next declaration
    /// will be checked.
    pub fn environment(&self) -> &Environment {
        &self.environment
    }

    /// The deterministic identity of this snapshot under the caller's exact
    /// elaboration-relevant options.
    pub fn logical_root(&self, options: &KVMap) -> LogicalRoot {
        self.environment.logical_root(options)
    }

    /// Prove or refute one supported Boolean/bitvector proposition through
    /// Verdict, then expose a successor engine only after the exact reflected
    /// theorem completes the facade's independent-checker council.
    ///
    /// Verdict first bitblasts the negated proposition, deterministically solves
    /// it, independently replays an UNSAT proof, and asks K1 to check a candidate
    /// without publishing it. The facade then moves that exact theorem through
    /// [`Self::admit_declaration`]. The independent-checker council is therefore
    /// the only environment publication door.
    pub fn decide_bv(
        &self,
        request: BvDecideRequest,
        options: &KVMap,
        limits: EngineBvDecideLimits,
    ) -> Result<EngineBvDecideOutcome, EngineBvDecideError> {
        self.decide_bv_with_cancel(request, options, limits, None)
    }

    /// Cancellation-aware form of [`Self::decide_bv`]. Cancellation is sampled
    /// throughout Verdict and once more before the facade council. The existing
    /// admission council itself remains bounded but is not yet cooperatively
    /// cancellable.
    pub fn decide_bv_with_cancel(
        &self,
        request: BvDecideRequest,
        options: &KVMap,
        limits: EngineBvDecideLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<EngineBvDecideOutcome, EngineBvDecideError> {
        let theorem_name = request.theorem_name().clone();
        let verdict = fln_verdict::bv_decide_with_cancel(
            &self.environment,
            request,
            limits.verdict,
            cancellation,
        );
        let candidate = match verdict {
            fln_verdict::BvDecideOutcome::Candidate(candidate) => candidate,
            fln_verdict::BvDecideOutcome::Counterexample(counterexample) => {
                return Ok(EngineBvDecideOutcome::Counterexample(counterexample));
            }
            fln_verdict::BvDecideOutcome::Refused(refusal) => {
                return Ok(EngineBvDecideOutcome::Refused(refusal));
            }
            fln_verdict::BvDecideOutcome::Inconclusive(inconclusive) => {
                return Ok(EngineBvDecideOutcome::Inconclusive(
                    EngineBvDecideInconclusive::Verdict(inconclusive),
                ));
            }
            fln_verdict::BvDecideOutcome::InternalFault(fault) => {
                return Ok(EngineBvDecideOutcome::InternalFault(
                    EngineBvDecideInternalFault::Verdict(fault),
                ));
            }
        };

        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(EngineBvDecideOutcome::Inconclusive(
                EngineBvDecideInconclusive::Admission(Inconclusive::cancelled(
                    "engine-bv-decide/before-facade-council",
                )),
            ));
        }

        let theorem = candidate.reflection().theorem().clone();
        if theorem.base.name != theorem_name {
            return Err(EngineBvDecideError::CandidateTheoremMismatch {
                expected: theorem_name,
                actual: theorem.base.name,
            });
        }
        let admission = self
            .admit_declaration(Declaration::Thm(theorem), options, limits.admission)
            .map_err(EngineBvDecideError::Admission)?;
        let admission = match admission {
            Outcome::Complete(admission) => admission,
            Outcome::Inconclusive(inconclusive) => {
                return Ok(EngineBvDecideOutcome::Inconclusive(
                    EngineBvDecideInconclusive::Admission(inconclusive),
                ));
            }
            Outcome::InternalFault(fault) => {
                return Ok(EngineBvDecideOutcome::InternalFault(
                    EngineBvDecideInternalFault::Admission(fault),
                ));
            }
        };
        Ok(EngineBvDecideOutcome::Proved(Box::new(
            EngineBvDecidePublication {
                engine: admission.engine,
                verdict: *candidate,
                base_logical_root: admission.base_logical_root,
                result_logical_root: admission.result_logical_root,
                checker: admission.checker,
            },
        )))
    }

    /// Decode and atomically check every declaration in one standalone
    /// pinned-format `.olean`.
    ///
    /// The declaration array is not trusted to be dependency-ordered. This
    /// method derives a stable Kahn order from exact constant references, then
    /// sends every declaration through the same K1-plus-independent-checker
    /// council as [`Self::admit_declaration`]. The artifact must be import-free:
    /// resolving module names to exact predecessor environments belongs to the
    /// module loader, and treating unresolved imports as axioms would violate
    /// the Oracle-Only and single-authority laws.
    ///
    /// A completed result means all decoded declarations were checked and the
    /// returned engine contains all of them. It does not mean environment
    /// extension payloads were interpreted or that K2/receipt/release gates
    /// were satisfied. Module-system artifacts are refused here because this
    /// convenience door has no companion-part arguments; use
    /// [`Self::check_olean_artifact_parts`] for those.
    pub fn check_olean_artifact(
        &self,
        artifact: &[u8],
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<CheckedOlean>, OleanCheckError> {
        self.check_olean_artifact_parts(artifact, None, None, options, limits)
    }

    /// Decode and atomically check one standalone or complete module-system
    /// pinned-format `.olean` artifact.
    ///
    /// Module-system inputs must provide both companion parts. Refusing an
    /// incomplete chain is load-bearing: checking only the exported part would
    /// turn stripped definitions into axioms and omit private auxiliaries.
    pub fn check_olean_artifact_parts(
        &self,
        artifact: &[u8],
        server_artifact: Option<&[u8]>,
        private_artifact: Option<&[u8]>,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<CheckedOlean>, OleanCheckError> {
        let decoded = match (server_artifact, private_artifact) {
            (Some(server), Some(private)) => {
                decode_olean_module_artifacts(artifact, server, private, limits.decode)?
            }
            (server, private) => {
                let decoded = decode_olean_artifact(artifact, limits.decode)?;
                if decoded.module.is_module {
                    return Err(OleanCheckError::MissingCompanionParts {
                        module: None,
                        missing_server: server.is_none(),
                        missing_private: private.is_none(),
                    });
                }
                if server.is_some() || private.is_some() {
                    return Err(OleanCheckError::Decode(
                        OleanDecodeError::UnexpectedCompanionParts,
                    ));
                }
                decoded
            }
        };
        if !decoded.module.imports.is_empty() {
            return Err(OleanCheckError::ImportsRequireResolver {
                imports: decoded
                    .module
                    .imports
                    .iter()
                    .map(|import| import.module.clone())
                    .collect(),
            });
        }
        self.check_decoded_olean(decoded, options, limits)
    }

    /// Decode and atomically check a closed set of named `.olean` modules.
    ///
    /// Every direct import must name another input row. Modules are checked in
    /// a deterministic import-topological order; declarations within each
    /// module are independently dependency-sorted. Nothing from a missing
    /// import is synthesized, and no prefix engine is returned on a later
    /// failure or non-answer.
    pub fn check_olean_modules(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<CheckedOleanSet>, OleanCheckError> {
        if modules.is_empty() {
            return Err(OleanCheckError::EmptyModuleSet);
        }
        if modules.len() > limits.max_modules {
            return Err(OleanCheckError::ModuleLimit {
                observed: modules.len(),
                limit: limits.max_modules,
            });
        }
        let mut total_bytes = 0_usize;
        let mut owners = BTreeMap::new();
        for (index, module) in modules.iter().enumerate() {
            for artifact in [
                Some(module.artifact),
                module.server_artifact,
                module.private_artifact,
            ]
            .into_iter()
            .flatten()
            {
                total_bytes = total_bytes.checked_add(artifact.len()).ok_or(
                    OleanCheckError::TotalBytesLimit {
                        observed: usize::MAX,
                        limit: limits.max_total_bytes,
                    },
                )?;
            }
            if total_bytes > limits.max_total_bytes {
                return Err(OleanCheckError::TotalBytesLimit {
                    observed: total_bytes,
                    limit: limits.max_total_bytes,
                });
            }
            if owners.insert(module.name.clone(), index).is_some() {
                return Err(OleanCheckError::DuplicateModule {
                    module: module.name.clone(),
                });
            }
        }

        let mut decoded = Vec::new();
        decoded.try_reserve_exact(modules.len()).map_err(|_| {
            OleanCheckError::AllocationFailure {
                resource: ".olean decoded module set",
                requested: modules.len(),
            }
        })?;
        for module in modules {
            let artifact = match (module.server_artifact, module.private_artifact) {
                (Some(server), Some(private)) => {
                    decode_olean_module_artifacts(module.artifact, server, private, limits.decode)
                }
                (server, private) => {
                    let decoded = decode_olean_artifact(module.artifact, limits.decode);
                    match decoded {
                        Ok(decoded) if decoded.module.is_module => {
                            return Err(OleanCheckError::MissingCompanionParts {
                                module: Some(module.name.clone()),
                                missing_server: server.is_none(),
                                missing_private: private.is_none(),
                            });
                        }
                        Ok(_) if server.is_some() || private.is_some() => {
                            return Err(OleanCheckError::Decode(
                                OleanDecodeError::UnexpectedCompanionParts,
                            ));
                        }
                        other => other,
                    }
                }
            }
            .map_err(|error| OleanCheckError::ModuleDecode {
                module: module.name.clone(),
                error,
            })?;
            decoded.push(Some((module.name.clone(), artifact)));
        }

        let mut remaining = vec![0_usize; modules.len()];
        let mut dependents = vec![Vec::new(); modules.len()];
        for (index, module) in decoded.iter().enumerate() {
            let Some((_, artifact)) = module.as_ref() else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "decoded module disappeared before planning",
                });
            };
            let mut missing = BTreeSet::new();
            let mut dependencies = BTreeSet::new();
            for import in &artifact.module.imports {
                match owners.get(&import.module).copied() {
                    Some(owner) if owner != index => {
                        dependencies.insert(owner);
                    }
                    Some(_) => {
                        dependencies.insert(index);
                    }
                    None => {
                        missing.insert(import.module.clone());
                    }
                }
            }
            if !missing.is_empty() {
                let Some(input) = modules.get(index) else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "decoded module has no corresponding input",
                    });
                };
                return Err(OleanCheckError::MissingModuleImports {
                    module: input.name.clone(),
                    imports: missing.into_iter().collect(),
                });
            }
            remaining[index] = dependencies.len();
            for dependency in dependencies {
                dependents[dependency].push(index);
            }
        }

        let mut ready: BTreeSet<Name> = modules
            .iter()
            .enumerate()
            .filter(|(index, _)| remaining[*index] == 0)
            .map(|(_, module)| module.name.clone())
            .collect();
        let mut order = Vec::new();
        order
            .try_reserve_exact(modules.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean module order",
                requested: modules.len(),
            })?;
        while let Some(name) = ready.pop_first() {
            let Some(&index) = owners.get(&name) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "ready module has no owner",
                });
            };
            order.push(index);
            let Some(next) = dependents.get(index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "module owner is outside the dependent table",
                });
            };
            for dependent in next {
                let Some(count) = remaining.get_mut(*dependent) else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "dependent module is outside the remaining table",
                    });
                };
                *count = count
                    .checked_sub(1)
                    .ok_or(OleanCheckError::InternalInvariant {
                        detail: "module dependency count underflowed",
                    })?;
                if *count == 0 {
                    let Some(module) = modules.get(*dependent) else {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "ready dependent is outside the module table",
                        });
                    };
                    ready.insert(module.name.clone());
                }
            }
        }
        if order.len() != modules.len() {
            return Err(OleanCheckError::ModuleImportCycle {
                modules: modules
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| remaining[*index] != 0)
                    .map(|(_, module)| module.name.clone())
                    .collect(),
            });
        }

        let base_logical_root = self.logical_root(options);
        let mut engine = self.clone();
        let mut checked_modules = Vec::new();
        checked_modules
            .try_reserve_exact(modules.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean checked module records",
                requested: modules.len(),
            })?;
        for index in order {
            let Some(slot) = decoded.get_mut(index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "topological module is outside the decoded table",
                });
            };
            let Some((name, artifact)) = slot.take() else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "topological module was consumed more than once",
                });
            };
            let checked = match engine.check_decoded_olean(artifact, options, limits)? {
                Outcome::Complete(checked) => checked,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            engine = checked.engine;
            checked_modules.push(CheckedOleanModule {
                name,
                decoded: checked.decoded,
                base_logical_root: checked.base_logical_root,
                result_logical_root: checked.result_logical_root,
                declarations: checked.declarations,
            });
        }
        let result_logical_root = engine.logical_root(options);
        Ok(Outcome::Complete(CheckedOleanSet {
            engine,
            base_logical_root,
            result_logical_root,
            modules: checked_modules,
        }))
    }

    fn check_decoded_olean(
        &self,
        decoded: DecodedOlean,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<CheckedOlean>, OleanCheckError> {
        let order = plan_olean_declarations(&self.environment, &decoded.constants, limits)?;
        let base_logical_root = self.logical_root(options);
        if order.is_empty() {
            return Ok(Outcome::Complete(CheckedOlean {
                engine: self.clone(),
                decoded,
                base_logical_root,
                result_logical_root: base_logical_root,
                declarations: Vec::new(),
            }));
        }

        let mut declarations = Vec::new();
        declarations.try_reserve_exact(order.len()).map_err(|_| {
            OleanCheckError::AllocationFailure {
                resource: ".olean declaration batch",
                requested: order.len(),
            }
        })?;
        for index in &order {
            let Some(info) = decoded.constants.get(*index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "planned declaration is outside the decoded constant table",
                });
            };
            declarations.push(checked_olean_declaration(info)?);
        }
        let admitted = match self
            .admit_declarations(&declarations, options, limits.admission)
            .map_err(OleanCheckError::Admission)?
        {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut checked = Vec::new();
        checked
            .try_reserve_exact(admitted.admissions.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean completed declaration records",
                requested: admitted.admissions.len(),
            })?;
        for (constant_index, admission) in order.iter().zip(&admitted.admissions) {
            let Some(info) = decoded.constants.get(*constant_index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "completed declaration is outside the decoded constant table",
                });
            };
            checked.push(OleanCheckedDeclaration {
                name: info.name().clone(),
                checker: admission.checker,
            });
        }
        if checked.len() != order.len() {
            return Err(OleanCheckError::InternalInvariant {
                detail: "admission result count differs from the declaration plan",
            });
        }
        Ok(Outcome::Complete(CheckedOlean {
            engine: admitted.engine,
            decoded,
            base_logical_root: admitted.base_logical_root,
            result_logical_root: admitted.result_logical_root,
            declarations: checked,
        }))
    }

    /// Admit and publish one declaration without compiling or executing it.
    ///
    /// This is the environment-building counterpart to
    /// [`Self::execute_definition`]. It currently accepts the declaration kinds
    /// on which both K1 and the independent checker can issue a completed
    /// verdict: axioms, definitions, theorems, opaques, and non-safe mutual
    /// definition blocks. Inductives and quotient initialization remain
    /// explicit refusals until the independent checker can represent and decide
    /// their complete input.
    ///
    /// Success returns a new immutable engine snapshot. A rejection,
    /// independent-checker non-answer, duplicate, resource stop, or internal
    /// fault exposes no successor and leaves `self` unchanged.
    pub fn admit_declaration(
        &self,
        declaration: Declaration,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationAdmission>, EngineAdmissionError> {
        if !matches!(
            declaration,
            Declaration::Axiom(_)
                | Declaration::Defn(_)
                | Declaration::Thm(_)
                | Declaration::Opaque(_)
                | Declaration::Mutual(_)
        ) {
            return Err(EngineAdmissionError::UnsupportedDeclaration {
                kind: declaration_kind(&declaration),
            });
        }

        let base_logical_root = self.logical_root(options);
        let checker_review = review_with_independent_checker(
            &self.environment,
            self.checker_environment.as_ref(),
            &declaration,
            limits.checker,
        );
        let admitted = match admit(&self.environment, declaration.clone(), limits.kernel) {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let checked = match convene(&checker_review.council, admitted) {
            CouncilOutcome::Agreed(checked) => checked,
            CouncilOutcome::KernelRejected { class, message, .. } => {
                return Err(EngineAdmissionError::KernelRejected { class, message });
            }
            CouncilOutcome::Halted(halt) => {
                return Err(EngineAdmissionError::CouncilHalted {
                    summary: halt.summary(),
                });
            }
        };
        let checker =
            checker_review
                .agreement
                .ok_or_else(|| EngineAdmissionError::CheckerBridge {
                    detail: "the checker council agreed without an admission record".to_owned(),
                })?;
        let checker_environment = checker_review.successor_environment.ok_or_else(|| {
            EngineAdmissionError::CheckerBridge {
                detail: "the checker council agreed without a retained successor environment"
                    .to_owned(),
            }
        })?;
        let expects_block = matches!(declaration, Declaration::Mutual(_));
        let environment = match checked.publish(limits.declaration, limits.collisions, None) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                publication,
            ))) => {
                if expects_block {
                    return Err(EngineAdmissionError::UnexpectedPublication {
                        detail: "a block declaration published as one constant",
                    });
                }
                publication.environment
            }
            Outcome::Complete(Published::Committed(DeclarationCommitted::DuplicateName {
                name,
            }))
            | Outcome::Complete(Published::DuplicateName { name }) => {
                return Err(EngineAdmissionError::DuplicateName { name });
            }
            Outcome::Complete(Published::BlockCommitted(publication)) => {
                if !expects_block {
                    return Err(EngineAdmissionError::UnexpectedPublication {
                        detail: "a non-block declaration published as a block",
                    });
                }
                publication.environment
            }
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let result_logical_root = environment.logical_root(options);

        Ok(Outcome::Complete(DeclarationAdmission {
            engine: Engine {
                environment,
                checker_environment: Some(checker_environment),
            },
            declaration,
            base_logical_root,
            result_logical_root,
            checker,
        }))
    }

    /// Admit and publish a nonempty declaration sequence atomically.
    ///
    /// Each declaration observes the immutable successor of its predecessor.
    /// Any error or non-answer returns no batch successor, so callers can retain
    /// only the original engine. Completed results carry every root transition
    /// for direct continuity checks.
    pub fn admit_declarations(
        &self,
        declarations: &[Declaration],
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineAdmissionError> {
        if declarations.is_empty() {
            return Err(EngineAdmissionError::EmptyBatch);
        }
        let mut admissions = Vec::new();
        admissions
            .try_reserve_exact(declarations.len())
            .map_err(|_| EngineAdmissionError::AllocationFailure {
                resource: "declaration batch results",
                requested: declarations.len(),
            })?;
        let base_logical_root = self.logical_root(options);
        let mut engine = self.clone();
        for (index, declaration) in declarations.iter().cloned().enumerate() {
            let admission = match engine.admit_declaration(declaration, options, limits) {
                Ok(Outcome::Complete(admission)) => admission,
                Ok(Outcome::Inconclusive(reason)) => return Ok(Outcome::Inconclusive(reason)),
                Ok(Outcome::InternalFault(fault)) => return Ok(Outcome::InternalFault(fault)),
                Err(error) => {
                    return Err(EngineAdmissionError::BatchDeclaration {
                        index,
                        error: Box::new(error),
                    });
                }
            };
            engine = admission.engine.clone();
            admissions.push(admission);
        }
        let result_logical_root = engine.logical_root(options);
        Ok(Outcome::Complete(DeclarationBatchAdmission {
            engine,
            base_logical_root,
            result_logical_root,
            admissions,
        }))
    }

    /// Parse, elaborate, admit, publish, compile, canonically encode/decode,
    /// and execute one bounded Nat-valued definition command. The declaration
    /// may have explicit `Nat` parameters; its body may be a natural literal, a
    /// reference, or a saturated identifier-headed application of those atom
    /// forms, optionally under a chain of non-recursive local `Nat` lets.
    ///
    /// The independent `fln-checker` must agree with K1 before the publication
    /// capability survives the council. A disagreement or checker non-answer
    /// halts publication. Kernel and VM non-answers remain
    /// [`Outcome::Inconclusive`] or [`Outcome::InternalFault`]; they are never
    /// collapsed into rejection.
    pub fn execute_nat_definition(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionExecution>, EngineExecutionError> {
        let parsed = fln_parse::parse_nat_definition(source)
            .map_err(NatDefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        self.execute_parsed_nat_definition(parsed, options, limits)
    }

    fn execute_parsed_nat_definition(
        &self,
        parsed: fln_parse::ParsedNatDefinition,
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionExecution>, EngineExecutionError> {
        let declaration =
            fln_elab::elaborate_nat_definition_in(parsed.syntax(), self.environment())
                .map_err(NatDefinitionFrontendError::Elaborate)
                .map_err(EngineExecutionError::Frontend)?;
        self.execute_definition(declaration, options, limits)
    }

    /// Parse, elaborate, admit, publish, compile, canonically encode/decode,
    /// and execute one definition in the bounded exact Nat/String/Bool source slice.
    ///
    /// Every declaration still crosses K1 and the retained independent checker;
    /// accepting String syntax does not add a second publication authority.
    pub fn execute_source_definition(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionExecution>, EngineExecutionError> {
        let parsed = fln_parse::parse_definition(source)
            .map_err(DefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        self.execute_parsed_source_definition(parsed, options, limits)
    }

    fn execute_parsed_source_definition(
        &self,
        parsed: fln_parse::ParsedDefinition,
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionExecution>, EngineExecutionError> {
        let declaration = fln_elab::elaborate_definition_in(parsed.syntax(), self.environment())
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        self.execute_definition(declaration, options, limits)
    }

    /// Execute the bounded Nat definitions in a nonempty sequence of source
    /// files atomically.
    ///
    /// Each file may contain one or more commands. The seed parser partitions
    /// only on real `def` tokens, then parses every slice through its existing
    /// single-command authority. Commands observe the immutable successor of the
    /// command before them across file boundaries. A refusal or non-answer at any
    /// flattened command index returns no batch successor, so the caller can only
    /// retain the original `self`. Completed per-command roots remain in the
    /// successful result and form a checkable continuity chain.
    pub fn execute_nat_definitions(
        &self,
        sources: &[&[u8]],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionBatchExecution>, EngineExecutionError> {
        let mut commands = Vec::new();
        for source in sources {
            let partitioned =
                fln_parse::partition_nat_definition_commands(source).map_err(|error| {
                    EngineExecutionError::BatchCommand {
                        index: commands.len(),
                        error: Box::new(EngineExecutionError::Frontend(
                            NatDefinitionFrontendError::Parse(error),
                        )),
                    }
                })?;
            let requested = commands.len().checked_add(partitioned.len()).ok_or(
                EngineExecutionError::AllocationFailure {
                    resource: "definition command table",
                    requested: usize::MAX,
                },
            )?;
            commands.try_reserve(partitioned.len()).map_err(|_| {
                EngineExecutionError::AllocationFailure {
                    resource: "definition command table",
                    requested,
                }
            })?;
            commands.extend(partitioned);
        }
        self.execute_batch(commands.len(), options, |engine, index| {
            let (original_offset, source) = commands[index];
            let parsed = fln_parse::parse_nat_definition(source)
                .map_err(|error| error.with_original_offset(original_offset))
                .map_err(NatDefinitionFrontendError::Parse)
                .map_err(EngineExecutionError::Frontend)?;
            engine.execute_parsed_nat_definition(parsed, options, limits)
        })
    }

    /// Execute a nonempty source-file sequence in the bounded exact Nat/String/Bool
    /// grammar atomically. Each command observes the checked successor of the
    /// prior command; any refusal or non-answer exposes no batch successor.
    pub fn execute_source_definitions(
        &self,
        sources: &[&[u8]],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionBatchExecution>, EngineExecutionError> {
        let mut commands = Vec::new();
        for source in sources {
            let partitioned =
                fln_parse::partition_definition_commands(source).map_err(|error| {
                    EngineExecutionError::BatchCommand {
                        index: commands.len(),
                        error: Box::new(EngineExecutionError::Frontend(
                            DefinitionFrontendError::Parse(error),
                        )),
                    }
                })?;
            let requested = commands.len().checked_add(partitioned.len()).ok_or(
                EngineExecutionError::AllocationFailure {
                    resource: "definition command table",
                    requested: usize::MAX,
                },
            )?;
            commands.try_reserve(partitioned.len()).map_err(|_| {
                EngineExecutionError::AllocationFailure {
                    resource: "definition command table",
                    requested,
                }
            })?;
            commands.extend(partitioned);
        }
        self.execute_batch(commands.len(), options, |engine, index| {
            let (original_offset, source) = commands[index];
            let parsed = fln_parse::parse_definition(source)
                .map_err(|error| error.with_original_offset(original_offset))
                .map_err(DefinitionFrontendError::Parse)
                .map_err(EngineExecutionError::Frontend)?;
            engine.execute_parsed_source_definition(parsed, options, limits)
        })
    }

    /// Execute a nonempty sequence of already-elaborated definitions atomically.
    ///
    /// This is the reusable project-sized door over [`Self::execute_definition`]:
    /// each declaration is admitted, published, compiled, and executed against
    /// the preceding immutable successor. A refusal or non-answer exposes no
    /// batch successor, while a completed result carries every root transition
    /// and the final queryable environment.
    pub fn execute_definitions(
        &self,
        declarations: &[Declaration],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionBatchExecution>, EngineExecutionError> {
        self.execute_batch(declarations.len(), options, |engine, index| {
            engine.execute_definition(declarations[index].clone(), options, limits)
        })
    }

    fn execute_batch<F>(
        &self,
        command_count: usize,
        options: &KVMap,
        mut execute: F,
    ) -> Result<Outcome<DefinitionBatchExecution>, EngineExecutionError>
    where
        F: FnMut(&Engine, usize) -> Result<Outcome<DefinitionExecution>, EngineExecutionError>,
    {
        if command_count == 0 {
            return Err(EngineExecutionError::EmptyBatch);
        }
        let mut executions = Vec::new();
        executions.try_reserve_exact(command_count).map_err(|_| {
            EngineExecutionError::AllocationFailure {
                resource: "definition batch results",
                requested: command_count,
            }
        })?;
        let base_logical_root = self.logical_root(options);
        let mut engine = self.clone();
        for index in 0..command_count {
            let execution = match execute(&engine, index) {
                Ok(Outcome::Complete(execution)) => execution,
                Ok(Outcome::Inconclusive(reason)) => return Ok(Outcome::Inconclusive(reason)),
                Ok(Outcome::InternalFault(fault)) => return Ok(Outcome::InternalFault(fault)),
                Err(error) => {
                    return Err(EngineExecutionError::BatchCommand {
                        index,
                        error: Box::new(error),
                    });
                }
            };
            engine = execution.engine.clone();
            executions.push(execution);
        }
        let result_logical_root = engine.logical_root(options);
        Ok(Outcome::Complete(DefinitionBatchExecution {
            engine,
            base_logical_root,
            result_logical_root,
            executions,
        }))
    }

    /// Admit, publish, compile, canonically encode/decode, and execute one
    /// already-elaborated definition.
    ///
    /// This is the reusable engine seam behind [`Self::execute_nat_definition`].
    /// It accepts the compiler's substantially broader implemented closed-
    /// expression subset rather than the seed parser's literal-or-identifier
    /// Nat-term subset.
    /// References to closed, universe-free first-order definitions over exact
    /// `Nat` and `String` parameter/result types are compiled from the types and
    /// bodies already published in the base environment. This is the first
    /// environment-to-compiler catalog bridge; other runtime signatures remain
    /// explicit compiler refusals. Non-definition declarations are explicit
    /// refusals because they have no executable body.
    ///
    /// The independent checker receives a complete checker-owned projection of
    /// the base environment and candidate. Its agreement is a mandatory council
    /// veto seat, never an alternative publication authority. Publication creates
    /// only a local immutable successor until compilation and execution complete,
    /// so a later refusal or non-answer exposes no partially advanced engine.
    /// Golem captures the pin-defined `maxHeartbeats` value from `options` at
    /// command entry; its own instruction and stack ceilings remain the separate
    /// explicit [`EngineExecutionLimits`] policy.
    pub fn execute_definition(
        &self,
        declaration: Declaration,
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionExecution>, EngineExecutionError> {
        let expression = match &declaration {
            Declaration::Defn(definition) => definition.value.clone(),
            Declaration::Axiom(_) => {
                return Err(EngineExecutionError::UnsupportedDeclaration { kind: "axiom" });
            }
            Declaration::Thm(_) => {
                return Err(EngineExecutionError::UnsupportedDeclaration { kind: "theorem" });
            }
            Declaration::Opaque(_) => {
                return Err(EngineExecutionError::UnsupportedDeclaration { kind: "opaque" });
            }
            Declaration::Mutual(_) => {
                return Err(EngineExecutionError::UnsupportedDeclaration {
                    kind: "mutual block",
                });
            }
            Declaration::Inductive(_) => {
                return Err(EngineExecutionError::UnsupportedDeclaration {
                    kind: "inductive block",
                });
            }
            Declaration::Quotient(_) => {
                return Err(EngineExecutionError::UnsupportedDeclaration {
                    kind: "quotient initialization",
                });
            }
        };
        let admission = match self
            .admit_declaration(declaration, options, limits.admission())
            .map_err(EngineExecutionError::from)?
        {
            Outcome::Complete(admission) => admission,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };

        let catalog = executable_dependencies(&self.environment, &expression, limits.ingress)
            .map_err(EngineExecutionError::Ingress)?;
        let local_lambda = executable_lambda(&admission.declaration, limits.ingress)
            .map_err(EngineExecutionError::Ingress)?;
        let lambdas = local_lambda.as_slice();
        let ingress = fln_comp::ingress::lower_closed_expr_with_lambdas(
            &expression,
            &catalog.intrinsics,
            &[],
            &catalog.functions,
            lambdas,
            limits.ingress,
        )
        .map_err(EngineExecutionError::Ingress)?;
        let lowered =
            fln_comp::fir::lower_to_flbc(ingress.fir()).map_err(EngineExecutionError::Lowering)?;
        let flbc_artifact = fln_comp::flbc::encode_canonical(&lowered, limits.flbc_codec)
            .map_err(EngineExecutionError::Codec)?;
        let executable = fln_comp::flbc::decode_canonical(&flbc_artifact, limits.flbc_codec)
            .map_err(EngineExecutionError::Codec)?;
        let exit = match execute_golem_with_options(&executable, options, limits.vm) {
            Outcome::Complete(exit) => exit,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        Ok(Outcome::Complete(DefinitionExecution {
            engine: admission.engine,
            declaration: admission.declaration,
            base_logical_root: admission.base_logical_root,
            result_logical_root: admission.result_logical_root,
            flbc_artifact,
            exit,
            checker: admission.checker,
        }))
    }
}

fn execute_golem_with_options(
    executable: &fln_comp::flbc::ValidatedProgram,
    options: &KVMap,
    limits: VmExecutionLimits,
) -> Outcome<VmExit> {
    fln_vm::interpreter::execute_with_context(
        executable,
        limits,
        CommandExecutionContext::from_options(options),
        None,
    )
}

fn declaration_kind(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Axiom(_) => "axiom",
        Declaration::Defn(_) => "definition",
        Declaration::Thm(_) => "theorem",
        Declaration::Opaque(_) => "opaque",
        Declaration::Mutual(_) => "mutual block",
        Declaration::Inductive(_) => "inductive block",
        Declaration::Quotient(_) => "quotient initialization",
    }
}

#[derive(Debug)]
struct CheckerReview {
    council: Council,
    agreement: Option<CheckerAgreement>,
    successor_environment: Option<CheckerConstantEnvironment>,
}

impl CheckerReview {
    fn from_seat(
        verdict: SeatVerdict,
        agreement: Option<CheckerAgreement>,
        successor_environment: Option<CheckerConstantEnvironment>,
    ) -> Self {
        Self {
            council: Council::of(vec![Seat::new(
                "fln-checker",
                SeatOrigin::IndependentImplementation,
                SeatBounds::not_established(
                    "fln-checker uses an independent structural budget taxonomy",
                ),
                verdict,
            )]),
            agreement,
            successor_environment,
        }
    }

    fn no_answer(reason: String) -> Self {
        Self::from_seat(SeatVerdict::NoAnswer { reason }, None, None)
    }
}

fn decode_checker_name(name: &Name, budget: CheckerDecodeBudget) -> Result<CheckerName, String> {
    match checker_decode_name(&name.to_canonical_bytes(), budget) {
        CheckerDecodeOutcome::Complete(Ok(name)) => Ok(name),
        CheckerDecodeOutcome::Complete(Err(malformed)) => {
            Err(format!("canonical name decode failed: {malformed:?}"))
        }
        CheckerDecodeOutcome::Inconclusive(stop) => {
            Err(format!("canonical name decode did not finish: {stop:?}"))
        }
    }
}

fn decode_checker_expr(
    expression: &Expr,
    budget: CheckerDecodeBudget,
) -> Result<CheckerExpr, String> {
    match checker_decode_expr(&expression.to_canonical_bytes(), budget) {
        CheckerDecodeOutcome::Complete(Ok(expression)) => Ok(expression),
        CheckerDecodeOutcome::Complete(Err(malformed)) => {
            Err(format!("canonical expression decode failed: {malformed:?}"))
        }
        CheckerDecodeOutcome::Inconclusive(stop) => Err(format!(
            "canonical expression decode did not finish: {stop:?}"
        )),
    }
}

fn decode_checker_names(
    names: &[Name],
    budget: CheckerDecodeBudget,
) -> Result<Vec<CheckerName>, String> {
    let mut decoded = Vec::new();
    decoded
        .try_reserve_exact(names.len())
        .map_err(|_| format!("could not reserve {} checker names", names.len()))?;
    for name in names {
        decoded.push(decode_checker_name(name, budget)?);
    }
    Ok(decoded)
}

fn checker_constant_safety(is_unsafe: bool) -> CheckerConstantSafety {
    if is_unsafe {
        CheckerConstantSafety::Unsafe
    } else {
        CheckerConstantSafety::Safe
    }
}

fn checker_entry(
    info: &ConstantInfo,
    budget: CheckerDecodeBudget,
) -> Result<CheckerConstantEntry, String> {
    let base = info.constant_val();
    let name = decode_checker_name(&base.name, budget)?;
    let level_parameters = decode_checker_names(&base.level_params, budget)?;
    let type_ = decode_checker_expr(&base.type_, budget)?;
    let declaration = match info {
        ConstantInfo::Axiom(value) => CheckerConstantDeclaration::header(
            level_parameters,
            type_,
            CheckerConstantKind::Axiom,
            checker_constant_safety(value.is_unsafe),
        ),
        ConstantInfo::Defn(value) => {
            let hint = match value.hints {
                ReducibilityHints::Opaque => CheckerReducibilityHint::Opaque,
                ReducibilityHints::Abbrev => CheckerReducibilityHint::Abbrev,
                ReducibilityHints::Regular(height) => CheckerReducibilityHint::Regular(height),
            };
            let safety = match value.safety {
                DefinitionSafety::Unsafe => CheckerDefinitionSafety::Unsafe,
                DefinitionSafety::Safe => CheckerDefinitionSafety::Safe,
                DefinitionSafety::Partial => CheckerDefinitionSafety::Partial,
            };
            let body = CheckerDefinitionBody::new(
                decode_checker_expr(&value.value, budget)?,
                hint,
                safety,
                decode_checker_names(&value.all, budget)?,
            );
            CheckerConstantDeclaration::definition(
                level_parameters,
                type_,
                checker_constant_safety(matches!(value.safety, DefinitionSafety::Unsafe)),
                body,
            )
        }
        ConstantInfo::Thm(value) => CheckerConstantDeclaration::theorem(
            level_parameters,
            type_,
            decode_checker_expr(&value.value, budget)?,
            decode_checker_names(&value.all, budget)?,
        ),
        ConstantInfo::Opaque(value) => CheckerConstantDeclaration::opaque(
            level_parameters,
            type_,
            checker_constant_safety(value.is_unsafe),
            decode_checker_expr(&value.value, budget)?,
            decode_checker_names(&value.all, budget)?,
        ),
        ConstantInfo::Quot(_) => CheckerConstantDeclaration::header(
            level_parameters,
            type_,
            CheckerConstantKind::Quotient,
            CheckerConstantSafety::Safe,
        ),
        ConstantInfo::Induct(value) => CheckerConstantDeclaration::header(
            level_parameters,
            type_,
            CheckerConstantKind::Inductive,
            checker_constant_safety(value.is_unsafe),
        ),
        ConstantInfo::Ctor(value) => CheckerConstantDeclaration::header(
            level_parameters,
            type_,
            CheckerConstantKind::Constructor,
            checker_constant_safety(value.is_unsafe),
        ),
        ConstantInfo::Rec(value) => CheckerConstantDeclaration::header(
            level_parameters,
            type_,
            CheckerConstantKind::Recursor,
            checker_constant_safety(value.is_unsafe),
        ),
    };
    Ok(CheckerConstantEntry::new(name, declaration))
}

fn checker_environment(
    environment: &Environment,
    limits: CheckerExecutionLimits,
) -> Result<CheckerConstantEnvironment, String> {
    let mut entries = Vec::new();
    entries
        .try_reserve_exact(environment.len())
        .map_err(|_| format!("could not reserve {} checker constants", environment.len()))?;
    for (_, info) in environment.constants() {
        entries.push(checker_entry(info, limits.decode)?);
    }
    match CheckerConstantEnvironment::build(entries, limits.environment) {
        CheckerEnvironmentOutcome::Complete { environment, .. } => Ok(environment),
        CheckerEnvironmentOutcome::Refused { refusal, .. } => Err(format!(
            "checker environment refused its projection: {refusal:?}"
        )),
        CheckerEnvironmentOutcome::Inconclusive(stop) => Err(format!(
            "checker environment projection did not finish: {stop:?}"
        )),
        CheckerEnvironmentOutcome::InternalFault { fault, .. } => Err(format!(
            "checker environment projection hit an internal fault: {fault:?}"
        )),
    }
}

fn review_mutual_with_independent_checker(
    environment: &Environment,
    retained_environment: Option<&CheckerConstantEnvironment>,
    definitions: &[DefinitionVal],
    limits: CheckerExecutionLimits,
) -> CheckerReview {
    let mut candidates = Vec::new();
    if candidates.try_reserve_exact(definitions.len()).is_err() {
        return CheckerReview::no_answer(format!(
            "could not reserve {} checker mutual-block members",
            definitions.len()
        ));
    }
    for (index, definition) in definitions.iter().enumerate() {
        match checker_entry(&ConstantInfo::Defn(definition.clone()), limits.decode) {
            Ok(candidate) => candidates.push(candidate),
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "mutual-block member {index} projection into fln-checker failed: {detail}"
                ));
            }
        }
    }

    let environment = match retained_environment {
        Some(environment) => environment.clone(),
        None => match checker_environment(environment, limits) {
            Ok(environment) => environment,
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "base projection into fln-checker failed: {detail}"
                ));
            }
        },
    };

    match fln_checker::admit::admit_block(&environment, &candidates, limits.admission) {
        CheckerBlockVerdict::Admitted(admission) => {
            let agreement = CheckerAgreement {
                schema: admission.schema(),
                ground: admission.ground(),
            };
            let mut successor = environment;
            for candidate in candidates {
                let member = candidate.name().clone();
                match successor.extend(candidate, limits.environment) {
                    CheckerEnvironmentOutcome::Complete {
                        environment: extended,
                        ..
                    } => successor = extended,
                    CheckerEnvironmentOutcome::Refused { refusal, .. } => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker refused mutual member {member:?} retention: {refusal:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::Inconclusive(stop) => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker could not retain mutual member {member:?}: {stop:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::InternalFault { fault, .. } => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker hit an internal fault while retaining mutual member \
                             {member:?}: {fault:?}"
                        ));
                    }
                }
            }
            CheckerReview::from_seat(SeatVerdict::Agrees, Some(agreement), Some(successor))
        }
        CheckerBlockVerdict::Rejected(rejection) => CheckerReview::from_seat(
            SeatVerdict::Disagrees {
                detail: format!("fln-checker rejected the mutual block: {rejection:?}"),
            },
            None,
            None,
        ),
        CheckerBlockVerdict::MemberRejected { member, rejection } => CheckerReview::from_seat(
            SeatVerdict::Disagrees {
                detail: format!("fln-checker rejected mutual member {member:?}: {rejection:?}"),
            },
            None,
            None,
        ),
        CheckerBlockVerdict::MemberDeferred { member, deferred } => CheckerReview::no_answer(
            format!("fln-checker deferred mutual member {member:?}: {deferred:?}"),
        ),
        CheckerBlockVerdict::MemberInconclusive { member, stop } => CheckerReview::no_answer(
            format!("fln-checker exhausted or was cancelled on mutual member {member:?}: {stop:?}"),
        ),
        CheckerBlockVerdict::MemberFault { member, fault } => CheckerReview::no_answer(format!(
            "fln-checker hit an internal fault on mutual member {member:?}: {fault:?}"
        )),
    }
}

fn review_with_independent_checker(
    environment: &Environment,
    retained_environment: Option<&CheckerConstantEnvironment>,
    declaration: &Declaration,
    limits: CheckerExecutionLimits,
) -> CheckerReview {
    if let Declaration::Mutual(definitions) = declaration {
        return review_mutual_with_independent_checker(
            environment,
            retained_environment,
            definitions,
            limits,
        );
    }

    let candidate = match declaration {
        Declaration::Axiom(axiom) => {
            checker_entry(&ConstantInfo::Axiom(axiom.clone()), limits.decode)
        }
        Declaration::Defn(definition) => {
            checker_entry(&ConstantInfo::Defn(definition.clone()), limits.decode)
        }
        Declaration::Thm(theorem) => {
            checker_entry(&ConstantInfo::Thm(theorem.clone()), limits.decode)
        }
        Declaration::Opaque(opaque) => {
            checker_entry(&ConstantInfo::Opaque(opaque.clone()), limits.decode)
        }
        _ => {
            return CheckerReview::no_answer(
                "the facade asked the independent checker to review an unsupported declaration"
                    .to_owned(),
            );
        }
    };
    let candidate = match candidate {
        Ok(candidate) => candidate,
        Err(detail) => {
            return CheckerReview::no_answer(format!(
                "candidate projection into fln-checker failed: {detail}"
            ));
        }
    };
    let environment = match retained_environment {
        Some(environment) => environment.clone(),
        None => match checker_environment(environment, limits) {
            Ok(environment) => environment,
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "base projection into fln-checker failed: {detail}"
                ));
            }
        },
    };

    match fln_checker::admit::admit(&environment, &candidate, limits.admission) {
        CheckerVerdict::Admitted(admission) => {
            let agreement = CheckerAgreement {
                schema: admission.schema(),
                ground: admission.ground(),
            };
            match environment.extend(candidate, limits.environment) {
                CheckerEnvironmentOutcome::Complete {
                    environment: successor,
                    ..
                } => {
                    CheckerReview::from_seat(SeatVerdict::Agrees, Some(agreement), Some(successor))
                }
                CheckerEnvironmentOutcome::Refused { refusal, .. } => CheckerReview::no_answer(
                    format!("fln-checker refused candidate retention: {refusal:?}"),
                ),
                CheckerEnvironmentOutcome::Inconclusive(stop) => CheckerReview::no_answer(format!(
                    "fln-checker could not retain the candidate: {stop:?}"
                )),
                CheckerEnvironmentOutcome::InternalFault { fault, .. } => {
                    CheckerReview::no_answer(format!(
                        "fln-checker hit an internal fault while retaining the candidate: {fault:?}"
                    ))
                }
            }
        }
        CheckerVerdict::Rejected(rejection) => CheckerReview::from_seat(
            SeatVerdict::Disagrees {
                detail: format!("fln-checker rejected the declaration: {rejection:?}"),
            },
            None,
            None,
        ),
        CheckerVerdict::Deferred(requirement) => CheckerReview::no_answer(format!(
            "fln-checker deferred the declaration: {requirement:?}"
        )),
        CheckerVerdict::Inconclusive(stop) => {
            CheckerReview::no_answer(format!("fln-checker exhausted or was cancelled: {stop:?}"))
        }
        CheckerVerdict::InternalFault(fault) => {
            CheckerReview::no_answer(format!("fln-checker hit an internal fault: {fault:?}"))
        }
    }
}

/// Derive the compiler catalog from declarations that already passed K1.
///
/// This deliberately supports one exact family of erased scalar/owned
/// signatures. A raw
/// caller-supplied [`FunctionBinding`] would be able to replace a checked
/// constant's body or lie about its runtime type; neither is an acceptable
/// embeddable-engine boundary.
struct ExecutableCatalog {
    intrinsics: Vec<IntrinsicBinding>,
    functions: Vec<FunctionBinding>,
}

struct ExecutableValueTypes {
    nat: Expr,
    string: Expr,
    bool_: Expr,
}

impl ExecutableValueTypes {
    fn bounded_source() -> Self {
        Self {
            nat: Expr::const_(Name::from_components(["Nat"]), Vec::new()),
            string: Expr::const_(Name::from_components(["String"]), Vec::new()),
            bool_: Expr::const_(Name::from_components(["Bool"]), Vec::new()),
        }
    }
}

fn executable_dependencies(
    environment: &Environment,
    source: &Expr,
    limits: IngressLimits,
) -> Result<ExecutableCatalog, IngressError> {
    let value_types = ExecutableValueTypes::bounded_source();
    let mut pending = BTreeSet::new();
    let mut resolved = BTreeSet::new();
    let mut visited_nodes = 0usize;
    collect_executable_constants(source, &mut pending, &mut visited_nodes, limits)?;

    let maximum_functions = limits.fir.max_functions.saturating_sub(1);
    let mut intrinsics = Vec::new();
    let mut functions = Vec::new();
    while let Some(name) = pending.pop_first() {
        if !resolved.insert(name.clone()) {
            continue;
        }
        if let Some(binding) = source_intrinsic_binding(environment, &name) {
            intrinsics
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: 1,
                })?;
            intrinsics.push(binding);
            continue;
        }
        let Some(ConstantInfo::Defn(definition)) = environment.find(&name) else {
            continue;
        };
        let Some(signature) =
            executable_signature(definition, &value_types, &mut visited_nodes, limits, true)?
        else {
            continue;
        };
        let observed = functions.len().saturating_add(1);
        if observed > maximum_functions {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ProgramTables,
                limit: maximum_functions,
                observed,
            });
        }
        functions
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: observed,
            })?;
        let parameter_ownership = borrowed_runtime_parameters(signature.parameters.len())?;
        collect_executable_constants(&signature.body, &mut pending, &mut visited_nodes, limits)?;
        functions.push(FunctionBinding {
            name,
            universe_arity: 0,
            parameters: signature.parameters,
            parameter_ownership,
            result: signature.result,
            result_ownership: signature.result_ownership,
            body: signature.body,
        });
    }
    Ok(ExecutableCatalog {
        intrinsics,
        functions,
    })
}

fn source_intrinsic_binding(environment: &Environment, name: &Name) -> Option<IntrinsicBinding> {
    let info = environment.find(name)?;
    let ConstantInfo::Axiom(actual) = info else {
        return None;
    };
    let Declaration::Axiom(expected) = fln_elab::seed::source_intrinsic_seed_declaration(name)?
    else {
        return None;
    };
    if actual != &expected {
        return None;
    }
    generated_source_intrinsic_binding(name)
}

fn generated_source_intrinsic_binding(name: &Name) -> Option<IntrinsicBinding> {
    use fln_vm::extern_row::{
        ArgumentOwnership as ContractArgumentOwnership, EffectClass as ContractEffectClass,
        Ownership as ContractOwnership, ResultOwnership as ContractResultOwnership,
    };

    let row_name = name.to_display_string();
    let (argument_types, result, type_family_anchor) = match row_name.as_str() {
        "Nat.add" | "Nat.sub" | "Nat.mul" | "Nat.div" | "Nat.gcd" | "Nat.land" | "Nat.lor"
        | "Nat.mod" | "Nat.pow" | "Nat.shiftLeft" | "Nat.shiftRight" | "Nat.xor" => (
            vec![ValueType::Nat, ValueType::Nat],
            ValueType::Nat,
            Some("Nat.add"),
        ),
        "Nat.log2" | "Nat.pred" => (vec![ValueType::Nat], ValueType::Nat, Some("Nat.pred")),
        "Nat.beq" | "Nat.ble" => (
            vec![ValueType::Nat, ValueType::Nat],
            ValueType::Bool,
            Some("Nat.beq"),
        ),
        "String.append" => (
            vec![ValueType::String, ValueType::String],
            ValueType::String,
            None,
        ),
        "String.length" | "String.utf8ByteSize" => (
            vec![ValueType::String],
            ValueType::Nat,
            Some("String.length"),
        ),
        "String.decEq" => (
            vec![ValueType::String, ValueType::String],
            ValueType::Bool,
            None,
        ),
        _ => return None,
    };
    let arity = u32::try_from(argument_types.len()).ok()?;
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == row_name && row.levels == 0 && row.arity == arity)?;
    if let Some(anchor_name) = type_family_anchor {
        let type_anchor = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|candidate| candidate.name == anchor_name)?;
        if row.type_hash != type_anchor.type_hash {
            return None;
        }
    }
    if ContractEffectClass::parse(row.effect).ok()? != ContractEffectClass::Pure {
        return None;
    }
    let ownership = ContractOwnership::parse(row.ownership).ok()?;
    let argument_ownership = ownership
        .argument_ownership(argument_types.len())
        .ok()?
        .into_iter()
        .map(|argument| match argument {
            ContractArgumentOwnership::Borrowed => fln_comp::flbc::ArgumentOwnership::Borrowed,
            ContractArgumentOwnership::Owned => fln_comp::flbc::ArgumentOwnership::Owned,
            ContractArgumentOwnership::Unique => fln_comp::flbc::ArgumentOwnership::Unique,
            ContractArgumentOwnership::Scalar => fln_comp::flbc::ArgumentOwnership::Scalar,
        })
        .collect();
    let result_ownership = match ownership.result_ownership().ok()? {
        ContractResultOwnership::Owned => fln_comp::flbc::ResultOwnership::Owned,
        ContractResultOwnership::Borrowed => fln_comp::flbc::ResultOwnership::Borrowed,
        ContractResultOwnership::Scalar => fln_comp::flbc::ResultOwnership::Scalar,
        ContractResultOwnership::RawObject => fln_comp::flbc::ResultOwnership::RawObject,
    };

    Some(IntrinsicBinding {
        name: name.clone(),
        universe_arity: 0,
        row: row.id.to_owned(),
        arguments: argument_types,
        argument_ownership,
        result,
        result_ownership,
        effect: fln_comp::fir::EffectClass::Pure,
    })
}

/// Describe the definition currently being published when its full value is a
/// supported first-order runtime lambda. This lets the same compiler path
/// execute the function value itself and expose the checked successor snapshot.
fn executable_lambda(
    declaration: &Declaration,
    limits: IngressLimits,
) -> Result<Option<LambdaBinding>, IngressError> {
    let Declaration::Defn(definition) = declaration else {
        return Ok(None);
    };
    let value_types = ExecutableValueTypes::bounded_source();
    let mut visited_nodes = 0usize;
    let Some(signature) =
        executable_signature(definition, &value_types, &mut visited_nodes, limits, false)?
    else {
        return Ok(None);
    };
    if signature.parameters.is_empty() {
        return Ok(None);
    }
    // Catalog eta can give a Const/App alias a first-order signature. Only a
    // real lambda spine is a publishable local closure; executing `copy` as a
    // zero-argument program is an arity error.
    if !matches!(
        definition.value.node(),
        fln_core::expr::ExprNode::Lam { .. }
    ) {
        return Ok(None);
    }
    let parameter_ownership = borrowed_runtime_parameters(signature.parameters.len())?;
    Ok(Some(LambdaBinding {
        lambda: definition.value.clone(),
        parameters: signature.parameters,
        parameter_ownership,
        result: signature.result,
        result_ownership: signature.result_ownership,
        recursion: LambdaRecursion::NonRecursive,
    }))
}

fn borrowed_runtime_parameters(
    arity: usize,
) -> Result<Vec<fln_comp::flbc::ArgumentOwnership>, IngressError> {
    let mut parameter_ownership = Vec::new();
    parameter_ownership
        .try_reserve_exact(arity)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: arity,
        })?;
    parameter_ownership.resize(arity, fln_comp::flbc::ArgumentOwnership::Borrowed);
    Ok(parameter_ownership)
}

struct ExecutableSignature {
    parameters: Vec<ValueType>,
    result: ValueType,
    result_ownership: CallableResultOwnership,
    body: Expr,
}

/// Bind one checked definition to the compiler's exact first-order runtime ABI.
///
/// Pi binders and lambda binders must match structurally and in count. K1 has
/// already proved the declaration well typed, but the runtime bridge accepts a
/// deliberately narrower representation than definitional equality so it
/// never invents an erasure rule. The returned body has its top-level lambdas
/// removed, as required by [`FunctionBinding`].
fn executable_signature(
    definition: &DefinitionVal,
    value_types: &ExecutableValueTypes,
    visited_nodes: &mut usize,
    limits: IngressLimits,
    eta_expand: bool,
) -> Result<Option<ExecutableSignature>, IngressError> {
    use fln_core::expr::ExprNode;

    if !definition.base.level_params.is_empty() {
        return Ok(None);
    }

    let mut declared_type = &definition.base.type_;
    let mut body = &definition.value;
    let mut parameters = Vec::new();
    loop {
        charge_catalog_node(visited_nodes, limits)?;
        match declared_type.node() {
            ExprNode::ForallE {
                binder_type,
                body: result_type,
                ..
            } => {
                let Some((parameter, _)) = executable_value_type(binder_type, value_types) else {
                    break;
                };
                charge_catalog_node(visited_nodes, limits)?;
                let ExprNode::Lam {
                    binder_type: value_binder_type,
                    body: value_body,
                    ..
                } = body.node()
                else {
                    // Remaining Π after zero or more real lambdas is still a
                    // first-order function (`fun ignored => copy`). Eta is
                    // sound only when the current body is closed; a body that
                    // already mentions peeled binders would need lifting.
                    // Local-closure execution must not eta: it binds the
                    // source lambda spine, whose binder count would then
                    // disagree with the expanded signature.
                    if eta_expand {
                        return eta_expand_signature(
                            body,
                            declared_type,
                            parameters,
                            value_types,
                            visited_nodes,
                            limits,
                        );
                    }
                    return Ok(None);
                };
                if value_binder_type != binder_type {
                    return Ok(None);
                }
                let observed = parameters.len().saturating_add(1);
                if observed > limits.max_context_depth {
                    return Err(IngressError::ResourceLimit {
                        resource: IngressResource::ContextDepth,
                        limit: limits.max_context_depth,
                        observed,
                    });
                }
                parameters
                    .try_reserve(1)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::ProgramTables,
                        requested: observed,
                    })?;
                parameters.push(parameter);
                declared_type = result_type;
                body = value_body;
            }
            _ => break,
        }
    }

    let Some((result, result_ownership)) = executable_value_type(declared_type, value_types) else {
        return Ok(None);
    };
    Ok(Some(ExecutableSignature {
        parameters,
        result,
        result_ownership,
        body: body.clone(),
    }))
}

/// Compile `fun ignored => copy` as `fun ignored x => copy x` when the
/// remaining type is a first-order scalar telescope and `function` is already
/// that closed function value.
fn eta_expand_signature(
    function: &Expr,
    remaining_type: &Expr,
    mut parameters: Vec<ValueType>,
    value_types: &ExecutableValueTypes,
    visited_nodes: &mut usize,
    limits: IngressLimits,
) -> Result<Option<ExecutableSignature>, IngressError> {
    use fln_core::expr::ExprNode;

    let mut remaining = remaining_type;
    let mut extra = 0_usize;
    loop {
        charge_catalog_node(visited_nodes, limits)?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = remaining.node()
        else {
            break;
        };
        if body.has_loose_bvars() {
            return Ok(None);
        }
        let Some((parameter, _)) = executable_value_type(binder_type, value_types) else {
            return Ok(None);
        };
        extra = extra.saturating_add(1);
        let observed = parameters.len().saturating_add(1);
        if observed > limits.max_context_depth {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: limits.max_context_depth,
                observed,
            });
        }
        parameters
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: observed,
            })?;
        parameters.push(parameter);
        remaining = body;
    }
    if extra == 0 {
        return Ok(None);
    }
    let Some((result, result_ownership)) = executable_value_type(remaining, value_types) else {
        return Ok(None);
    };

    let extra_u32 = u32::try_from(extra).map_err(|_| IngressError::ResourceLimit {
        resource: IngressResource::ContextDepth,
        limit: limits.max_context_depth,
        observed: extra,
    })?;
    let mut eta = function
        .lift_loose(0, extra_u32)
        .map_err(|_| IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: limits.max_context_depth,
            observed: extra,
        })?;
    for index in (0..extra).rev() {
        charge_catalog_node(visited_nodes, limits)?;
        let index = u32::try_from(index).map_err(|_| IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: limits.max_context_depth,
            observed: extra,
        })?;
        let argument = Expr::bvar(index).map_err(|_| IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: limits.max_context_depth,
            observed: extra,
        })?;
        eta = Expr::app(eta, argument);
    }
    Ok(Some(ExecutableSignature {
        parameters,
        result,
        result_ownership,
        body: eta,
    }))
}

fn executable_value_type(
    source: &Expr,
    value_types: &ExecutableValueTypes,
) -> Option<(ValueType, CallableResultOwnership)> {
    if source == &value_types.nat {
        Some((ValueType::Nat, CallableResultOwnership::OwnedOrScalar))
    } else if source == &value_types.string {
        Some((ValueType::String, CallableResultOwnership::Owned))
    } else if source == &value_types.bool_ {
        Some((ValueType::Bool, CallableResultOwnership::Scalar))
    } else {
        None
    }
}

fn charge_catalog_node(
    visited_nodes: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    let observed = visited_nodes.saturating_add(1);
    if observed > limits.max_nodes {
        return Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: limits.max_nodes,
            observed,
        });
    }
    *visited_nodes = observed;
    Ok(())
}

/// Find only constants in expression positions that compiler ingress evaluates.
/// Type annotations remain source metadata on the currently implemented path.
fn collect_executable_constants(
    source: &Expr,
    names: &mut BTreeSet<Name>,
    visited_nodes: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    use fln_core::expr::ExprNode;

    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::PendingTasks,
            requested: 1,
        })?;
    pending.push(source);
    while let Some(expression) = pending.pop() {
        charge_catalog_node(visited_nodes, limits)?;
        match expression.node() {
            ExprNode::Const { name, .. } => {
                names.insert(name.clone());
            }
            ExprNode::App { f, a } => {
                pending
                    .try_reserve(2)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::PendingTasks,
                        requested: pending.len().saturating_add(2),
                    })?;
                pending.push(a);
                pending.push(f);
            }
            ExprNode::Lam { body, .. } | ExprNode::ForallE { body, .. } => {
                pending
                    .try_reserve(1)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::PendingTasks,
                        requested: pending.len().saturating_add(1),
                    })?;
                pending.push(body);
            }
            ExprNode::LetE { value, body, .. } => {
                pending
                    .try_reserve(2)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::PendingTasks,
                        requested: pending.len().saturating_add(2),
                    })?;
                pending.push(body);
                pending.push(value);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                pending
                    .try_reserve(1)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::PendingTasks,
                        requested: pending.len().saturating_add(1),
                    })?;
                pending.push(expr);
            }
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    Ok(())
}

/// Independent checker bounds for one facade execution.
///
/// These defaults are finite and deliberately separate from K1's calibrated
/// stack budget. Callers may tighten or expand them explicitly without making a
/// checker non-answer count as agreement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckerExecutionLimits {
    pub decode: CheckerDecodeBudget,
    pub environment: CheckerEnvironmentBudget,
    pub admission: CheckerAdmissionBudget,
}

impl Default for CheckerExecutionLimits {
    fn default() -> Self {
        let term = fln_checker::term::TermBudget::new(1_000_000, 10_000_000)
            .with_max_arena_nodes(1_000_000);
        let whnf = fln_checker::whnf::WhnfBudget::new(1_000_000, 1_000_000, term);
        let inference = fln_checker::infer::InferenceBudget::new(1_000_000, 1_000_000, term, term)
            .with_whnf(whnf);
        Self {
            decode: CheckerDecodeBudget::new(16 * 1024 * 1024, 1_000_000),
            environment: CheckerEnvironmentBudget::new(
                10_000_000,
                100_000,
                100_000,
                100_000,
                10_000_000,
                100_000_000,
            ),
            admission: CheckerAdmissionBudget::new(inference, whnf, inference.defeq),
        }
    }
}

/// Caller-supplied bounds for admission and immutable environment publication.
///
/// There is deliberately no `Default`: as with [`EngineExecutionLimits`], the
/// kernel budget must be calibrated to the native stack on which it runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineAdmissionLimits {
    pub kernel: Budget,
    pub checker: CheckerExecutionLimits,
    pub declaration: DeclarationBudget,
    pub collisions: CollisionBudget,
}

impl EngineAdmissionLimits {
    /// Use subsystem defaults around an explicitly calibrated kernel budget.
    pub fn new(kernel: Budget) -> Self {
        Self {
            kernel,
            checker: CheckerExecutionLimits::default(),
            declaration: DeclarationBudget::default(),
            collisions: CollisionBudget::default(),
        }
    }
}

/// Independent caller-supplied bounds for every bounded stage of one execution.
///
/// There is deliberately no `Default`: a kernel budget is calibrated to the
/// native stack on which the caller will run it, and an embeddable API cannot
/// infer that stack size honestly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineExecutionLimits {
    pub kernel: Budget,
    pub checker: CheckerExecutionLimits,
    pub declaration: DeclarationBudget,
    pub collisions: CollisionBudget,
    pub ingress: IngressLimits,
    pub flbc_codec: CodecLimits,
    pub vm: VmExecutionLimits,
}

impl EngineExecutionLimits {
    /// Use subsystem defaults around an explicitly calibrated kernel budget.
    pub fn new(kernel: Budget) -> Self {
        Self {
            kernel,
            checker: CheckerExecutionLimits::default(),
            declaration: DeclarationBudget::default(),
            collisions: CollisionBudget::default(),
            ingress: IngressLimits::default(),
            flbc_codec: CodecLimits::default(),
            vm: VmExecutionLimits::default(),
        }
    }

    /// The exact admission subset used before compiler ingress and Golem.
    pub fn admission(self) -> EngineAdmissionLimits {
        EngineAdmissionLimits {
            kernel: self.kernel,
            checker: self.checker,
            declaration: self.declaration,
            collisions: self.collisions,
        }
    }
}

/// The independent checker's exact completed admission observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckerAgreement {
    pub schema: &'static str,
    pub ground: CheckerAdmissionGround,
}

/// The authoritative outputs of one completed admission-only transition.
#[derive(Debug)]
pub struct DeclarationAdmission {
    /// The immutable snapshot containing the newly published declaration.
    pub engine: Engine,
    /// The exact declaration admitted by K1 and independently reviewed.
    pub declaration: Declaration,
    /// The exact base-environment identity under the caller's options.
    pub base_logical_root: LogicalRoot,
    /// The exact successor-environment identity under the same options.
    pub result_logical_root: LogicalRoot,
    /// The independent checker observation that allowed the council to agree.
    pub checker: CheckerAgreement,
}

/// The authoritative result of one atomic nonempty admission batch.
#[derive(Debug)]
pub struct DeclarationBatchAdmission {
    /// The immutable snapshot containing every published declaration.
    pub engine: Engine,
    /// The batch's original environment identity under the caller's options.
    pub base_logical_root: LogicalRoot,
    /// The final environment identity under the same options.
    pub result_logical_root: LogicalRoot,
    /// Every completed admission in input order, including root transitions.
    pub admissions: Vec<DeclarationAdmission>,
}

/// The authoritative outputs of one completed bounded engine run.
#[derive(Debug)]
pub struct DefinitionExecution {
    /// The immutable snapshot containing the newly published declaration.
    pub engine: Engine,
    /// The exact declaration admitted by K1 and then published.
    pub declaration: Declaration,
    /// The exact base-environment identity under the caller's options.
    pub base_logical_root: LogicalRoot,
    /// The exact successor-environment identity under the same options.
    pub result_logical_root: LogicalRoot,
    /// The canonical FLBC bytes decoded and executed by Golem.
    pub flbc_artifact: Vec<u8>,
    /// Golem's completed domain result.
    pub exit: VmExit,
    /// The independent checker observation that allowed the council to agree.
    pub checker: CheckerAgreement,
}

/// The authoritative result of one atomic nonempty definition batch.
#[derive(Debug)]
pub struct DefinitionBatchExecution {
    /// The immutable snapshot containing every published definition.
    pub engine: Engine,
    /// The batch's original environment identity under the caller's options.
    pub base_logical_root: LogicalRoot,
    /// The final environment identity under the same options.
    pub result_logical_root: LogicalRoot,
    /// Every completed definition in input order, including its root transition.
    pub executions: Vec<DefinitionExecution>,
}

const SOURCE_RUN_EPOCH_ID: EpochId = EpochId::new(4_032_000);
const SOURCE_RUN_CGSE_POLICY_ID: CgsePolicyId = CgsePolicyId::new(1);
const SOURCE_RUN_TARGET_X86_64_LINUX_GNU_ID: TargetId = TargetId::new(1);
const SOURCE_RUN_DEBUG_PROFILE_ID: BuildProfileId = BuildProfileId::new(1);
const SOURCE_RUN_RELEASE_PROFILE_ID: BuildProfileId = BuildProfileId::new(2);
const SOURCE_RUN_TARGET_TRIPLE: &str = "x86_64-unknown-linux-gnu";
const SOURCE_RUN_POLICY_TAG: &str = "fln.source-run.product-policy/1";

fn source_run_build_profile() -> (BuildProfileId, &'static str) {
    if cfg!(debug_assertions) {
        (SOURCE_RUN_DEBUG_PROFILE_ID, "debug")
    } else {
        (SOURCE_RUN_RELEASE_PROFILE_ID, "release")
    }
}

fn current_source_run_coordinates()
-> Result<StandardProductCoordinatesV1, SourceRunSidecarBuildError> {
    if !cfg!(all(
        target_arch = "x86_64",
        target_os = "linux",
        target_env = "gnu"
    )) {
        return Err(SourceRunSidecarBuildError::UnsupportedTarget {
            target: format!(
                "{}-{}-{}",
                std::env::consts::ARCH,
                std::env::consts::OS,
                std::env::consts::FAMILY
            ),
        });
    }
    Ok(StandardProductCoordinatesV1 {
        mode: Mode::Sound,
        epoch: SOURCE_RUN_EPOCH_ID,
        cgse_policy: SOURCE_RUN_CGSE_POLICY_ID,
        determinism: DeterminismClass::D1Canonicalized,
        target: SOURCE_RUN_TARGET_X86_64_LINUX_GNU_ID,
        build_profile: source_run_build_profile().0,
    })
}

fn material_bytes(tag: &str, write: impl FnOnce(&mut CanonWriter)) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.str(tag);
    write(&mut writer);
    writer.into_bytes()
}

fn source_material(sources: &[&[u8]]) -> Vec<u8> {
    material_bytes("fln.source-run.sources/1", |writer| {
        writer.u64(sources.len() as u64);
        for source in sources {
            writer.bytes(source);
        }
    })
}

fn suite_lock_material() -> Vec<u8> {
    material_bytes("fln.source-run.suite-lock/1", |writer| {
        writer.bytes(include_bytes!("../../../SUITE.lock"));
    })
}

fn options_material(options: &KVMap) -> Vec<u8> {
    material_bytes("fln.source-run.options/1", |writer| {
        writer.bytes(&options.to_canonical_bytes());
    })
}

fn empty_set_material(tag: &str) -> Vec<u8> {
    material_bytes(tag, |writer| writer.u64(0))
}

fn mode_material() -> Vec<u8> {
    material_bytes("fln.source-run.mode/1", |writer| {
        writer.u8(Mode::Sound.tag());
    })
}

fn epoch_material() -> Vec<u8> {
    material_bytes("fln.source-run.epoch/1", |writer| {
        writer.bytes(&SOURCE_RUN_EPOCH_ID.get().to_le_bytes());
        writer.str(OLEAN_PIN_TAG);
        writer.str(OLEAN_PIN_COMMIT);
    })
}

fn target_material() -> Vec<u8> {
    material_bytes("fln.source-run.target/1", |writer| {
        writer.bytes(&SOURCE_RUN_TARGET_X86_64_LINUX_GNU_ID.get().to_le_bytes());
        writer.str(SOURCE_RUN_TARGET_TRIPLE);
    })
}

fn build_profile_material() -> Vec<u8> {
    let (profile, name) = source_run_build_profile();
    material_bytes("fln.source-run.build-profile/1", |writer| {
        writer.bytes(&profile.get().to_le_bytes());
        writer.str(name);
    })
}

fn policy_material() -> Vec<u8> {
    material_bytes("fln.source-run.policy-epochs/1", |writer| {
        writer.str(SOURCE_RUN_POLICY_TAG);
        writer.bytes(&SOURCE_RUN_CGSE_POLICY_ID.get().to_le_bytes());
        writer.u16(fln_comp::flbc::FLBC_SCHEMA_VERSION);
        writer.u16(fln_comp::flbc::FLBC_WIRE_VERSION);
        writer.u16(fln_comp::flbc::OWNERSHIP_WITNESS_VERSION);
    })
}

fn semantic_input_material(completed: &DefinitionBatchExecution) -> Vec<u8> {
    material_bytes("fln.source-run.semantic-inputs/1", |writer| {
        writer.u64(completed.executions.len() as u64);
        writer.bytes(&completed.base_logical_root.0.0);
        writer.bytes(&completed.result_logical_root.0.0);
        for execution in &completed.executions {
            writer.bytes(&execution.base_logical_root.0.0);
            writer.bytes(&execution.result_logical_root.0.0);
            writer.bytes(&flbc_product_root(&execution.flbc_artifact).bytes());
        }
    })
}

fn source_run_material<'a>(
    sources: &[&[u8]],
    options: &KVMap,
    toolchain_image: &'a [u8],
    completed: &DefinitionBatchExecution,
) -> Vec<(ClosureComponent, std::borrow::Cow<'a, [u8]>)> {
    vec![
        (
            ClosureComponent::Sources,
            std::borrow::Cow::Owned(source_material(sources)),
        ),
        (
            ClosureComponent::Toolchain,
            std::borrow::Cow::Borrowed(toolchain_image),
        ),
        (
            ClosureComponent::SuiteLock,
            std::borrow::Cow::Owned(suite_lock_material()),
        ),
        (
            ClosureComponent::Options,
            std::borrow::Cow::Owned(options_material(options)),
        ),
        (
            ClosureComponent::Plugins,
            std::borrow::Cow::Owned(empty_set_material("fln.source-run.plugins/1")),
        ),
        (
            ClosureComponent::Mode,
            std::borrow::Cow::Owned(mode_material()),
        ),
        (
            ClosureComponent::Epoch,
            std::borrow::Cow::Owned(epoch_material()),
        ),
        (
            ClosureComponent::Target,
            std::borrow::Cow::Owned(target_material()),
        ),
        (
            ClosureComponent::BuildProfile,
            std::borrow::Cow::Owned(build_profile_material()),
        ),
        (
            ClosureComponent::Features,
            std::borrow::Cow::Owned(empty_set_material("fln.source-run.features/1")),
        ),
        (
            ClosureComponent::PolicyEpochs,
            std::borrow::Cow::Owned(policy_material()),
        ),
        (
            ClosureComponent::SemanticInputs,
            std::borrow::Cow::Owned(semantic_input_material(completed)),
        ),
        (
            ClosureComponent::ReplayInputs,
            std::borrow::Cow::Owned(empty_set_material("fln.source-run.replay-inputs/1")),
        ),
    ]
}

/// Bind the bounded source runner's exact final FLBC bytes to its standard-profile
/// closure. The toolchain component is the caller-supplied current executable image;
/// this API makes no certified/reproducible claim and cannot construct that profile.
pub fn build_source_run_flbc_sidecar(
    sources: &[&[u8]],
    options: &KVMap,
    toolchain_image: &[u8],
    completed: &DefinitionBatchExecution,
) -> Result<FlbcProductSidecarV1, SourceRunSidecarBuildError> {
    let final_execution = completed
        .executions
        .last()
        .ok_or(SourceRunSidecarBuildError::EmptyExecutionBatch)?;
    let coordinates = current_source_run_coordinates()?;
    let material = source_run_material(sources, options, toolchain_image, completed);
    let entries: Vec<_> = material
        .iter()
        .map(|(component, bytes)| ClosureMaterialV1 {
            component: *component,
            bytes: bytes.as_ref(),
        })
        .collect();
    FlbcProductSidecarV1::build_standard(coordinates, &entries, &final_execution.flbc_artifact)
        .map_err(SourceRunSidecarBuildError::Closure)
}

/// Validate a sidecar against exact FLBC bytes and every current source-run component
/// the consumer can independently rederive. Source bytes and elaborated logical roots
/// are intentionally not reconstructed from executable output; v1 is a standard
/// binding, not a certified source-reproducibility proof.
pub fn verify_source_run_flbc_sidecar(
    sidecar_bytes: &[u8],
    flbc_product: &[u8],
    toolchain_image: &[u8],
) -> Result<FlbcProductSidecarV1, SourceRunSidecarVerificationError> {
    let sidecar = decode_flbc_product_sidecar(sidecar_bytes)
        .map_err(SourceRunSidecarVerificationError::Codec)?;
    let expected = current_source_run_coordinates().map_err(|error| match error {
        SourceRunSidecarBuildError::UnsupportedTarget { target } => {
            SourceRunSidecarVerificationError::UnsupportedTarget { target }
        }
        SourceRunSidecarBuildError::EmptyExecutionBatch
        | SourceRunSidecarBuildError::Closure(_) => {
            unreachable!("coordinate derivation cannot inspect an execution closure")
        }
    })?;
    sidecar
        .verify_coordinates(expected)
        .map_err(SourceRunSidecarVerificationError::Binding)?;
    sidecar
        .verify_product(flbc_product, Mode::Sound)
        .map_err(SourceRunSidecarVerificationError::Binding)?;
    sidecar
        .verify_component_material(ClosureComponent::Toolchain, toolchain_image)
        .map_err(SourceRunSidecarVerificationError::Binding)?;
    let options = KVMap::new();
    for (component, material) in [
        (ClosureComponent::SuiteLock, suite_lock_material()),
        (ClosureComponent::Options, options_material(&options)),
        (
            ClosureComponent::Plugins,
            empty_set_material("fln.source-run.plugins/1"),
        ),
        (ClosureComponent::Mode, mode_material()),
        (ClosureComponent::Epoch, epoch_material()),
        (ClosureComponent::Target, target_material()),
        (ClosureComponent::BuildProfile, build_profile_material()),
        (
            ClosureComponent::Features,
            empty_set_material("fln.source-run.features/1"),
        ),
        (ClosureComponent::PolicyEpochs, policy_material()),
        (
            ClosureComponent::ReplayInputs,
            empty_set_material("fln.source-run.replay-inputs/1"),
        ),
    ] {
        sidecar
            .verify_component_material(component, &material)
            .map_err(SourceRunSidecarVerificationError::Binding)?;
    }
    Ok(sidecar)
}

/// A completed refusal before an admission-only successor is exposed.
/// Non-answers live in [`Outcome`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineAdmissionError {
    EmptyBatch,
    AllocationFailure {
        resource: &'static str,
        requested: usize,
    },
    BatchDeclaration {
        index: usize,
        error: Box<EngineAdmissionError>,
    },
    UnsupportedDeclaration {
        kind: &'static str,
    },
    KernelRejected {
        class: RejectClass,
        message: String,
    },
    CouncilHalted {
        summary: String,
    },
    CheckerBridge {
        detail: String,
    },
    DuplicateName {
        name: Name,
    },
    UnexpectedPublication {
        detail: &'static str,
    },
}

impl fmt::Display for EngineAdmissionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyBatch => write!(formatter, "declaration batch must not be empty"),
            Self::AllocationFailure {
                resource,
                requested,
            } => write!(
                formatter,
                "could not reserve {requested} entries for {resource}"
            ),
            Self::BatchDeclaration { index, error } => {
                write!(formatter, "declaration batch item {index} failed: {error}")
            }
            Self::UnsupportedDeclaration { kind } => write!(
                formatter,
                "cannot admit {kind}: the independent checker has no completed representation"
            ),
            Self::KernelRejected { class, message } => {
                write!(
                    formatter,
                    "kernel rejected declaration ({class:?}): {message}"
                )
            }
            Self::CouncilHalted { summary } => write!(formatter, "council halted: {summary}"),
            Self::CheckerBridge { detail } => {
                write!(formatter, "independent checker bridge failed: {detail}")
            }
            Self::DuplicateName { name } => write!(
                formatter,
                "environment already contains {}",
                name.to_display_string()
            ),
            Self::UnexpectedPublication { detail } => {
                write!(formatter, "unexpected publication result: {detail}")
            }
        }
    }
}

impl std::error::Error for EngineAdmissionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::BatchDeclaration { error, .. } => Some(error.as_ref()),
            _ => None,
        }
    }
}

/// A completed refusal before Golem execution. Non-answers live in `Outcome`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineExecutionError {
    EmptyBatch,
    AllocationFailure {
        resource: &'static str,
        requested: usize,
    },
    BatchCommand {
        index: usize,
        error: Box<EngineExecutionError>,
    },
    Frontend(NatDefinitionFrontendError),
    KernelRejected {
        class: RejectClass,
        message: String,
    },
    CouncilHalted {
        summary: String,
    },
    CheckerBridge {
        detail: String,
    },
    DuplicateName {
        name: Name,
    },
    UnsupportedDeclaration {
        kind: &'static str,
    },
    UnexpectedPublication {
        detail: &'static str,
    },
    Ingress(IngressError),
    Lowering(LoweringError),
    Codec(CodecError),
}

impl fmt::Display for EngineExecutionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyBatch => write!(formatter, "definition batch must not be empty"),
            Self::AllocationFailure {
                resource,
                requested,
            } => write!(
                formatter,
                "could not reserve {requested} entries for {resource}"
            ),
            Self::BatchCommand { index, error } => {
                write!(
                    formatter,
                    "definition batch command {index} failed: {error}"
                )
            }
            Self::Frontend(error) => write!(formatter, "frontend refused source: {error}"),
            Self::KernelRejected { class, message } => {
                write!(
                    formatter,
                    "kernel rejected declaration ({class:?}): {message}"
                )
            }
            Self::CouncilHalted { summary } => write!(formatter, "council halted: {summary}"),
            Self::CheckerBridge { detail } => {
                write!(formatter, "independent checker bridge failed: {detail}")
            }
            Self::DuplicateName { name } => {
                write!(
                    formatter,
                    "environment already contains {}",
                    name.to_display_string()
                )
            }
            Self::UnsupportedDeclaration { kind } => {
                write!(formatter, "cannot execute {kind}: no definition body")
            }
            Self::UnexpectedPublication { detail } => {
                write!(formatter, "unexpected publication result: {detail}")
            }
            Self::Ingress(error) => write!(formatter, "compiler ingress refused term: {error:?}"),
            Self::Lowering(error) => write!(formatter, "FIR lowering refused term: {error}"),
            Self::Codec(error) => write!(formatter, "FLBC codec refused artifact: {error:?}"),
        }
    }
}

impl std::error::Error for EngineExecutionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::BatchCommand { error, .. } => Some(error.as_ref()),
            _ => None,
        }
    }
}

impl From<EngineAdmissionError> for EngineExecutionError {
    fn from(error: EngineAdmissionError) -> Self {
        match error {
            EngineAdmissionError::EmptyBatch => Self::EmptyBatch,
            EngineAdmissionError::AllocationFailure {
                resource,
                requested,
            } => Self::AllocationFailure {
                resource,
                requested,
            },
            EngineAdmissionError::BatchDeclaration { index, error } => Self::BatchCommand {
                index,
                error: Box::new(Self::from(*error)),
            },
            EngineAdmissionError::UnsupportedDeclaration { kind } => {
                Self::UnsupportedDeclaration { kind }
            }
            EngineAdmissionError::KernelRejected { class, message } => {
                Self::KernelRejected { class, message }
            }
            EngineAdmissionError::CouncilHalted { summary } => Self::CouncilHalted { summary },
            EngineAdmissionError::CheckerBridge { detail } => Self::CheckerBridge { detail },
            EngineAdmissionError::DuplicateName { name } => Self::DuplicateName { name },
            EngineAdmissionError::UnexpectedPublication { detail } => {
                Self::UnexpectedPublication { detail }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        AxiomVal, BinderInfo, Budget, CheckerAdmissionBudget, CheckerAdmissionGround,
        ClosedVmValue, ClosedVmValueError, ConstantInfo, ConstantVal, Declaration,
        DefinitionSafety, DefinitionVal, DiagnosticChannel, DiagnosticColorPolicy, DiagnosticEpoch,
        DiagnosticFormat, DiagnosticFrontend, DiagnosticOrderPolicy, DiagnosticPathPolicy, Engine,
        EngineAdmissionError, EngineAdmissionLimits, EngineBvDecideError,
        EngineBvDecideInconclusive, EngineBvDecideLimits, EngineBvDecideOutcome,
        EngineExecutionError, EngineExecutionLimits, Environment, ExitClass, Expr,
        FlbcExecutionLimits, IngressError, IngressResource, KVMap, Level, Literal, Name,
        NatDefinitionFrontendError, NatLit, OleanCheckError, OleanCheckLimits,
        OleanDeclarationError, OleanDecodeError, OleanDecodeLimits, OleanModuleImport,
        OleanModuleInput, OleanRebuildError, OleanRegionError, OleanWalkBudget, OpaqueVal, Outcome,
        ProjectionRefusal, ProjectionRequest, ProjectionSnapshot, ReducibilityHints, RejectClass,
        TheoremVal, VmExecutionLimits, closed_vm_value, decode_olean_artifact,
        execute_flbc_artifact, execute_golem_with_options, project_lsp_diagnostics,
        rebuild_olean_artifact,
    };
    use fln_comp::flbc::{
        ArgumentOwnership, CallableResultOwnership, CodecError, CodecLimits, Function, FunctionId,
        Instruction, Program, Register, ResultOwnership, ValidatedProgram, encode_canonical,
        validate,
    };
    use fln_core::diag::ResourceReason;
    use fln_core::mode::{Mode, ReproducibilityProfile};
    use fln_core::options::DataValue;
    use fln_core::outcome::{Authority, InconclusiveCause};
    use fln_env::constants::{QuotKind, QuotVal};
    use fln_verdict::{BoolExpr, BvDecideRequest};
    use fln_vm::interpreter::{ExecutionUsage, ValueKind, VmExit, value_kind};

    fn test_budget() -> Budget {
        Budget::for_stack_bytes(2 * 1024 * 1024)
    }

    fn test_limits() -> EngineExecutionLimits {
        EngineExecutionLimits::new(test_budget())
    }

    fn seeded_engine() -> Engine {
        Engine::with_nat_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the Nat seed council does not reject")
            .into_complete()
            .expect("the bounded Nat seed council answers completely")
    }

    fn engine_with_string_type() -> Engine {
        let seeded = seeded_engine();
        seeded
            .admit_declaration(
                typed_axiom("String", Expr::sort(Level::one())),
                &KVMap::new(),
                EngineAdmissionLimits::new(test_budget()),
            )
            .expect("the String type stand-in reaches both council seats")
            .into_complete()
            .expect("the bounded String type admission answers completely")
            .engine
    }

    fn bv_identity_type() -> Expr {
        Expr::forall_e(
            Name::from_components(["p"]),
            Expr::sort(Level::zero()),
            Expr::forall_e(
                Name::from_components(["h"]),
                Expr::bvar(0).expect("test bound variable is in range"),
                Expr::bvar(1).expect("test bound variable is in range"),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    }

    fn bv_identity_proof() -> Expr {
        Expr::lam(
            Name::from_components(["p"]),
            Expr::sort(Level::zero()),
            Expr::lam(
                Name::from_components(["h"]),
                Expr::bvar(0).expect("test bound variable is in range"),
                Expr::bvar(0).expect("test bound variable is in range"),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    }

    fn bv_request(proposition: BoolExpr, theorem: &str) -> BvDecideRequest {
        BvDecideRequest::new(
            proposition,
            Name::from_components([theorem]),
            Vec::new(),
            bv_identity_type(),
            bv_identity_proof(),
            Mode::Sound,
            ReproducibilityProfile::Standard,
        )
    }

    fn olean_fixture(name: &str) -> Vec<u8> {
        // Resolve the invoking tree at run time. A cached test binary from a
        // different checkout must never silently read that checkout's fixture.
        let manifest_dir = std::env::var_os("CARGO_MANIFEST_DIR")
            .map(std::path::PathBuf::from)
            .expect("cargo identifies the invoking crate directory");
        let path = manifest_dir.join("../../tribunal/fixtures/c3").join(name);
        std::fs::read(&path)
            .unwrap_or_else(|error| panic!("cannot read fixture {}: {error}", path.display()))
    }

    fn standalone_olean(constants: &[ConstantInfo]) -> Vec<u8> {
        olean_with_imports(constants, &[])
    }

    fn olean_with_imports(constants: &[ConstantInfo], imports: &[OleanModuleImport]) -> Vec<u8> {
        let lean_version = super::OLEAN_PIN_TAG
            .strip_prefix('v')
            .expect("the extracted pin tag carries its v prefix");
        super::encode_olean_module(
            super::OleanModuleWriteInput {
                is_module: false,
                imports,
                constants,
                extra_const_names: &[],
            },
            super::OleanWriteHeader {
                version: super::OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version,
                githash: super::OLEAN_PIN_COMMIT,
                base_addr: (super::OLEAN_REGION_ALIGN as u64) * 2,
            },
            super::OleanWriteBudget::default(),
        )
        .expect("the public writer emits the standalone checking fixture")
        .bytes
    }

    fn standalone_declarations() -> Vec<ConstantInfo> {
        let proposition = Name::from_components(["Fixture", "P"]);
        let witness = Name::from_components(["Fixture", "p"]);
        let theorem = Name::from_components(["Fixture", "t"]);
        let proposition_expr = Expr::const_(proposition.clone(), Vec::new());
        let witness_expr = Expr::const_(witness.clone(), Vec::new());
        vec![
            ConstantInfo::Thm(TheoremVal {
                base: ConstantVal {
                    name: theorem,
                    level_params: Vec::new(),
                    type_: proposition_expr.clone(),
                },
                value: witness_expr,
                all: Vec::new(),
            }),
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: witness,
                    level_params: Vec::new(),
                    type_: proposition_expr,
                },
                is_unsafe: false,
            }),
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: proposition,
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::zero()),
                },
                is_unsafe: false,
            }),
        ]
    }

    fn heartbeat_program(new_count: u64, check_system: bool) -> ValidatedProgram {
        let mut code = vec![
            Instruction::Nat {
                dst: Register::new(0),
                value: new_count,
            },
            Instruction::Intrinsic {
                dst: Register::new(1),
                row: "extern:IO.setNumHeartbeats".to_string(),
                args: vec![Register::new(0)],
                argument_ownership: vec![ArgumentOwnership::Borrowed],
                result_ownership: ResultOwnership::Owned,
            },
        ];
        if check_system {
            code.push(Instruction::CheckSystem {
                module_name: "Facade.Options".to_string(),
            });
        }
        code.extend([
            Instruction::Nat {
                dst: Register::new(2),
                value: 7,
            },
            Instruction::Return {
                src: Register::new(2),
            },
        ]);
        validate(Program::new(
            FunctionId::new(0),
            vec![Function {
                id: FunctionId::new(0),
                arity: 0,
                parameter_ownership: Vec::new(),
                result_ownership: CallableResultOwnership::Scalar,
                register_count: 3,
                code,
            }],
        ))
        .expect("the command-options fixture is valid FLBC")
    }

    fn reset_runtime_heartbeats() {
        assert!(matches!(
            fln_vm::interpreter::execute(
                &heartbeat_program(0, false),
                VmExecutionLimits::default(),
                None,
            ),
            Outcome::Complete(VmExit::Returned(_))
        ));
    }

    #[test]
    fn public_lsp_projection_is_reachable_through_the_embeddable_facade() {
        let request = ProjectionRequest {
            epoch: DiagnosticEpoch::V4_32_0,
            mode: Mode::Sound,
            frontend: DiagnosticFrontend::Lsp,
            format: DiagnosticFormat::Lsp,
            channel: DiagnosticChannel::Protocol,
            color: DiagnosticColorPolicy::Never,
            path: DiagnosticPathPolicy::Preserve,
            ordering: DiagnosticOrderPolicy::SourcePositionV1,
        };
        let snapshot = ProjectionSnapshot::Complete {
            diagnostics: Vec::new(),
        };
        let projection = project_lsp_diagnostics(request, &snapshot)
            .expect("the registered LSP tuple projects through fln-server");
        assert_eq!(projection.disposition, ExitClass::Success);
        assert_eq!(projection.semantic, snapshot);
        assert_eq!(projection.messages.len(), 1);
        assert!(projection.messages[0].contains("\"method\":\"$/lean/diagnosticOutcome\""));
        assert!(projection.messages[0].contains("\"outcome\":\"complete\""));
        assert!(projection.messages[0].contains("\"authority\":true"));

        let wrong_frontend = ProjectionRequest {
            frontend: DiagnosticFrontend::Library,
            format: DiagnosticFormat::Typed,
            channel: DiagnosticChannel::ReturnValue,
            ..request
        };
        assert!(matches!(
            project_lsp_diagnostics(wrong_frontend, &snapshot),
            Err(ProjectionRefusal::Frontend {
                expected: DiagnosticFrontend::Lsp,
                actual: DiagnosticFrontend::Library,
            })
        ));
    }

    #[test]
    fn public_flbc_artifact_door_validates_executes_and_preserves_nonanswers() {
        let program = validate(Program::new(
            FunctionId::new(0),
            vec![Function {
                id: FunctionId::new(0),
                arity: 0,
                parameter_ownership: Vec::new(),
                result_ownership: CallableResultOwnership::Scalar,
                register_count: 1,
                code: vec![
                    Instruction::Nat {
                        dst: Register::new(0),
                        value: 41,
                    },
                    Instruction::Return {
                        src: Register::new(0),
                    },
                ],
            }],
        ))
        .expect("the public-door fixture is valid FLBC");
        let artifact = encode_canonical(&program, CodecLimits::default())
            .expect("the validated fixture has a canonical encoding");

        let Outcome::Complete(VmExit::Returned(returned)) =
            execute_flbc_artifact(&artifact, &KVMap::new(), FlbcExecutionLimits::default())
                .expect("canonical bytes pass decoder validation")
        else {
            panic!("the small valid artifact must return normally");
        };
        assert_eq!(returned.value.unbox(), 41);
        drop(returned);

        let mut malformed = artifact.clone();
        malformed[0] ^= u8::MAX;
        assert!(matches!(
            execute_flbc_artifact(&malformed, &KVMap::new(), FlbcExecutionLimits::default()),
            Err(CodecError::BadMagic)
        ));

        let mut limits = FlbcExecutionLimits::default();
        limits.vm.max_steps = 0;
        assert!(matches!(
            execute_flbc_artifact(&artifact, &KVMap::new(), limits),
            Ok(Outcome::Inconclusive(_))
        ));
    }

    #[test]
    fn public_olean_artifact_door_audits_and_decodes_real_reference_bytes() {
        let bytes = olean_fixture("Init.BinderNameHint.olean");
        let decoded = decode_olean_artifact(&bytes, OleanDecodeLimits::new(bytes.len()))
            .expect("the real pinned artifact passes every public read stage");

        assert_eq!(decoded.header.githash, fln_olean::format::PIN_COMMIT);
        assert!(decoded.walk.objects > 0);
        assert_eq!(decoded.module.constants as usize, decoded.constants.len());
        assert_eq!(decoded.constants.len(), 2);
        assert!(decoded.constants.iter().any(|constant| {
            constant.name().to_display_string() == "binderNameHint"
                && matches!(constant, ConstantInfo::Defn(_))
        }));
    }

    #[test]
    fn public_olean_write_and_ilean_doors_are_live() {
        let lean_version = super::OLEAN_PIN_TAG
            .strip_prefix('v')
            .expect("the extracted pin tag carries its v prefix");
        let encoded = super::encode_olean_module(
            super::OleanModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[],
                extra_const_names: &[],
            },
            super::OleanWriteHeader {
                version: super::OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version,
                githash: super::OLEAN_PIN_COMMIT,
                base_addr: (super::OLEAN_REGION_ALIGN as u64) * 2,
            },
            super::OleanWriteBudget::default(),
        )
        .expect("the public facade writes an empty basic module image");
        let decoded =
            decode_olean_artifact(&encoded.bytes, OleanDecodeLimits::new(encoded.bytes.len()))
                .expect("the public reader accepts the public writer's image");
        assert_eq!(decoded.module.constants, 0);
        assert!(decoded.constants.is_empty());

        let semantic = super::Ilean {
            version: super::ILEAN_VERSION,
            module: "Facade.Probe".to_owned(),
            direct_imports: Vec::new(),
            references: Default::default(),
            decls: Default::default(),
        };
        let bytes = super::encode_ilean(&semantic, super::IleanBudget::default())
            .expect("the public facade writes compact ilean JSON");
        assert_eq!(
            super::decode_ilean(&bytes, super::IleanBudget::default())
                .expect("the public facade reads its ilean JSON"),
            semantic
        );
    }

    #[test]
    fn standalone_olean_check_derives_dependency_order_and_uses_both_checkers() {
        let constants = standalone_declarations();
        let bytes = standalone_olean(&constants);
        let engine = Engine::from_environment(Environment::new());
        let outcome = engine
            .check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            )
            .expect("the import-free artifact reaches admission");
        let Outcome::Complete(checked) = outcome else {
            panic!("the fixture must complete: {outcome:?}");
        };

        let names: Vec<String> = checked
            .declarations
            .iter()
            .map(|declaration| declaration.name.to_display_string())
            .collect();
        assert_eq!(names, ["Fixture.P", "Fixture.p", "Fixture.t"]);
        assert_eq!(checked.engine.environment().len(), 3);
        assert_eq!(checked.decoded.constants, constants);
        assert_ne!(checked.base_logical_root, checked.result_logical_root);
        assert!(checked.declarations.iter().all(|declaration| {
            declaration.checker.schema == fln_checker::admit::ADMISSION_SCHEMA
        }));
    }

    #[test]
    fn standalone_olean_check_is_atomic_on_kernel_rejection() {
        let mut constants = standalone_declarations();
        let ConstantInfo::Thm(theorem) = &mut constants[0] else {
            panic!("fixture starts with its theorem")
        };
        theorem.value = Expr::sort(Level::zero());
        let bytes = standalone_olean(&constants);
        let engine = Engine::from_environment(Environment::new());
        let result = engine.check_olean_artifact(
            &bytes,
            &KVMap::new(),
            OleanCheckLimits::new(bytes.len(), test_budget()),
        );

        assert!(matches!(
            result,
            Err(OleanCheckError::Admission(
                EngineAdmissionError::BatchDeclaration { index: 2, .. }
            ))
        ));
        assert_eq!(
            engine.environment().len(),
            0,
            "a failed batch cannot expose its two successful prefixes"
        );
    }

    #[test]
    fn standalone_olean_check_refuses_unresolved_imports_and_unsupported_units() {
        let reference = olean_with_imports(
            &[],
            &[OleanModuleImport {
                module: Name::from_components(["Fixture", "Missing"]),
                import_all: false,
                is_exported: false,
                is_meta: false,
            }],
        );
        let engine = Engine::from_environment(Environment::new());
        let imported = engine.check_olean_artifact(
            &reference,
            &KVMap::new(),
            OleanCheckLimits::new(reference.len(), test_budget()),
        );
        assert!(matches!(
            imported,
            Err(OleanCheckError::ImportsRequireResolver { ref imports }) if !imports.is_empty()
        ));

        let quotient_name = Name::from_components(["Fixture", "Quot"]);
        let quotient = ConstantInfo::Quot(QuotVal {
            base: ConstantVal {
                name: quotient_name.clone(),
                level_params: Vec::new(),
                type_: Expr::sort(Level::zero()),
            },
            kind: QuotKind::Type,
        });
        let bytes = standalone_olean(&[quotient]);
        assert!(matches!(
            engine.check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            ),
            Err(OleanCheckError::UnsupportedDeclaration { name, kind: "quotient" })
                if name == quotient_name
        ));
    }

    #[test]
    fn standalone_olean_check_preserves_decode_and_planning_resource_refusals() {
        let constants = standalone_declarations();
        let bytes = standalone_olean(&constants);
        let engine = Engine::from_environment(Environment::new());
        let too_small = engine.check_olean_artifact(
            &bytes,
            &KVMap::new(),
            OleanCheckLimits::new(bytes.len() - 1, test_budget()),
        );
        assert!(matches!(
            too_small,
            Err(OleanCheckError::Decode(
                OleanDecodeError::ArtifactTooLarge { .. }
            ))
        ));

        let mut planning = OleanCheckLimits::new(bytes.len(), test_budget());
        planning.max_dependency_presentations = 0;
        assert!(matches!(
            engine.check_olean_artifact(&bytes, &KVMap::new(), planning),
            Err(OleanCheckError::DependencyPresentationLimit {
                observed: 1,
                limit: 0
            })
        ));
    }

    #[test]
    fn module_system_public_part_is_refused_before_stripped_bodies_reach_admission() {
        let bytes = olean_fixture("Init.BinderNameHint.olean");
        let decoded = decode_olean_artifact(&bytes, OleanDecodeLimits::new(bytes.len()))
            .expect("the exported module part remains inspectable on its own");
        assert!(decoded.module.is_module, "fixture must require companions");
        assert!(!decoded.companion_parts_loaded);

        let engine = Engine::from_environment(Environment::new());
        assert!(matches!(
            engine.check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            ),
            Err(OleanCheckError::MissingCompanionParts {
                module: None,
                missing_server: true,
                missing_private: true,
            })
        ));
    }

    #[test]
    fn closed_olean_module_set_resolves_imports_in_deterministic_order() {
        let constants = standalone_declarations();
        let base_name = Name::from_components(["Fixture", "Base"]);
        let child_name = Name::from_components(["Fixture", "Child"]);
        let import = OleanModuleImport {
            module: base_name.clone(),
            import_all: false,
            is_exported: false,
            is_meta: false,
        };
        let base = standalone_olean(&constants[2..]);
        let child = olean_with_imports(&constants[..2], &[import]);
        let inputs = [
            OleanModuleInput {
                name: &child_name,
                artifact: &child,
                server_artifact: None,
                private_artifact: None,
            },
            OleanModuleInput {
                name: &base_name,
                artifact: &base,
                server_artifact: None,
                private_artifact: None,
            },
        ];
        let engine = Engine::from_environment(Environment::new());
        let checked = engine
            .check_olean_modules(
                &inputs,
                &KVMap::new(),
                OleanCheckLimits::new(base.len() + child.len(), test_budget()),
            )
            .expect("the closed import graph reaches admission");
        let Outcome::Complete(checked) = checked else {
            panic!("the closed import graph must complete: {checked:?}")
        };

        assert_eq!(checked.modules.len(), 2);
        assert_eq!(checked.modules[0].name, base_name);
        assert_eq!(checked.modules[1].name, child_name);
        assert_eq!(checked.modules[0].declarations.len(), 1);
        assert_eq!(checked.modules[1].declarations.len(), 2);
        assert_eq!(checked.engine.environment().len(), 3);
        assert_eq!(
            checked.modules[0].result_logical_root,
            checked.modules[1].base_logical_root
        );
        assert_ne!(checked.base_logical_root, checked.result_logical_root);
    }

    #[test]
    fn closed_olean_module_set_refuses_missing_imports_cycles_and_aggregate_exhaustion() {
        let base_name = Name::from_components(["Fixture", "Base"]);
        let child_name = Name::from_components(["Fixture", "Child"]);
        let import_base = OleanModuleImport {
            module: base_name.clone(),
            import_all: false,
            is_exported: false,
            is_meta: false,
        };
        let child = olean_with_imports(&[], &[import_base]);
        let engine = Engine::from_environment(Environment::new());
        let child_only = [OleanModuleInput {
            name: &child_name,
            artifact: &child,
            server_artifact: None,
            private_artifact: None,
        }];
        assert!(matches!(
            engine.check_olean_modules(
                &child_only,
                &KVMap::new(),
                OleanCheckLimits::new(child.len(), test_budget()),
            ),
            Err(OleanCheckError::MissingModuleImports { module, imports })
                if module == child_name && imports == vec![base_name.clone()]
        ));

        let import_child = OleanModuleImport {
            module: child_name.clone(),
            import_all: false,
            is_exported: false,
            is_meta: false,
        };
        let base = olean_with_imports(&[], &[import_child]);
        let cycle = [
            OleanModuleInput {
                name: &base_name,
                artifact: &base,
                server_artifact: None,
                private_artifact: None,
            },
            OleanModuleInput {
                name: &child_name,
                artifact: &child,
                server_artifact: None,
                private_artifact: None,
            },
        ];
        assert!(matches!(
            engine.check_olean_modules(
                &cycle,
                &KVMap::new(),
                OleanCheckLimits::new(base.len() + child.len(), test_budget()),
            ),
            Err(OleanCheckError::ModuleImportCycle { modules }) if modules.len() == 2
        ));

        let mut exhausted = OleanCheckLimits::new(base.len() + child.len(), test_budget());
        exhausted.max_total_bytes = base.len() + child.len() - 1;
        assert!(matches!(
            engine.check_olean_modules(&cycle, &KVMap::new(), exhausted),
            Err(OleanCheckError::TotalBytesLimit { .. })
        ));
    }

    #[test]
    fn public_olean_artifact_door_preserves_malformed_input_as_a_typed_refusal() {
        let mut bytes = olean_fixture("Init.BinderNameHint.olean");
        bytes[0] ^= u8::MAX;

        assert!(matches!(
            decode_olean_artifact(&bytes, OleanDecodeLimits::new(bytes.len())),
            Err(OleanDecodeError::Region(OleanRegionError::BadMagic))
        ));
    }

    #[test]
    fn public_olean_artifact_door_enforces_byte_and_declaration_budgets() {
        let bytes = olean_fixture("Init.SizeOfLemmas.olean");
        let too_small = bytes.len() - 1;
        assert!(matches!(
            decode_olean_artifact(&bytes, OleanDecodeLimits::new(too_small)),
            Err(OleanDecodeError::ArtifactTooLarge {
                bytes: observed,
                limit,
            }) if observed == bytes.len() && limit == too_small
        ));

        let mut limits = OleanDecodeLimits::new(bytes.len());
        limits.declarations = OleanWalkBudget { max_objects: 5 };
        assert!(matches!(
            decode_olean_artifact(&bytes, limits),
            Err(OleanDecodeError::Declaration(
                OleanDeclarationError::Budget { .. }
            ))
        ));
    }

    #[test]
    fn public_olean_rebuild_door_rederives_real_reference_bytes_with_a_bound() {
        let bytes = olean_fixture("Init.BinderNameHint.olean");
        let (rebuilt, report) = rebuild_olean_artifact(&bytes, bytes.len())
            .expect("the real pinned artifact rebuilds from parsed semantics");

        assert_eq!(rebuilt, bytes);
        assert!(report.objects > 0);
        assert!(report.rederived_bytes > 0);
        assert_eq!(report.nonzero_padding_bytes, 0);
        assert!(report.findings.is_empty());

        assert!(matches!(
            rebuild_olean_artifact(&bytes, bytes.len() - 1),
            Err(OleanRebuildError::ArtifactTooLarge {
                bytes: observed,
                limit,
            }) if observed == bytes.len() && limit == bytes.len() - 1
        ));

        let mut malformed = bytes;
        malformed[0] ^= u8::MAX;
        assert!(matches!(
            rebuild_olean_artifact(&malformed, malformed.len()),
            Err(OleanRebuildError::Region(OleanRegionError::BadMagic))
        ));
    }

    fn nat_type() -> Expr {
        Expr::const_(Name::str(Name::anonymous(), "Nat"), Vec::new())
    }

    fn string_type() -> Expr {
        Expr::const_(Name::str(Name::anonymous(), "String"), Vec::new())
    }

    fn definition(name: &str, value: Expr) -> Declaration {
        typed_definition(name, nat_type(), value)
    }

    fn typed_definition(name: &str, type_: Expr, value: Expr) -> Declaration {
        let name = Name::from_components([name]);
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_,
            },
            value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name],
        })
    }

    fn axiom(name: &str) -> Declaration {
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: Name::from_components([name]),
                level_params: Vec::new(),
                type_: nat_type(),
            },
            is_unsafe: false,
        })
    }

    fn typed_axiom(name: &str, type_: Expr) -> Declaration {
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: Name::from_components([name]),
                level_params: Vec::new(),
                type_,
            },
            is_unsafe: false,
        })
    }

    fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
        let name = Name::from_components([name]);
        Declaration::Thm(TheoremVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_,
            },
            value,
            all: vec![name],
        })
    }

    fn opaque(name: &str, value: Expr) -> Declaration {
        let name = Name::from_components([name]);
        Declaration::Opaque(OpaqueVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_: nat_type(),
            },
            value,
            is_unsafe: false,
            all: vec![name],
        })
    }

    fn partial_sort_definition(name: &str, value: Expr, all: Vec<Name>) -> DefinitionVal {
        DefinitionVal {
            base: ConstantVal {
                name: Name::from_components([name]),
                level_params: Vec::new(),
                type_: Expr::sort(Level::zero()),
            },
            value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Partial,
            all,
        }
    }

    fn nested_let_definition() -> Declaration {
        definition(
            "chosen",
            Expr::let_e(
                Name::from_components(["x"]),
                nat_type(),
                Expr::lit(Literal::Nat(NatLit::from_u64(41))),
                Expr::bvar(0).expect("one local binder fits the term covenant"),
                false,
            ),
        )
    }

    fn nat_identity_definition(name: &str) -> Declaration {
        identity_definition(name, nat_type())
    }

    fn string_identity_definition(name: &str) -> Declaration {
        identity_definition(name, string_type())
    }

    fn identity_definition(name: &str, parameter_type: Expr) -> Declaration {
        let name = Name::from_components([name]);
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_: Expr::forall_e(
                    Name::from_components(["value"]),
                    parameter_type.clone(),
                    parameter_type.clone(),
                    BinderInfo::Default,
                ),
            },
            value: Expr::lam(
                Name::from_components(["value"]),
                parameter_type,
                Expr::bvar(0).expect("one first-order parameter fits the term covenant"),
                BinderInfo::Default,
            ),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name],
        })
    }

    fn first_nat_definition(name: &str) -> Declaration {
        let name = Name::from_components([name]);
        let second_type = Expr::forall_e(
            Name::from_components(["second"]),
            nat_type(),
            nat_type(),
            BinderInfo::Default,
        );
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_: Expr::forall_e(
                    Name::from_components(["first"]),
                    nat_type(),
                    second_type,
                    BinderInfo::Default,
                ),
            },
            value: Expr::lam(
                Name::from_components(["first"]),
                nat_type(),
                Expr::lam(
                    Name::from_components(["second"]),
                    nat_type(),
                    Expr::bvar(1).expect("two Nat parameters fit the term covenant"),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name],
        })
    }

    #[test]
    fn bounded_engine_executes_checked_source_and_returns_the_published_snapshot() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let base_root = engine.logical_root(&options);
        let completed = engine
            .execute_nat_definition(b"def answer := 42", &options, test_limits())
            .expect("the supported source reaches Golem");
        let Outcome::Complete(completed) = completed else {
            panic!("the small bounded run must answer completely");
        };

        assert_eq!(
            engine.environment().len(),
            1,
            "the receiver stays immutable"
        );
        assert_eq!(completed.engine.environment().len(), 2);
        assert!(
            completed
                .engine
                .environment()
                .contains(&Name::from_components(["answer"]))
        );
        assert_eq!(completed.base_logical_root, base_root);
        assert_eq!(
            completed.result_logical_root,
            completed.engine.logical_root(&options)
        );
        assert_ne!(completed.base_logical_root, completed.result_logical_root);
        assert!(!completed.flbc_artifact.is_empty());
        assert_eq!(
            completed.checker.schema,
            fln_checker::admit::ADMISSION_SCHEMA
        );
        assert_eq!(
            completed.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let VmExit::Returned(returned) = completed.exit else {
            panic!("the literal definition must return normally");
        };
        assert_eq!(value_kind(&returned.value), ValueKind::Scalar);
        assert_eq!(returned.value.unbox(), 42);
    }

    #[test]
    fn source_run_sidecar_binds_exact_product_toolchain_and_current_coordinates() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let sources: [&[u8]; 2] = [b"def first := 17", b"def answer := first"];
        let completed = engine
            .execute_nat_definitions(&sources, &options, test_limits())
            .expect("the supported batch reaches Golem")
            .into_complete()
            .expect("the bounded batch answers completely");
        let product = completed
            .executions
            .last()
            .expect("the completed batch is nonempty")
            .flbc_artifact
            .clone();
        let sidecar = super::build_source_run_flbc_sidecar(
            &sources,
            &options,
            b"exact toolchain image",
            &completed,
        )
        .expect("the current target has a standard closure");
        let bytes = super::encode_flbc_product_sidecar(&sidecar);
        let verified =
            super::verify_source_run_flbc_sidecar(&bytes, &product, b"exact toolchain image")
                .expect("the exact product closure verifies");
        assert_eq!(verified, sidecar);
        assert_eq!(verified.mode(), Mode::Sound);
        assert_eq!(verified.reproducibility(), ReproducibilityProfile::Standard);

        let mut substituted = product.clone();
        substituted[0] ^= 1;
        assert!(matches!(
            super::verify_source_run_flbc_sidecar(&bytes, &substituted, b"exact toolchain image"),
            Err(super::SourceRunSidecarVerificationError::Binding(
                super::ProductSidecarRefusal::ProductRootMismatch
            ))
        ));
        assert!(matches!(
            super::verify_source_run_flbc_sidecar(&bytes, &product, b"other toolchain image"),
            Err(super::SourceRunSidecarVerificationError::Binding(
                super::ProductSidecarRefusal::ClosureComponentMismatch {
                    component: super::ClosureComponent::Toolchain,
                }
            ))
        ));
        super::verify_source_run_flbc_sidecar(&bytes, &product, b"exact toolchain image")
            .expect("both negative controls recover on exact inputs");
    }

    #[test]
    fn bv_decide_publishes_only_the_exact_dually_checked_successor() {
        let engine = Engine::from_environment(Environment::new());
        let options = KVMap::new();
        let base_root = engine.logical_root(&options);
        let theorem = Name::from_components(["bv.facade.positive"]);
        let outcome = engine
            .decide_bv(
                bv_request(BoolExpr::Constant(true), "bv.facade.positive"),
                &options,
                EngineBvDecideLimits::new(test_budget()),
            )
            .expect("Verdict and the facade council accept the identity theorem");
        let EngineBvDecideOutcome::Proved(publication) = outcome else {
            panic!("a true proposition must produce the only successor-carrying arm");
        };

        assert!(engine.environment().is_empty(), "the receiver is immutable");
        assert_eq!(engine.logical_root(&options), base_root);
        assert_eq!(publication.base_logical_root, base_root);
        assert_eq!(
            publication.result_logical_root,
            publication.engine.logical_root(&options)
        );
        assert_ne!(publication.result_logical_root, base_root);
        assert!(publication.engine.environment().contains(&theorem));
        let candidate = publication.verdict.reflection().theorem();
        assert_eq!(&candidate.base.name, &theorem);
        assert!(matches!(
            publication.engine.environment().find(&theorem),
            Some(ConstantInfo::Thm(published)) if published == candidate
        ));
        assert_eq!(
            publication.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
    }

    #[test]
    fn bv_decide_counterexample_cancellation_and_exhaustion_have_no_successor() {
        let engine = Engine::from_environment(Environment::new());
        let options = KVMap::new();
        let before = engine.logical_root(&options);

        let counterexample = engine
            .decide_bv(
                bv_request(BoolExpr::Constant(false), "bv.facade.counterexample"),
                &options,
                EngineBvDecideLimits::new(test_budget()),
            )
            .expect("false has a completed SAT counterexample");
        assert!(matches!(
            counterexample,
            EngineBvDecideOutcome::Counterexample(_)
        ));
        assert!(counterexample.publication().is_none());

        let cancelled = std::sync::atomic::AtomicBool::new(true);
        let cancellation = engine
            .decide_bv_with_cancel(
                bv_request(BoolExpr::Constant(true), "bv.facade.cancelled"),
                &options,
                EngineBvDecideLimits::new(test_budget()),
                Some(&cancelled),
            )
            .expect("cancellation is a typed non-answer");
        assert!(matches!(
            cancellation,
            EngineBvDecideOutcome::Inconclusive(EngineBvDecideInconclusive::Verdict(
                fln_verdict::BvDecideInconclusive::Pipeline(_)
            ))
        ));
        assert!(cancellation.publication().is_none());

        let mut exhausted_limits = EngineBvDecideLimits::new(test_budget());
        exhausted_limits.verdict.bitblast.max_ast_nodes = 0;
        let exhausted = engine
            .decide_bv(
                bv_request(BoolExpr::Constant(true), "bv.facade.exhausted"),
                &options,
                exhausted_limits,
            )
            .expect("resource exhaustion is a typed non-answer");
        assert!(matches!(
            exhausted,
            EngineBvDecideOutcome::Inconclusive(EngineBvDecideInconclusive::Verdict(
                fln_verdict::BvDecideInconclusive::Bitblast(_)
            ))
        ));
        assert!(exhausted.publication().is_none());
        assert_eq!(engine.logical_root(&options), before);
        assert!(engine.environment().is_empty());
    }

    #[test]
    fn bv_decide_facade_checker_veto_is_atomic_and_recoverable() {
        let engine = Engine::from_environment(Environment::new());
        let options = KVMap::new();
        let before = engine.logical_root(&options);
        let term = fln_checker::term::TermBudget::new(0, 0).with_max_arena_nodes(0);
        let whnf = fln_checker::whnf::WhnfBudget::new(0, 0, term);
        let inference = fln_checker::infer::InferenceBudget::new(0, 0, term, term).with_whnf(whnf);
        let mut constrained = EngineBvDecideLimits::new(test_budget());
        constrained.admission.checker.admission =
            CheckerAdmissionBudget::new(inference, whnf, inference.defeq);

        let raw = fln_verdict::bv_decide(
            engine.environment(),
            bv_request(BoolExpr::Constant(true), "bv.facade.raw-candidate"),
            constrained.verdict,
        );
        assert!(matches!(raw, fln_verdict::BvDecideOutcome::Candidate(_)));
        assert!(
            engine.environment().is_empty(),
            "a raw Verdict candidate must carry no environment successor"
        );

        let error = engine
            .decide_bv(
                bv_request(BoolExpr::Constant(true), "bv.facade.vetoed"),
                &options,
                constrained,
            )
            .expect_err("the facade checker non-answer must veto the Verdict successor");
        assert!(matches!(
            error,
            EngineBvDecideError::Admission(EngineAdmissionError::CouncilHalted {
                ref summary
            }) if summary.contains("fln-checker") && summary.contains("no answer")
        ));
        assert_eq!(engine.logical_root(&options), before);
        assert!(engine.environment().is_empty());

        let recovered = engine
            .decide_bv(
                bv_request(BoolExpr::Constant(true), "bv.facade.recovered"),
                &options,
                EngineBvDecideLimits::new(test_budget()),
            )
            .expect("a veto does not poison the immutable receiver");
        assert!(matches!(recovered, EngineBvDecideOutcome::Proved(_)));
    }

    #[test]
    fn bv_decide_duplicate_is_a_refusal_without_a_second_successor() {
        let engine = Engine::from_environment(Environment::new());
        let options = KVMap::new();
        let first = engine
            .decide_bv(
                bv_request(BoolExpr::Constant(true), "bv.facade.duplicate"),
                &options,
                EngineBvDecideLimits::new(test_budget()),
            )
            .expect("the first theorem publishes");
        let EngineBvDecideOutcome::Proved(first) = first else {
            panic!("the first theorem must publish");
        };
        let successor_root = first.engine.logical_root(&options);
        let duplicate = first
            .engine
            .decide_bv(
                bv_request(BoolExpr::Constant(true), "bv.facade.duplicate"),
                &options,
                EngineBvDecideLimits::new(test_budget()),
            )
            .expect("a duplicate is a completed Verdict refusal");
        assert!(
            matches!(
                &duplicate,
                EngineBvDecideOutcome::Refused(fln_verdict::BvDecideRefusal::Reflection(
                    fln_verdict::ReflectedTheoremRefusal::Kernel {
                        class: RejectClass::AlreadyDeclared,
                        ..
                    }
                ))
            ),
            "unexpected duplicate outcome: {duplicate:?}"
        );
        assert!(duplicate.publication().is_none());
        assert_eq!(first.engine.logical_root(&options), successor_root);
        assert_eq!(first.engine.environment().len(), 1);
    }

    #[test]
    fn independent_checker_non_answer_vetoes_publication() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let before = engine.logical_root(&options);
        let term = fln_checker::term::TermBudget::new(0, 0).with_max_arena_nodes(0);
        let whnf = fln_checker::whnf::WhnfBudget::new(0, 0, term);
        let inference = fln_checker::infer::InferenceBudget::new(0, 0, term, term).with_whnf(whnf);
        let mut constrained = test_limits();
        constrained.checker.admission =
            CheckerAdmissionBudget::new(inference, whnf, inference.defeq);

        let error = engine
            .execute_nat_definition(b"def answer := 42", &options, constrained)
            .expect_err("a checker non-answer must consume the publication capability");
        assert!(matches!(
            error,
            EngineExecutionError::CouncilHalted { ref summary }
                if summary.contains("fln-checker") && summary.contains("no answer")
        ));
        assert_eq!(engine.logical_root(&options), before);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["answer"]))
        );

        let control = engine
            .execute_nat_definition(b"def answer := 42", &options, test_limits())
            .expect("the same declaration completes when the checker can answer");
        assert!(
            matches!(&control, Outcome::Complete(_)),
            "the checker control must answer completely"
        );
        let Outcome::Complete(control) = control else {
            return;
        };
        assert_eq!(
            control.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        assert!(
            control
                .engine
                .environment()
                .contains(&Name::from_components(["answer"]))
        );
    }

    #[test]
    fn retained_checker_projection_advances_under_a_single_candidate_budget() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let answer = engine
            .execute_nat_definition(b"def answer := 41", &options, test_limits())
            .expect("the first definition establishes the retained checker projection");
        assert!(
            matches!(&answer, Outcome::Complete(_)),
            "the small bounded run must answer completely"
        );
        let Outcome::Complete(answer) = answer else {
            return;
        };

        let mut candidate_only = test_limits();
        candidate_only.checker.environment = fln_checker::environment::EnvironmentBudget::new(
            u64::MAX,
            1,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            u64::MAX,
        );
        let answer_name = Name::from_components(["answer"]);
        let copy_name = Name::from_components(["copy"]);
        let copied = answer
            .engine
            .execute_definition(
                definition("copy", Expr::const_(answer_name.clone(), Vec::new())),
                &options,
                candidate_only,
            )
            .expect("a retained base leaves the one-constant budget for the candidate");
        assert!(
            matches!(&copied, Outcome::Complete(_)),
            "the retained checker projection must answer completely"
        );
        let Outcome::Complete(copied) = copied else {
            return;
        };
        assert!(copied.engine.environment().contains(&copy_name));
        assert!(
            matches!(&copied.exit, VmExit::Returned(_)),
            "the checked dependency must execute after retained admission"
        );
        let VmExit::Returned(returned) = copied.exit else {
            return;
        };
        assert_eq!(returned.value.unbox(), 41);

        let uncached = Engine::from_environment(answer.engine.environment().clone());
        let before = uncached.logical_root(&options);
        let error = uncached
            .execute_definition(
                definition("uncached", Expr::const_(answer_name, Vec::new())),
                &options,
                candidate_only,
            )
            .expect_err("the same budget cannot reconstruct a two-constant base");
        assert!(matches!(
            error,
            EngineExecutionError::CouncilHalted { ref summary }
                if summary.contains("fln-checker") && summary.contains("no answer")
        ));
        assert_eq!(uncached.logical_root(&options), before);
        assert!(
            !uncached
                .environment()
                .contains(&Name::from_components(["uncached"]))
        );
    }

    #[test]
    fn nat_seed_requires_the_independent_checker_and_recovers_atomically() {
        let term = fln_checker::term::TermBudget::new(0, 0).with_max_arena_nodes(0);
        let whnf = fln_checker::whnf::WhnfBudget::new(0, 0, term);
        let inference = fln_checker::infer::InferenceBudget::new(0, 0, term, term).with_whnf(whnf);
        let mut constrained = EngineAdmissionLimits::new(test_budget());
        constrained.checker.admission =
            CheckerAdmissionBudget::new(inference, whnf, inference.defeq);

        let error = Engine::with_nat_seed(constrained)
            .expect_err("a checker non-answer must veto even the Nat seed successor");
        assert!(matches!(
            error,
            EngineAdmissionError::CouncilHalted { ref summary }
                if summary.contains("fln-checker") && summary.contains("no answer")
        ));

        let recovered = Engine::with_nat_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the unchanged seed recovers when the checker can answer")
            .into_complete()
            .expect("the bounded seed admission answers completely");
        assert_eq!(recovered.environment().len(), 1);
        assert!(
            recovered
                .environment()
                .contains(&Name::from_components(["Nat"]))
        );

        let mut candidate_only = EngineAdmissionLimits::new(test_budget());
        candidate_only.checker.environment = fln_checker::environment::EnvironmentBudget::new(
            u64::MAX,
            1,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            u64::MAX,
        );
        let successor = recovered
            .admit_declaration(axiom("after_seed"), &KVMap::new(), candidate_only)
            .expect("the retained seed projection leaves one row for the candidate")
            .into_complete()
            .expect("the candidate admission answers completely");
        assert!(
            successor
                .engine
                .environment()
                .contains(&Name::from_components(["after_seed"]))
        );
    }

    #[test]
    fn admission_only_axioms_publish_and_retain_the_checker_projection() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let base_root = engine.logical_root(&options);
        let first = engine
            .admit_declaration(
                axiom("first_postulate"),
                &options,
                EngineAdmissionLimits::new(test_budget()),
            )
            .expect("K1 and the independent checker both admit the axiom");
        assert!(
            matches!(&first, Outcome::Complete(_)),
            "the bounded axiom admission must answer completely"
        );
        let Outcome::Complete(first) = first else {
            return;
        };

        assert_eq!(engine.logical_root(&options), base_root);
        assert_eq!(engine.environment().len(), 1, "the receiver is immutable");
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["first_postulate"]))
        );
        assert!(
            first
                .engine
                .environment()
                .contains(&Name::from_components(["first_postulate"]))
        );
        assert_eq!(first.base_logical_root, base_root);
        assert_eq!(
            first.result_logical_root,
            first.engine.logical_root(&options)
        );
        assert_eq!(first.checker.ground, CheckerAdmissionGround::AxiomPreamble);

        let mut candidate_only = EngineAdmissionLimits::new(test_budget());
        candidate_only.checker.environment = fln_checker::environment::EnvironmentBudget::new(
            u64::MAX,
            1,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            u64::MAX,
        );
        let second = first
            .engine
            .admit_declaration(axiom("second_postulate"), &options, candidate_only)
            .expect("the retained projection leaves the one-row budget for the candidate");
        assert!(
            matches!(&second, Outcome::Complete(_)),
            "the retained checker projection must answer completely"
        );
        let Outcome::Complete(second) = second else {
            return;
        };
        assert!(
            second
                .engine
                .environment()
                .contains(&Name::from_components(["second_postulate"]))
        );

        let uncached = Engine::from_environment(first.engine.environment().clone());
        let uncached_root = uncached.logical_root(&options);
        let error = uncached
            .admit_declaration(axiom("uncached_postulate"), &options, candidate_only)
            .expect_err("the same budget cannot reconstruct the multi-row base");
        assert!(matches!(
            error,
            EngineAdmissionError::CouncilHalted { ref summary }
                if summary.contains("fln-checker") && summary.contains("no answer")
        ));
        assert_eq!(uncached.logical_root(&options), uncached_root);
        assert!(
            !uncached
                .environment()
                .contains(&Name::from_components(["uncached_postulate"]))
        );
    }

    #[test]
    fn admission_only_theorems_and_opaques_are_checked_and_published() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let limits = EngineAdmissionLimits::new(test_budget());
        let base_root = engine.logical_root(&options);

        let proposition_name = Name::from_components(["P"]);
        let proposition = engine
            .admit_declaration(
                typed_axiom("P", Expr::sort(Level::zero())),
                &options,
                limits,
            )
            .expect("the proposition constant is admitted");
        let Outcome::Complete(proposition) = proposition else {
            panic!("the proposition admission must answer completely");
        };
        let proof_name = Name::from_components(["h"]);
        let proof = proposition
            .engine
            .admit_declaration(
                typed_axiom("h", Expr::const_(proposition_name.clone(), Vec::new())),
                &options,
                limits,
            )
            .expect("the proof axiom is admitted");
        let Outcome::Complete(proof) = proof else {
            panic!("the proof admission must answer completely");
        };

        let theorem_name = Name::from_components(["proved"]);
        let theorem_admission = proof
            .engine
            .admit_declaration(
                theorem(
                    "proved",
                    Expr::const_(proposition_name, Vec::new()),
                    Expr::const_(proof_name.clone(), Vec::new()),
                ),
                &options,
                limits,
            )
            .expect("K1 and the independent checker admit the theorem");
        let Outcome::Complete(theorem_admission) = theorem_admission else {
            panic!("the theorem admission must answer completely");
        };
        assert_eq!(
            theorem_admission.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        assert!(
            theorem_admission
                .engine
                .environment()
                .contains(&theorem_name)
        );
        match theorem_admission.engine.environment().find(&theorem_name) {
            Some(ConstantInfo::Thm(value)) => {
                assert_eq!(value.value, Expr::const_(proof_name, Vec::new()));
            }
            other => panic!("published theorem was not queryable as a theorem: {other:?}"),
        }

        let opaque_name = Name::from_components(["sealedNat"]);
        let opaque_admission = theorem_admission
            .engine
            .admit_declaration(
                opaque("sealedNat", Expr::lit(Literal::Nat(NatLit::from_u64(7)))),
                &options,
                limits,
            )
            .expect("K1 and the independent checker admit the opaque");
        let Outcome::Complete(opaque_admission) = opaque_admission else {
            panic!("the opaque admission must answer completely");
        };
        assert_eq!(
            opaque_admission.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        assert!(opaque_admission.engine.environment().contains(&opaque_name));
        assert!(matches!(
            opaque_admission.engine.environment().find(&opaque_name),
            Some(ConstantInfo::Opaque(value))
                if value.value == Expr::lit(Literal::Nat(NatLit::from_u64(7)))
        ));
        assert_eq!(
            opaque_admission.result_logical_root,
            opaque_admission.engine.logical_root(&options)
        );

        assert_eq!(engine.logical_root(&options), base_root);
        assert!(!engine.environment().contains(&theorem_name));
        assert!(!engine.environment().contains(&opaque_name));

        let rejected_name = Name::from_components(["notATheorem"]);
        let before_rejection = opaque_admission.engine.logical_root(&options);
        let rejection = opaque_admission
            .engine
            .admit_declaration(
                theorem(
                    "notATheorem",
                    nat_type(),
                    Expr::lit(Literal::Nat(NatLit::from_u64(9))),
                ),
                &options,
                limits,
            )
            .expect_err("a theorem whose statement is Nat is rejected");
        assert!(matches!(
            rejection,
            EngineAdmissionError::KernelRejected {
                class: RejectClass::TheoremNotProp,
                ..
            }
        ));
        assert_eq!(
            opaque_admission.engine.logical_root(&options),
            before_rejection
        );
        assert!(
            !opaque_admission
                .engine
                .environment()
                .contains(&rejected_name)
        );
    }

    #[test]
    fn admission_only_mutual_definitions_are_checked_published_and_failure_atomic() {
        let engine = Engine::from_environment(Environment::new());
        let options = KVMap::new();
        let limits = EngineAdmissionLimits::new(test_budget());
        let base_root = engine.logical_root(&options);

        let left_name = Name::from_components(["mutualLeft"]);
        let right_name = Name::from_components(["mutualRight"]);
        let members = vec![left_name.clone(), right_name.clone()];
        let left = partial_sort_definition(
            "mutualLeft",
            Expr::const_(right_name.clone(), Vec::new()),
            members.clone(),
        );
        let right = partial_sort_definition(
            "mutualRight",
            Expr::const_(left_name.clone(), Vec::new()),
            members,
        );
        let admitted = engine
            .admit_declaration(
                Declaration::Mutual(vec![left.clone(), right.clone()]),
                &options,
                limits,
            )
            .expect("K1 and the independent checker admit genuine mutual recursion");
        let Outcome::Complete(admitted) = admitted else {
            panic!("the mutual admission must answer completely");
        };

        assert_eq!(
            admitted.checker.ground,
            CheckerAdmissionGround::PartialQuarantine
        );
        assert_eq!(admitted.base_logical_root, base_root);
        assert_eq!(
            admitted.result_logical_root,
            admitted.engine.logical_root(&options)
        );
        assert_eq!(
            admitted.engine.environment().find(&left_name),
            Some(&ConstantInfo::Defn(left))
        );
        assert_eq!(
            admitted.engine.environment().find(&right_name),
            Some(&ConstantInfo::Defn(right))
        );
        assert_eq!(engine.logical_root(&options), base_root);
        assert!(engine.environment().is_empty());

        let mut candidate_only = limits;
        candidate_only.checker.environment = fln_checker::environment::EnvironmentBudget::new(
            u64::MAX,
            1,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            u64::MAX,
        );
        let follower_name = Name::from_components(["mutualFollower"]);
        let retained = admitted
            .engine
            .admit_declaration(
                typed_axiom("mutualFollower", Expr::sort(Level::zero())),
                &options,
                candidate_only,
            )
            .expect("the retained checker block leaves one-row budget for its consumer");
        let Outcome::Complete(retained) = retained else {
            panic!("the retained checker projection must answer completely");
        };
        assert!(retained.engine.environment().contains(&follower_name));

        let uncached = Engine::from_environment(admitted.engine.environment().clone());
        let uncached_name = Name::from_components(["uncachedMutualFollower"]);
        let error = uncached
            .admit_declaration(
                typed_axiom("uncachedMutualFollower", Expr::sort(Level::zero())),
                &options,
                candidate_only,
            )
            .expect_err("one row cannot reconstruct an uncached two-member checker base");
        assert!(matches!(
            error,
            EngineAdmissionError::CouncilHalted { ref summary }
                if summary.contains("fln-checker") && summary.contains("no answer")
        ));
        assert!(!uncached.environment().contains(&uncached_name));

        let bad_left_name = Name::from_components(["badMutualLeft"]);
        let bad_right_name = Name::from_components(["badMutualRight"]);
        let bad_members = vec![bad_left_name.clone(), bad_right_name.clone()];
        let good_first = partial_sort_definition(
            "badMutualLeft",
            Expr::const_(bad_right_name.clone(), Vec::new()),
            bad_members.clone(),
        );
        let bad_second =
            partial_sort_definition("badMutualRight", Expr::sort(Level::zero()), bad_members);
        let rejection = engine
            .admit_declaration(
                Declaration::Mutual(vec![good_first, bad_second]),
                &options,
                limits,
            )
            .expect_err("a late mutual-member body mismatch rejects the whole block");
        assert!(matches!(
            rejection,
            EngineAdmissionError::KernelRejected {
                class: RejectClass::DefinitionTypeMismatch,
                ..
            }
        ));
        assert_eq!(engine.logical_root(&options), base_root);
        assert!(!engine.environment().contains(&bad_left_name));
        assert!(!engine.environment().contains(&bad_right_name));
    }

    #[test]
    fn admission_batch_hides_a_valid_prefix_and_recovers_after_rejection() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let base_root = engine.logical_root(&options);
        let limits = EngineAdmissionLimits::new(test_budget());
        let declarations = [axiom("postulate"), axiom("postulate")];
        let error = engine
            .admit_declarations(&declarations, &options, limits)
            .expect_err("the duplicate second declaration aborts the whole batch");
        assert!(matches!(
            error,
            EngineAdmissionError::BatchDeclaration {
                index: 1,
                error,
            } if matches!(
                error.as_ref(),
                EngineAdmissionError::KernelRejected {
                    class: RejectClass::AlreadyDeclared,
                    ..
                }
            )
        ));
        assert_eq!(engine.logical_root(&options), base_root);
        assert_eq!(engine.environment().len(), 1);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["postulate"]))
        );

        let corrected = [axiom("first_postulate"), axiom("second_postulate")];
        let completed = engine
            .admit_declarations(&corrected, &options, limits)
            .expect("the original snapshot accepts a corrected batch");
        assert!(
            matches!(&completed, Outcome::Complete(_)),
            "the corrected batch must answer completely"
        );
        let Outcome::Complete(completed) = completed else {
            return;
        };
        assert_eq!(completed.admissions.len(), 2);
        assert_eq!(completed.engine.environment().len(), 3);
        assert_eq!(completed.base_logical_root, base_root);
        assert_eq!(
            completed.admissions[0].result_logical_root,
            completed.admissions[1].base_logical_root
        );
        assert_eq!(
            completed.result_logical_root,
            completed.engine.logical_root(&options)
        );
    }

    #[test]
    fn bounded_engine_refuses_unsupported_source_without_mutating_its_snapshot() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let before = engine.environment().clone();
        let error = engine
            .execute_nat_definition(b"theorem answer : True := trivial", &options, test_limits())
            .expect_err("unsupported syntax is an explicit frontend refusal");

        assert!(matches!(error, EngineExecutionError::Frontend(_)));
        assert_eq!(engine.environment(), &before);
        assert_eq!(engine.environment().len(), 1);
    }

    #[test]
    fn bounded_engine_reports_duplicate_kernel_refusal_without_running_golem() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let first = engine
            .execute_nat_definition(b"def answer := 42", &options, test_limits())
            .expect("first definition is accepted");
        let Outcome::Complete(first) = first else {
            panic!("the small bounded run must answer completely");
        };
        let error = first
            .engine
            .execute_nat_definition(b"def answer := 7", &options, test_limits())
            .expect_err("duplicate name must not publish or execute");

        assert!(matches!(
            error,
            EngineExecutionError::KernelRejected {
                class: RejectClass::AlreadyDeclared,
                ref message,
            } if message.contains("answer")
        ));
        assert_eq!(first.engine.environment().len(), 2);
    }

    #[test]
    fn bounded_engine_preserves_vm_resource_exhaustion_as_a_non_answer() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let mut limits = test_limits();
        limits.vm.max_steps = 0;
        let outcome = engine
            .execute_nat_definition(b"def answer := 42", &options, limits)
            .expect("resource exhaustion is not a pipeline refusal");

        assert!(matches!(outcome, Outcome::Inconclusive(_)));
        assert_eq!(
            engine.environment().len(),
            1,
            "an inconclusive run cannot expose a published successor"
        );
    }

    #[test]
    fn engine_execution_binds_max_heartbeats_from_the_same_command_options() {
        reset_runtime_heartbeats();
        let program = heartbeat_program(1_001, true);
        let mut options = KVMap::new();
        options.insert(
            Name::from_components(["maxHeartbeats"]),
            DataValue::OfNat(1),
        );
        let outcome = execute_golem_with_options(&program, &options, VmExecutionLimits::default());
        let Outcome::Inconclusive(inconclusive) = outcome else {
            panic!("one command option unit must stop at 1,001 allocation heartbeats");
        };
        assert!(matches!(
            inconclusive.cause,
            InconclusiveCause::ResourceExhausted { usage }
                if usage.allowed == 1_000
                    && usage.observed == 1_001
                    && usage.reason
                        == ResourceReason::Heartbeats {
                            consumed: 1_001,
                            limit: 1_000,
                        }
        ));
        assert!(
            inconclusive
                .progress
                .as_deref()
                .is_some_and(|progress| progress.text().contains("Facade.Options"))
        );

        options.insert(
            Name::from_components(["maxHeartbeats"]),
            DataValue::OfNat(0),
        );
        let Outcome::Complete(VmExit::Returned(returned)) =
            execute_golem_with_options(&program, &options, VmExecutionLimits::default())
        else {
            panic!("zero maxHeartbeats must leave the same command unlimited");
        };
        assert_eq!(returned.value.unbox(), 7);
        drop(returned);
        reset_runtime_heartbeats();
    }

    #[test]
    fn checked_definition_ingress_executes_the_compilers_richer_closed_subset() {
        let seeded = seeded_engine();
        let engine = Engine::from_environment(seeded.environment().clone());
        let options = KVMap::new();
        assert_eq!(engine.logical_root(&options), seeded.logical_root(&options));
        let completed = engine
            .execute_definition(nested_let_definition(), &options, test_limits())
            .expect("a checked nested let reaches the reusable engine seam");
        let Outcome::Complete(completed) = completed else {
            panic!("the small checked definition must answer completely");
        };

        assert!(
            completed
                .engine
                .environment()
                .contains(&Name::from_components(["chosen"]))
        );
        assert_eq!(
            completed.result_logical_root,
            completed.engine.logical_root(&options)
        );
        let VmExit::Returned(returned) = completed.exit else {
            panic!("the checked nested let must return normally");
        };
        assert_eq!(value_kind(&returned.value), ValueKind::Scalar);
        assert_eq!(returned.value.unbox(), 41);
    }

    #[test]
    fn checked_nat_dependencies_compile_from_the_published_environment_and_recover_after_refusal() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let answer = engine
            .execute_nat_definition(b"def answer := 41", &options, test_limits())
            .expect("the dependency is checked and published first");
        let Outcome::Complete(answer) = answer else {
            panic!("the small bounded run must answer completely");
        };

        let answer_name = Name::from_components(["answer"]);
        let copy_name = Name::from_components(["copy"]);
        let copy = definition("copy", Expr::const_(answer_name, Vec::new()));
        let before_refusal = answer.engine.logical_root(&options);
        let mut constrained = test_limits();
        constrained.ingress.fir.max_functions = 1;
        let error = answer
            .engine
            .execute_definition(copy.clone(), &options, constrained)
            .expect_err("the entry-only FIR bound cannot admit one dependency");
        assert_eq!(
            error,
            EngineExecutionError::Ingress(IngressError::ResourceLimit {
                resource: IngressResource::ProgramTables,
                limit: 0,
                observed: 1,
            })
        );
        assert_eq!(answer.engine.logical_root(&options), before_refusal);
        assert!(!answer.engine.environment().contains(&copy_name));

        let copied = answer
            .engine
            .execute_definition(copy, &options, test_limits())
            .expect("retrying with a sufficient bound compiles the checked dependency");
        let Outcome::Complete(copied) = copied else {
            panic!("the checked dependency run must answer completely");
        };
        let VmExit::Returned(returned) = &copied.exit else {
            panic!("the checked dependency must return normally");
        };
        assert_eq!(returned.value.unbox(), 41);

        let chained = copied
            .engine
            .execute_definition(
                definition("again", Expr::const_(copy_name, Vec::new())),
                &options,
                test_limits(),
            )
            .expect("transitive checked dependencies form a complete compiler catalog");
        let Outcome::Complete(chained) = chained else {
            panic!("the transitive dependency run must answer completely");
        };
        let VmExit::Returned(returned) = chained.exit else {
            panic!("the transitive checked dependency must return normally");
        };
        assert_eq!(returned.value.unbox(), 41);
        assert_eq!(chained.engine.environment().len(), 4);
    }

    #[test]
    fn checked_nat_functions_publish_execute_and_recover_after_a_bounded_refusal() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let identity = nat_identity_definition("identity");
        let identity_name = Name::from_components(["identity"]);
        let base_root = engine.logical_root(&options);

        let mut constrained = test_limits();
        constrained.ingress.max_context_depth = 0;
        let error = engine
            .execute_definition(identity.clone(), &options, constrained)
            .expect_err("the explicit zero-depth bound refuses one Nat parameter");
        assert_eq!(
            error,
            EngineExecutionError::Ingress(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: 0,
                observed: 1,
            })
        );
        assert_eq!(engine.logical_root(&options), base_root);
        assert!(!engine.environment().contains(&identity_name));

        let published = engine
            .execute_definition(identity, &options, test_limits())
            .expect("the checked Nat function is compiled as a local closure");
        let Outcome::Complete(published) = published else {
            panic!("the small checked function must answer completely");
        };
        assert!(published.engine.environment().contains(&identity_name));

        let applied = published
            .engine
            .execute_definition(
                definition(
                    "answer",
                    Expr::app(
                        Expr::const_(identity_name, Vec::new()),
                        Expr::lit(Literal::Nat(NatLit::from_u64(42))),
                    ),
                ),
                &options,
                test_limits(),
            )
            .expect("the compiler derives the function ABI from the checked environment");
        let Outcome::Complete(applied) = applied else {
            panic!("the checked function application must answer completely");
        };
        let VmExit::Returned(returned) = applied.exit else {
            panic!("the checked function application must return normally");
        };
        assert_eq!(value_kind(&returned.value), ValueKind::Scalar);
        assert_eq!(returned.value.unbox(), 42);
        assert_eq!(applied.engine.environment().len(), 3);
    }

    #[test]
    fn checked_string_functions_publish_execute_and_recover_after_a_bounded_refusal() {
        let engine = engine_with_string_type();
        let options = KVMap::new();
        let identity = string_identity_definition("stringIdentity");
        let identity_name = Name::from_components(["stringIdentity"]);
        let base_root = engine.logical_root(&options);

        let mut constrained = test_limits();
        constrained.ingress.max_context_depth = 0;
        let error = engine
            .execute_definition(identity.clone(), &options, constrained)
            .expect_err("the explicit zero-depth bound refuses one String parameter");
        assert_eq!(
            error,
            EngineExecutionError::Ingress(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: 0,
                observed: 1,
            })
        );
        assert_eq!(engine.logical_root(&options), base_root);
        assert!(!engine.environment().contains(&identity_name));

        let published = engine
            .execute_definition(identity, &options, test_limits())
            .expect("the checked String function is compiled as a local closure");
        let Outcome::Complete(published) = published else {
            panic!("the small checked String function must answer completely");
        };
        assert!(published.engine.environment().contains(&identity_name));
        assert_eq!(closed_vm_value(&published.exit), Ok(None));

        let applied = published
            .engine
            .execute_definition(
                typed_definition(
                    "message",
                    string_type(),
                    Expr::app(
                        Expr::const_(identity_name, Vec::new()),
                        Expr::lit(Literal::Str("facade-catalog".to_owned())),
                    ),
                ),
                &options,
                test_limits(),
            )
            .expect("the compiler derives the owned String ABI from the checked environment");
        let Outcome::Complete(applied) = applied else {
            panic!("the checked String function application must answer completely");
        };
        assert_eq!(
            closed_vm_value(&applied.exit),
            Ok(Some(ClosedVmValue::String("facade-catalog".to_owned())))
        );
        let VmExit::Returned(returned) = applied.exit else {
            panic!("the checked String function application must return normally");
        };
        assert_eq!(value_kind(&returned.value), ValueKind::String);
        let (size, _, _, bytes) = returned.value.string_view();
        assert!(size > 0);
        assert_eq!(bytes.get(size - 1), Some(&0));
        assert_eq!(
            std::str::from_utf8(&bytes[..size - 1]).expect("Marrow String output is UTF-8"),
            "facade-catalog"
        );
        assert_eq!(applied.engine.environment().len(), 4);

        let panicked = VmExit::Panicked {
            message: "expected example panic".to_owned(),
            usage: ExecutionUsage {
                steps: 0,
                system_polls: 0,
                peak_stack_depth: 0,
            },
        };
        assert_eq!(
            closed_vm_value(&panicked),
            Err(ClosedVmValueError::NonReturningExit)
        );
    }

    #[test]
    fn checked_string_source_batch_reaches_the_existing_runtime_catalog() {
        let options = KVMap::new();
        let nat_only = seeded_engine();
        let missing_type = nat_only
            .execute_source_definition(
                b"def message : String := \"not seeded\"",
                &options,
                test_limits(),
            )
            .expect_err("the Nat-only constructor must not silently invent String authority");
        assert!(matches!(
            missing_type,
            EngineExecutionError::KernelRejected { ref message, .. }
                if message.contains("String")
        ));

        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        assert_eq!(engine.environment().len(), 23);
        assert!(
            engine
                .environment()
                .contains(&Name::from_components(["Nat"]))
        );
        assert!(
            engine
                .environment()
                .contains(&Name::from_components(["String"]))
        );
        assert!(
            engine
                .environment()
                .contains(&Name::from_components(["Bool"]))
        );
        assert!(
            engine
                .environment()
                .contains(&Name::from_components(["Nat", "add"]))
        );
        assert!(
            engine
                .environment()
                .contains(&Name::from_components(["Nat", "sub"]))
        );
        assert!(
            engine
                .environment()
                .contains(&Name::from_components(["Nat", "mul"]))
        );
        for operation in [
            "div",
            "gcd",
            "land",
            "log2",
            "lor",
            "mod",
            "pow",
            "pred",
            "shiftLeft",
            "shiftRight",
            "xor",
        ] {
            assert!(
                engine
                    .environment()
                    .contains(&Name::from_components(["Nat", operation])),
                "source seed must contain Nat.{operation}"
            );
        }
        assert!(
            engine
                .environment()
                .contains(&Name::from_components(["String", "append"]))
        );
        assert!(
            engine
                .environment()
                .contains(&Name::from_components(["String", "length"]))
        );
        assert!(
            engine
                .environment()
                .contains(&Name::from_components(["String", "utf8ByteSize"]))
        );
        for operation in ["beq", "ble"] {
            assert!(
                engine
                    .environment()
                    .contains(&Name::from_components(["Nat", operation])),
                "source seed must contain Nat.{operation}"
            );
        }
        assert!(
            engine
                .environment()
                .contains(&Name::from_components(["String", "decEq"]))
        );

        let completed = engine
            .execute_source_definitions(
                &[
                    b"def copy (value : String) := value",
                    b"def message : String := copy \"source\\nconnected\"",
                ],
                &options,
                test_limits(),
            )
            .expect("the real source path reaches the checked String compiler catalog");
        let Outcome::Complete(completed) = completed else {
            panic!("the small String source batch must answer completely");
        };
        assert_eq!(completed.executions.len(), 2);
        let VmExit::Returned(returned) = &completed.executions[1].exit else {
            panic!("the checked String source application must return normally");
        };
        assert_eq!(value_kind(&returned.value), ValueKind::String);
        let (size, _, _, bytes) = returned.value.string_view();
        assert_eq!(bytes.get(size - 1), Some(&0));
        assert_eq!(
            std::str::from_utf8(&bytes[..size - 1]).expect("Marrow String output is UTF-8"),
            "source\nconnected"
        );
        assert_eq!(completed.engine.environment().len(), 25);
    }

    #[test]
    fn checked_nat_add_source_reaches_the_existing_intrinsic_runtime() {
        let options = KVMap::new();
        let nat_only = seeded_engine();
        let base_root = nat_only.logical_root(&options);
        let missing = nat_only
            .execute_source_definition(b"def answer := Nat.add 40 2", &options, test_limits())
            .expect_err("the Nat-only seed must not invent the Nat.add constant");
        assert!(matches!(
            missing,
            EngineExecutionError::KernelRejected {
                class: RejectClass::UnknownConstant,
                ..
            }
        ));
        assert_eq!(nat_only.logical_root(&options), base_root);
        assert!(
            !nat_only
                .environment()
                .contains(&Name::from_components(["answer"]))
        );

        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definition(b"def answer := Nat.add 40 2", &options, test_limits())
            .expect("the checked Nat.add source reaches the compiler intrinsic catalog");
        let Outcome::Complete(completed) = completed else {
            panic!("the checked Nat.add source must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.exit),
            Ok(Some(ClosedVmValue::Scalar(42)))
        );

        let executable =
            fln_comp::flbc::decode_canonical(&completed.flbc_artifact, CodecLimits::default())
                .expect("the exact executed FLBC artifact decodes canonically");
        let nat_add_row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == "Nat.add")
            .expect("the generated pin census contains Nat.add")
            .id;
        assert!(executable.functions().iter().any(|function| {
            function.code.iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::Intrinsic { row, .. } if row == nat_add_row
                )
            })
        }));
    }

    #[test]
    fn checked_nat_mul_and_sub_source_reaches_golem() {
        let options = KVMap::new();
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def product := Nat.mul 9 5",
                    b"def answer := Nat.sub product 3",
                ],
                &options,
                test_limits(),
            )
            .expect("checked Nat.mul and Nat.sub reach Golem");
        let Outcome::Complete(completed) = completed else {
            panic!("the checked Nat arithmetic must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.executions[1].exit),
            Ok(Some(ClosedVmValue::Scalar(42)))
        );

        let executable = fln_comp::flbc::decode_canonical(
            &completed.executions[1].flbc_artifact,
            CodecLimits::default(),
        )
        .expect("the exact executed FLBC artifact decodes canonically");
        for expected in ["Nat.mul", "Nat.sub"] {
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == expected)
                .expect("the generated pin census contains the arithmetic row")
                .id;
            assert!(executable.functions().iter().any(|function| {
                function.code.iter().any(|instruction| {
                    matches!(instruction, Instruction::Intrinsic { row: actual, .. } if actual == row)
                })
            }));
        }
    }

    #[test]
    fn checked_bounded_nat_rows_reach_golem_with_reference_zero_semantics() {
        let options = KVMap::new();
        let nat_only = seeded_engine();
        let base_root = nat_only.logical_root(&options);
        let missing = nat_only
            .execute_source_definition(b"def answer := Nat.pred 9", &options, test_limits())
            .expect_err("the Nat type alone must not invent Nat.pred authority");
        assert!(matches!(
            missing,
            EngineExecutionError::KernelRejected {
                class: RejectClass::UnknownConstant,
                ..
            }
        ));
        assert_eq!(nat_only.logical_root(&options), base_root);
        assert!(
            !nat_only
                .environment()
                .contains(&Name::from_components(["answer"]))
        );

        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definition(
                b"def answer := Nat.add (Nat.pred 9) (Nat.add (Nat.div 20 6) (Nat.add (Nat.mod 20 6) (Nat.add (Nat.gcd 48 18) (Nat.add (Nat.land 12 10) (Nat.add (Nat.lor 12 10) (Nat.xor 12 10))))))",
                &options,
                test_limits(),
            )
            .expect("checked bounded Nat rows reach Golem through nested applications");
        let Outcome::Complete(completed) = completed else {
            panic!("the checked bounded Nat definition must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.exit),
            Ok(Some(ClosedVmValue::Scalar(47)))
        );

        let executable =
            fln_comp::flbc::decode_canonical(&completed.flbc_artifact, CodecLimits::default())
                .expect("the exact executed bounded Nat artifact decodes canonically");
        for expected in [
            "Nat.pred", "Nat.div", "Nat.mod", "Nat.gcd", "Nat.land", "Nat.lor", "Nat.xor",
        ] {
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == expected)
                .expect("the generated pin census contains the bounded Nat row")
                .id;
            assert!(executable.functions().iter().any(|function| {
                function.code.iter().any(|instruction| {
                    matches!(instruction, Instruction::Intrinsic { row: actual, .. } if actual == row)
                })
            }));
        }

        for (source, expected) in [
            (b"def divZero := Nat.div 5 0".as_slice(), 0),
            (b"def modZero := Nat.mod 5 0".as_slice(), 5),
            (b"def gcdZero := Nat.gcd 0 5".as_slice(), 5),
        ] {
            let completed = engine
                .execute_source_definition(source, &options, test_limits())
                .expect("the checked zero case reaches Golem");
            let Outcome::Complete(completed) = completed else {
                panic!("the checked zero case must answer completely");
            };
            assert_eq!(
                closed_vm_value(&completed.exit),
                Ok(Some(ClosedVmValue::Scalar(expected)))
            );
        }
    }

    #[test]
    fn checked_nat_power_log_and_shift_rows_reach_golem() {
        let options = KVMap::new();
        let nat_only = seeded_engine();
        let base_root = nat_only.logical_root(&options);
        let missing = nat_only
            .execute_source_definition(b"def answer := Nat.log2 8", &options, test_limits())
            .expect_err("the Nat type alone must not invent Nat.log2 authority");
        assert!(matches!(
            missing,
            EngineExecutionError::KernelRejected {
                class: RejectClass::UnknownConstant,
                ..
            }
        ));
        assert_eq!(nat_only.logical_root(&options), base_root);
        assert!(
            !nat_only
                .environment()
                .contains(&Name::from_components(["answer"]))
        );

        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definition(
                b"def answer := Nat.add (Nat.pow 3 4) (Nat.add (Nat.log2 8) (Nat.add (Nat.shiftLeft 7 3) (Nat.shiftRight 56 3)))",
                &options,
                test_limits(),
            )
            .expect("checked Nat power, log, and shift rows reach Golem");
        let Outcome::Complete(completed) = completed else {
            panic!("the checked Nat power/log/shift definition must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.exit),
            Ok(Some(ClosedVmValue::Scalar(147)))
        );

        let executable =
            fln_comp::flbc::decode_canonical(&completed.flbc_artifact, CodecLimits::default())
                .expect("the exact executed Nat power/log/shift artifact decodes canonically");
        for expected in ["Nat.pow", "Nat.log2", "Nat.shiftLeft", "Nat.shiftRight"] {
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == expected)
                .expect("the generated pin census contains the Nat power/log/shift row")
                .id;
            assert!(executable.functions().iter().any(|function| {
                function.code.iter().any(|instruction| {
                    matches!(instruction, Instruction::Intrinsic { row: actual, .. } if actual == row)
                })
            }));
        }
    }

    #[test]
    fn checked_nat_mpz_results_cross_source_dependencies_and_stay_resource_typed() {
        let options = KVMap::new();
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the source seed answers completely");

        let mut limited = test_limits();
        limited.vm.max_nat_magnitude_bytes = 8;
        let stopped = engine
            .execute_source_definition(b"def tooWide := 18446744073709551616", &options, limited)
            .expect("the checked source reaches Golem before its magnitude stop");
        assert_eq!(stopped.authority(), Authority::NonAuthoritative);
        assert!(matches!(
            stopped,
            Outcome::Inconclusive(ref inconclusive)
                if matches!(
                    inconclusive.cause,
                    InconclusiveCause::ResourceExhausted { ref usage }
                        if usage.allowed == 8
                            && usage.observed == 16
                            && usage.reason == ResourceReason::Memory { limit_bytes: 8 }
                )
        ));
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["tooWide"]))
        );

        let completed = engine
            .execute_source_definitions(
                &[
                    b"def huge := 1208925819614629174706176",
                    b"def answer := Nat.add huge 194",
                ],
                &options,
                test_limits(),
            )
            .expect("a checked mpz Nat crosses the dependent source call");
        let Outcome::Complete(completed) = completed else {
            panic!("the arbitrary-precision Nat source batch must answer completely");
        };
        assert_eq!(completed.executions.len(), 2);
        assert_eq!(
            closed_vm_value(&completed.executions[0].exit),
            Ok(Some(ClosedVmValue::NonnegativeMpz(
                "1208925819614629174706176".to_owned()
            )))
        );
        assert_eq!(
            closed_vm_value(&completed.executions[1].exit),
            Ok(Some(ClosedVmValue::NonnegativeMpz(
                "1208925819614629174706370".to_owned()
            )))
        );

        let literal_executable = fln_comp::flbc::decode_canonical(
            &completed.executions[0].flbc_artifact,
            CodecLimits::default(),
        )
        .expect("the direct arbitrary-precision Nat literal artifact decodes canonically");
        assert!(literal_executable.functions().iter().any(|function| {
            function.code.iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::NatBig { limbs_le, .. } if limbs_le == &[0, 65_536]
                )
            })
        }));

        let executable = fln_comp::flbc::decode_canonical(
            &completed.executions[1].flbc_artifact,
            CodecLimits::default(),
        )
        .expect("the dependent mpz artifact decodes canonically");
        assert!(executable.functions().iter().any(|function| {
            function.result_ownership == CallableResultOwnership::OwnedOrScalar
                && function.code.iter().any(|instruction| {
                    matches!(instruction, Instruction::Intrinsic { row, .. } if row == "extern:Nat.add")
                })
        }));
    }

    #[test]
    fn parenthesized_nested_application_reaches_checked_golem_intrinsics() {
        let options = KVMap::new();
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definition(
                b"def answer := Nat.sub (Nat.mul 9 5) 3",
                &options,
                test_limits(),
            )
            .expect("a parenthesized nested application reaches the checked source path");
        let Outcome::Complete(completed) = completed else {
            panic!("the nested arithmetic definition must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.exit),
            Ok(Some(ClosedVmValue::Scalar(42)))
        );

        let executable =
            fln_comp::flbc::decode_canonical(&completed.flbc_artifact, CodecLimits::default())
                .expect("the exact executed nested-application artifact decodes canonically");
        for expected in ["Nat.mul", "Nat.sub"] {
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == expected)
                .expect("the generated pin census contains the nested arithmetic row")
                .id;
            assert!(executable.functions().iter().any(|function| {
                function.code.iter().any(|instruction| {
                    matches!(instruction, Instruction::Intrinsic { row: actual, .. } if actual == row)
                })
            }));
        }
    }

    #[test]
    fn checked_string_append_source_reaches_golem() {
        let options = KVMap::new();
        let string_only = engine_with_string_type();
        let base_root = string_only.logical_root(&options);
        let missing = string_only
            .execute_source_definition(
                b"def message := String.append \"not-\" \"seeded\"",
                &options,
                test_limits(),
            )
            .expect_err("the String-only engine must not invent String.append authority");
        assert!(matches!(
            missing,
            EngineExecutionError::KernelRejected {
                class: RejectClass::UnknownConstant,
                ..
            }
        ));
        assert_eq!(string_only.logical_root(&options), base_root);
        assert!(
            !string_only
                .environment()
                .contains(&Name::from_components(["message"]))
        );

        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definition(
                b"def message := String.append \"source-\" \"golem\"",
                &options,
                test_limits(),
            )
            .expect("checked String.append reaches Golem");
        let Outcome::Complete(completed) = completed else {
            panic!("the checked String.append must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.exit),
            Ok(Some(ClosedVmValue::String("source-golem".to_owned())))
        );
        let executable =
            fln_comp::flbc::decode_canonical(&completed.flbc_artifact, CodecLimits::default())
                .expect("the exact executed FLBC artifact decodes canonically");
        let append_row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == "String.append")
            .expect("the generated pin census contains String.append")
            .id;
        assert!(executable.functions().iter().any(|function| {
            function.code.iter().any(|instruction| {
                matches!(instruction, Instruction::Intrinsic { row, .. } if row == append_row)
            })
        }));
    }

    #[test]
    fn checked_string_length_source_distinguishes_scalars_from_utf8_bytes() {
        let options = KVMap::new();
        let string_only = engine_with_string_type();
        let base_root = string_only.logical_root(&options);
        let missing = string_only
            .execute_source_definition(
                b"def answer := String.length \"not-seeded\"",
                &options,
                test_limits(),
            )
            .expect_err("the String type alone must not invent String.length authority");
        assert!(matches!(
            missing,
            EngineExecutionError::KernelRejected {
                class: RejectClass::UnknownConstant,
                ..
            }
        ));
        assert_eq!(string_only.logical_root(&options), base_root);
        assert!(
            !string_only
                .environment()
                .contains(&Name::from_components(["answer"]))
        );

        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definition(
                b"def answer := Nat.add (String.length \"\xce\xb2eta\") (String.utf8ByteSize \"\xce\xb2eta\")",
                &options,
                test_limits(),
            )
            .expect("checked String length metrics reach Golem through nested applications");
        let Outcome::Complete(completed) = completed else {
            panic!("the checked String metric definition must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.exit),
            Ok(Some(ClosedVmValue::Scalar(9)))
        );
        let executable =
            fln_comp::flbc::decode_canonical(&completed.flbc_artifact, CodecLimits::default())
                .expect("the exact executed String metric artifact decodes canonically");
        for expected in ["String.length", "String.utf8ByteSize"] {
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == expected)
                .expect("the generated pin census contains the String metric row")
                .id;
            assert!(executable.functions().iter().any(|function| {
                function.code.iter().any(|instruction| {
                    matches!(instruction, Instruction::Intrinsic { row: actual, .. } if actual == row)
                })
            }));
        }
    }

    #[test]
    fn checked_bool_comparison_rows_reach_golem_as_scalars() {
        let options = KVMap::new();
        let unseeded = engine_with_string_type();
        let base_root = unseeded.logical_root(&options);
        let missing = unseeded
            .execute_source_definition(b"def answer := Nat.beq 42 42", &options, test_limits())
            .expect_err("the scalar types alone must not invent Nat.beq authority");
        assert!(matches!(
            missing,
            EngineExecutionError::KernelRejected {
                class: RejectClass::UnknownConstant,
                ..
            }
        ));
        assert_eq!(unseeded.logical_root(&options), base_root);
        assert!(
            !unseeded
                .environment()
                .contains(&Name::from_components(["answer"]))
        );

        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the Bool source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded Bool source seed answers completely");
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def natEq : Bool := Nat.beq 42 42",
                    b"def natLe : Bool := Nat.ble 41 42",
                    "def answer : Bool := String.decEq \"βeta\" \"βeta\"".as_bytes(),
                ],
                &options,
                test_limits(),
            )
            .expect("checked Bool comparisons reach Golem");
        let Outcome::Complete(completed) = completed else {
            panic!("the checked Bool comparison batch must answer completely");
        };
        assert_eq!(completed.executions.len(), 3);
        for execution in &completed.executions {
            assert_eq!(
                closed_vm_value(&execution.exit),
                Ok(Some(ClosedVmValue::Scalar(1)))
            );
        }

        for (execution, expected) in
            completed
                .executions
                .iter()
                .zip(["Nat.beq", "Nat.ble", "String.decEq"])
        {
            let executable =
                fln_comp::flbc::decode_canonical(&execution.flbc_artifact, CodecLimits::default())
                    .expect("the exact executed Bool comparison artifact decodes canonically");
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == expected)
                .expect("the generated pin census contains the comparison row")
                .id;
            assert!(executable.functions().iter().any(|function| {
                function.code.iter().any(|instruction| {
                    matches!(instruction, Instruction::Intrinsic { row: actual, .. } if actual == row)
                })
            }));
        }
    }

    #[test]
    fn checked_definitions_named_bool_comparisons_remain_ordinary() {
        let options = KVMap::new();
        let engine = engine_with_string_type();
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def Nat.beq (left right : Nat) : Nat := left",
                    b"def Nat.ble (left right : Nat) : Nat := right",
                    b"def String.decEq (left right : String) : String := left",
                    b"def numeric := Nat.beq (Nat.ble 1 2) 3",
                    b"def answer := String.decEq \"ordinary\" \"ignored\"",
                ],
                &options,
                test_limits(),
            )
            .expect("ordinary checked comparison names remain ordinary functions");
        let Outcome::Complete(completed) = completed else {
            panic!("the ordinary comparison batch must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.executions[3].exit),
            Ok(Some(ClosedVmValue::Scalar(2)))
        );
        assert_eq!(
            closed_vm_value(&completed.executions[4].exit),
            Ok(Some(ClosedVmValue::String("ordinary".to_owned())))
        );

        for execution in [&completed.executions[3], &completed.executions[4]] {
            let executable =
                fln_comp::flbc::decode_canonical(&execution.flbc_artifact, CodecLimits::default())
                    .expect("the exact ordinary comparison artifact decodes canonically");
            for forbidden in ["Nat.beq", "Nat.ble", "String.decEq"] {
                let row = fln_vm::extern_table_generated::EXTERN_ROWS
                    .iter()
                    .find(|row| row.name == forbidden)
                    .expect("the generated pin census contains the comparison row")
                    .id;
                assert!(executable.functions().iter().all(|function| {
                    function.code.iter().all(|instruction| {
                        !matches!(instruction, Instruction::Intrinsic { row: actual, .. } if actual == row)
                    })
                }));
            }
        }
    }

    #[test]
    fn checked_definitions_named_string_length_metrics_remain_ordinary() {
        let options = KVMap::new();
        let engine = engine_with_string_type();
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def choose (left right : Nat) : Nat := left",
                    b"def String.length (value : String) : Nat := 7",
                    b"def String.utf8ByteSize (value : String) : Nat := 8",
                    b"def answer := choose (String.length \"ordinary\") (String.utf8ByteSize \"ordinary\")",
                ],
                &options,
                test_limits(),
            )
            .expect("ordinary checked String metric names remain ordinary functions");
        let Outcome::Complete(completed) = completed else {
            panic!("the ordinary String metric batch must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.executions[3].exit),
            Ok(Some(ClosedVmValue::Scalar(7)))
        );
        let executable = fln_comp::flbc::decode_canonical(
            &completed.executions[3].flbc_artifact,
            CodecLimits::default(),
        )
        .expect("the exact executed ordinary String metric artifact decodes canonically");
        for forbidden in ["String.length", "String.utf8ByteSize"] {
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == forbidden)
                .expect("the generated pin census contains the String metric row")
                .id;
            assert!(executable.functions().iter().all(|function| {
                function.code.iter().all(|instruction| {
                    !matches!(instruction, Instruction::Intrinsic { row: actual, .. } if actual == row)
                })
            }));
        }
    }

    #[test]
    fn checked_definition_named_nat_add_is_not_replaced_by_the_seed_intrinsic() {
        let options = KVMap::new();
        let engine = seeded_engine();
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def Nat.add (left right : Nat) : Nat := left",
                    b"def answer := Nat.add 40 2",
                ],
                &options,
                test_limits(),
            )
            .expect("an ordinary checked definition named Nat.add remains an ordinary function");
        let Outcome::Complete(completed) = completed else {
            panic!("the ordinary Nat.add definition batch must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.executions[1].exit),
            Ok(Some(ClosedVmValue::Scalar(40)))
        );
        let executable = fln_comp::flbc::decode_canonical(
            &completed.executions[1].flbc_artifact,
            CodecLimits::default(),
        )
        .expect("the exact executed ordinary-function FLBC decodes canonically");
        let nat_add_row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == "Nat.add")
            .expect("the generated pin census contains Nat.add")
            .id;
        assert!(executable.functions().iter().all(|function| {
            function.code.iter().all(|instruction| {
                !matches!(
                    instruction,
                    Instruction::Intrinsic { row, .. } if row == nat_add_row
                )
            })
        }));
    }

    #[test]
    fn checked_definitions_named_nat_mul_and_sub_are_not_replaced_by_seed_intrinsics() {
        let options = KVMap::new();
        let engine = seeded_engine();
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def Nat.mul (left right : Nat) : Nat := left",
                    b"def Nat.sub (left right : Nat) : Nat := right",
                    b"def answer := Nat.sub (Nat.mul 40 2) 3",
                ],
                &options,
                test_limits(),
            )
            .expect("ordinary checked arithmetic names remain ordinary functions");
        let Outcome::Complete(completed) = completed else {
            panic!("the ordinary arithmetic definition batch must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.executions[2].exit),
            Ok(Some(ClosedVmValue::Scalar(3)))
        );
        let executable = fln_comp::flbc::decode_canonical(
            &completed.executions[2].flbc_artifact,
            CodecLimits::default(),
        )
        .expect("the exact executed ordinary-function FLBC decodes canonically");
        for forbidden in ["Nat.mul", "Nat.sub"] {
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == forbidden)
                .expect("the generated pin census contains the arithmetic row")
                .id;
            assert!(executable.functions().iter().all(|function| {
                function.code.iter().all(|instruction| {
                    !matches!(instruction, Instruction::Intrinsic { row: actual, .. } if actual == row)
                })
            }));
        }
    }

    #[test]
    fn checked_definitions_named_bounded_nat_rows_remain_ordinary() {
        let options = KVMap::new();
        let engine = seeded_engine();
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def Nat.pred (value : Nat) : Nat := value",
                    b"def Nat.div (left right : Nat) : Nat := left",
                    b"def Nat.mod (left right : Nat) : Nat := left",
                    b"def Nat.gcd (left right : Nat) : Nat := left",
                    b"def Nat.land (left right : Nat) : Nat := left",
                    b"def Nat.lor (left right : Nat) : Nat := left",
                    b"def Nat.xor (left right : Nat) : Nat := left",
                    b"def Nat.pow (left right : Nat) : Nat := left",
                    b"def Nat.log2 (value : Nat) : Nat := value",
                    b"def Nat.shiftLeft (left right : Nat) : Nat := left",
                    b"def Nat.shiftRight (left right : Nat) : Nat := left",
                    b"def answer := Nat.shiftRight (Nat.shiftLeft (Nat.log2 (Nat.pow (Nat.xor (Nat.lor (Nat.land (Nat.gcd (Nat.mod (Nat.div (Nat.pred 1) 2) 3) 4) 5) 6) 7) 8)) 9) 10",
                ],
                &options,
                test_limits(),
            )
            .expect("ordinary checked bounded Nat names remain ordinary functions");
        let Outcome::Complete(completed) = completed else {
            panic!("the ordinary bounded Nat batch must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.executions[11].exit),
            Ok(Some(ClosedVmValue::Scalar(1)))
        );
        let executable = fln_comp::flbc::decode_canonical(
            &completed.executions[11].flbc_artifact,
            CodecLimits::default(),
        )
        .expect("the exact executed ordinary bounded Nat artifact decodes canonically");
        for forbidden in [
            "Nat.pred",
            "Nat.div",
            "Nat.mod",
            "Nat.gcd",
            "Nat.land",
            "Nat.lor",
            "Nat.xor",
            "Nat.pow",
            "Nat.log2",
            "Nat.shiftLeft",
            "Nat.shiftRight",
        ] {
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == forbidden)
                .expect("the generated pin census contains the bounded Nat row")
                .id;
            assert!(executable.functions().iter().all(|function| {
                function.code.iter().all(|instruction| {
                    !matches!(instruction, Instruction::Intrinsic { row: actual, .. } if actual == row)
                })
            }));
        }
    }

    #[test]
    fn checked_definition_named_string_append_is_not_replaced_by_the_seed_intrinsic() {
        let options = KVMap::new();
        let engine = engine_with_string_type();
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def String.append (left right : String) : String := left",
                    b"def message := String.append (String.append \"ordinary\" \"ignored\") \"intrinsic\"",
                ],
                &options,
                test_limits(),
            )
            .expect("an ordinary checked String.append remains an ordinary function");
        let Outcome::Complete(completed) = completed else {
            panic!("the ordinary String.append definition batch must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.executions[1].exit),
            Ok(Some(ClosedVmValue::String("ordinary".to_owned())))
        );
        let executable = fln_comp::flbc::decode_canonical(
            &completed.executions[1].flbc_artifact,
            CodecLimits::default(),
        )
        .expect("the exact executed ordinary-function FLBC decodes canonically");
        let append_row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == "String.append")
            .expect("the generated pin census contains String.append")
            .id;
        assert!(executable.functions().iter().all(|function| {
            function.code.iter().all(|instruction| {
                !matches!(instruction, Instruction::Intrinsic { row, .. } if row == append_row)
            })
        }));
    }

    #[test]
    fn inferred_string_application_executes_on_the_source_door() {
        let options = KVMap::new();
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def copy (value : String) := value",
                    b"def message := copy \"inferred\"",
                ],
                &options,
                test_limits(),
            )
            .expect("an un-ascribed String application must not be stamped Nat");
        let Outcome::Complete(completed) = completed else {
            panic!("the inferred String application batch must answer completely");
        };
        assert_eq!(completed.executions.len(), 2);
        assert_eq!(
            closed_vm_value(&completed.executions[1].exit),
            Ok(Some(ClosedVmValue::String("inferred".to_owned())))
        );
    }

    #[test]
    fn explicit_source_let_type_executes_and_a_mismatch_publishes_nothing() {
        let options = KVMap::new();
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let base_root = engine.logical_root(&options);
        let broken_name = Name::from_components(["broken"]);

        let mismatch = engine
            .execute_source_definition(
                b"def broken := let value : Nat := \"wrong\"; value",
                &options,
                test_limits(),
            )
            .expect_err("K1 must check an explicit let type against its value");
        assert!(
            matches!(
                &mismatch,
                EngineExecutionError::KernelRejected {
                    class: RejectClass::TypeMismatch,
                    ..
                }
            ),
            "unexpected explicit let mismatch: {mismatch:?}"
        );
        assert_eq!(engine.logical_root(&options), base_root);
        assert!(!engine.environment().contains(&broken_name));

        let completed = engine
            .execute_source_definitions(
                &[
                    b"def copy (value : String) := value",
                    b"def message := let value : String := copy \"typed\"; value",
                ],
                &options,
                test_limits(),
            )
            .expect("a corrected explicitly typed let recovers on the same engine");
        let Outcome::Complete(completed) = completed else {
            panic!("the explicitly typed String let batch must answer completely");
        };
        assert_eq!(completed.executions.len(), 2);
        assert_eq!(
            closed_vm_value(&completed.executions[1].exit),
            Ok(Some(ClosedVmValue::String("typed".to_owned())))
        );
    }

    #[test]
    fn inferred_function_alias_is_callable_on_the_source_door() {
        let options = KVMap::new();
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def copy (value : String) := value",
                    b"def alias := copy",
                    b"def message := alias \"via-alias\"",
                ],
                &options,
                test_limits(),
            )
            .expect("an un-ascribed function alias must stay a String function, not Nat");
        let Outcome::Complete(completed) = completed else {
            panic!("the function-alias batch must answer completely");
        };
        assert_eq!(completed.executions.len(), 3);
        assert_eq!(
            closed_vm_value(&completed.executions[2].exit),
            Ok(Some(ClosedVmValue::String("via-alias".to_owned())))
        );
    }

    #[test]
    fn returning_a_function_from_a_parameter_is_eta_applied() {
        let options = KVMap::new();
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def copy (value : String) := value",
                    b"def wrap (ignored : String) := copy",
                    b"def message := wrap \"ignored\" \"kept\"",
                ],
                &options,
                test_limits(),
            )
            .expect("fun ignored => copy must compile as fun ignored value => copy value");
        let Outcome::Complete(completed) = completed else {
            panic!("the function-returning wrapper batch must answer completely");
        };
        assert_eq!(completed.executions.len(), 3);
        assert_eq!(
            closed_vm_value(&completed.executions[2].exit),
            Ok(Some(ClosedVmValue::String("kept".to_owned())))
        );
    }

    #[test]
    fn partial_application_of_a_checked_function_eta_lifts_used_binders() {
        let options = KVMap::new();
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def first (x y : Nat) := x",
                    b"def apply (n : Nat) := first n",
                    b"def answer := apply 17 2",
                ],
                &options,
                test_limits(),
            )
            .expect("fun n => first n must compile as fun n y => first n y");
        let Outcome::Complete(completed) = completed else {
            panic!("the partial-application batch must answer completely");
        };
        assert_eq!(completed.executions.len(), 3);
        assert_eq!(
            closed_vm_value(&completed.executions[2].exit),
            Ok(Some(ClosedVmValue::Scalar(17)))
        );
    }

    #[test]
    fn checked_runtime_catalog_refuses_unmapped_types_without_publishing() {
        let engine = engine_with_string_type();
        let options = KVMap::new();
        let token_type = Expr::const_(Name::from_components(["Token"]), Vec::new());
        let admitted = engine
            .admit_declaration(
                typed_axiom("Token", Expr::sort(Level::one())),
                &options,
                EngineAdmissionLimits::new(test_budget()),
            )
            .expect("the opaque test type reaches both council seats")
            .into_complete()
            .expect("the bounded opaque type admission answers completely");
        let base_root = admitted.engine.logical_root(&options);
        let name = Name::from_components(["tokenIdentity"]);

        let error = admitted
            .engine
            .execute_definition(
                identity_definition("tokenIdentity", token_type),
                &options,
                test_limits(),
            )
            .expect_err("an unmapped source type has no invented runtime ABI");
        assert!(matches!(
            error,
            EngineExecutionError::Ingress(IngressError::UnknownLambda { .. })
        ));
        assert_eq!(admitted.engine.logical_root(&options), base_root);
        assert!(!admitted.engine.environment().contains(&name));
    }

    #[test]
    fn checked_multi_parameter_nat_function_preserves_argument_order() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let first_name = Name::from_components(["first"]);
        let published = engine
            .execute_definition(first_nat_definition("first"), &options, test_limits())
            .expect("the two-parameter checked function is executable");
        let Outcome::Complete(published) = published else {
            panic!("the small checked function must answer completely");
        };

        let call = Expr::app(
            Expr::app(
                Expr::const_(first_name, Vec::new()),
                Expr::lit(Literal::Nat(NatLit::from_u64(17))),
            ),
            Expr::lit(Literal::Nat(NatLit::from_u64(29))),
        );
        let selected = published
            .engine
            .execute_definition(definition("selected", call), &options, test_limits())
            .expect("the environment-derived two-parameter catalog entry compiles");
        let Outcome::Complete(selected) = selected else {
            panic!("the checked function application must answer completely");
        };
        let VmExit::Returned(returned) = selected.exit else {
            panic!("the checked function application must return normally");
        };
        assert_eq!(returned.value.unbox(), 17);
    }

    #[test]
    fn bounded_source_calls_checked_nat_functions_and_recovers_after_an_argument_bound() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let published = engine
            .execute_definition(first_nat_definition("first"), &options, test_limits())
            .expect("the checked two-parameter function publishes");
        let Outcome::Complete(published) = published else {
            panic!("the small checked function must answer completely");
        };
        let base_root = published.engine.logical_root(&options);
        let selected_name = Name::from_components(["selected"]);

        let mut constrained = test_limits();
        constrained.ingress.max_application_args = 1;
        let error = published
            .engine
            .execute_nat_definition(b"def selected := first 17 29", &options, constrained)
            .expect_err("two source arguments exceed the explicit one-argument bound");
        assert_eq!(
            error,
            EngineExecutionError::Ingress(IngressError::ResourceLimit {
                resource: IngressResource::ApplicationArguments,
                limit: 1,
                observed: 2,
            })
        );
        assert_eq!(published.engine.logical_root(&options), base_root);
        assert!(!published.engine.environment().contains(&selected_name));

        let selected = published
            .engine
            .execute_nat_definition(b"def selected := first 17 29", &options, test_limits())
            .expect("the same source application recovers under sufficient bounds");
        let Outcome::Complete(selected) = selected else {
            panic!("the bounded source call must answer completely");
        };
        let VmExit::Returned(returned) = selected.exit else {
            panic!("the bounded source call must return normally");
        };
        assert_eq!(returned.value.unbox(), 17);
        assert!(selected.engine.environment().contains(&selected_name));
    }

    #[test]
    fn checked_definition_batch_publishes_a_function_and_dependent_call_atomically() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let identity_name = Name::from_components(["identity"]);
        let declarations = [
            nat_identity_definition("identity"),
            definition(
                "answer",
                Expr::app(
                    Expr::const_(identity_name.clone(), Vec::new()),
                    Expr::lit(Literal::Nat(NatLit::from_u64(42))),
                ),
            ),
        ];
        let completed = engine
            .execute_definitions(&declarations, &options, test_limits())
            .expect("the elaborated project uses the checked batch door");
        let Outcome::Complete(completed) = completed else {
            panic!("the small checked project must answer completely");
        };

        assert_eq!(completed.executions.len(), 2);
        assert_eq!(completed.engine.environment().len(), 3);
        assert_eq!(completed.base_logical_root, engine.logical_root(&options));
        assert_eq!(
            completed.executions[0].result_logical_root,
            completed.executions[1].base_logical_root
        );
        assert!(completed.engine.environment().contains(&identity_name));
        assert!(
            completed
                .engine
                .environment()
                .contains(&Name::from_components(["answer"]))
        );
        let VmExit::Returned(returned) = &completed.executions[1].exit else {
            panic!("the dependent checked definition must return normally");
        };
        assert_eq!(value_kind(&returned.value), ValueKind::Scalar);
        assert_eq!(returned.value.unbox(), 42);
    }

    #[test]
    fn checked_definition_batch_hides_partial_progress_and_recovers_after_refusal() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let base_root = engine.logical_root(&options);
        let empty: [Declaration; 0] = [];
        assert_eq!(
            engine
                .execute_definitions(&empty, &options, test_limits())
                .expect_err("an empty elaborated project is not a successful batch"),
            EngineExecutionError::EmptyBatch
        );

        let postulate_name = Name::from_components(["postulate"]);
        let declarations = [
            definition("answer", Expr::lit(Literal::Nat(NatLit::from_u64(42)))),
            Declaration::Axiom(AxiomVal {
                base: ConstantVal {
                    name: postulate_name.clone(),
                    level_params: Vec::new(),
                    type_: nat_type(),
                },
                is_unsafe: false,
            }),
        ];
        let error = engine
            .execute_definitions(&declarations, &options, test_limits())
            .expect_err("a declaration without executable content aborts the project");
        assert!(matches!(
            error,
            EngineExecutionError::BatchCommand {
                index: 1,
                error,
            } if matches!(
                error.as_ref(),
                EngineExecutionError::UnsupportedDeclaration { kind: "axiom" }
            )
        ));
        assert_eq!(engine.logical_root(&options), base_root);
        assert_eq!(engine.environment().len(), 1);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["answer"]))
        );
        assert!(!engine.environment().contains(&postulate_name));

        let recovered = engine
            .execute_definitions(&declarations[..1], &options, test_limits())
            .expect("the original snapshot accepts a corrected retry");
        let Outcome::Complete(recovered) = recovered else {
            panic!("the corrected project must answer completely");
        };
        assert_eq!(recovered.engine.environment().len(), 2);
        let VmExit::Returned(returned) = &recovered.executions[0].exit else {
            panic!("the recovered checked definition must return normally");
        };
        assert_eq!(returned.value.unbox(), 42);
    }

    #[test]
    fn checked_definition_ingress_refuses_non_executable_declarations_atomically() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let base_root = engine.logical_root(&options);
        let declaration = Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: Name::from_components(["postulate"]),
                level_params: Vec::new(),
                type_: nat_type(),
            },
            is_unsafe: false,
        });
        let error = engine
            .execute_definition(declaration, &options, test_limits())
            .expect_err("an axiom has no executable body");

        assert_eq!(
            error,
            EngineExecutionError::UnsupportedDeclaration { kind: "axiom" }
        );
        assert_eq!(engine.logical_root(&options), base_root);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["postulate"]))
        );
    }

    #[test]
    fn checked_definition_ingress_hides_a_successor_when_compilation_refuses() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let base_root = engine.logical_root(&options);
        let name = Name::from_components(["universe"]);
        let declaration = Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            value: Expr::sort(Level::zero()),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name.clone()],
        });
        let error = engine
            .execute_definition(declaration, &options, test_limits())
            .expect_err("K1 accepts the sort definition but compiler ingress refuses it");

        assert!(matches!(error, EngineExecutionError::Ingress(_)));
        assert_eq!(engine.logical_root(&options), base_root);
        assert!(!engine.environment().contains(&name));
    }

    #[test]
    fn bounded_source_batch_chains_real_root_transitions_in_order() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let sources: [&[u8]; 2] = [b"def first := 1", b"def second := first"];
        let completed = engine
            .execute_nat_definitions(&sources, &options, test_limits())
            .expect("both supported commands execute");
        let Outcome::Complete(completed) = completed else {
            panic!("the small bounded batch must answer completely");
        };

        assert_eq!(completed.executions.len(), 2);
        assert_eq!(completed.engine.environment().len(), 3);
        assert_eq!(completed.base_logical_root, engine.logical_root(&options));
        assert_eq!(
            completed.executions[0].result_logical_root,
            completed.executions[1].base_logical_root
        );
        assert_eq!(
            completed.result_logical_root,
            completed.engine.logical_root(&options)
        );
        let VmExit::Returned(returned) = &completed.executions[1].exit else {
            panic!("the dependent second definition must return normally");
        };
        assert_eq!(returned.value.unbox(), 1);
    }

    #[test]
    fn bounded_source_batch_flattens_multiple_commands_in_one_file() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let sources: [&[u8]; 1] = [
            b"-- def hidden\r\ndef first (x y : Nat) : Nat := x\r\ndef selected : Nat := first 17 29",
        ];
        let completed = engine
            .execute_nat_definitions(&sources, &options, test_limits())
            .expect("both commands in the file execute");
        let Outcome::Complete(completed) = completed else {
            panic!("the bounded source file must answer completely");
        };

        assert_eq!(completed.executions.len(), 2);
        assert_eq!(completed.engine.environment().len(), 3);
        assert_eq!(
            completed.executions[0].result_logical_root,
            completed.executions[1].base_logical_root
        );
        let VmExit::Returned(returned) = &completed.executions[1].exit else {
            panic!("the dependent command must return normally");
        };
        assert_eq!(returned.value.unbox(), 17);
    }

    #[test]
    fn bounded_source_batch_rebases_later_parse_refusals_to_the_file() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let base_root = engine.logical_root(&options);
        let sources: [&[u8]; 1] = [b"def first := 1\r\ndef second : String := first"];
        let error = engine
            .execute_nat_definitions(&sources, &options, test_limits())
            .expect_err("the unsupported second result type must abort the file");

        assert!(matches!(
            error,
            EngineExecutionError::BatchCommand {
                index: 1,
                error,
            } if matches!(
                error.as_ref(),
                EngineExecutionError::Frontend(NatDefinitionFrontendError::Parse(
                    fln_parse::NatDefinitionParseError::OutsideSeedGrammar { at, .. }
                )) if at.0 == 29
            )
        ));
        assert_eq!(engine.logical_root(&options), base_root);
        assert_eq!(engine.environment().len(), 1);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["first"]))
        );
    }

    #[test]
    fn bounded_source_batch_composes_first_order_nat_functions_through_a_let_chain() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let sources: [&[u8]; 3] = [
            b"def first (x y : Nat) : Nat := x",
            b"def choose (x : Nat) : Nat := first x 29",
            b"def selected : Nat := let input := 17; let copied := input; choose copied",
        ];
        let completed = engine
            .execute_nat_definitions(&sources, &options, test_limits())
            .expect("composed source-defined functions execute atomically");
        let Outcome::Complete(completed) = completed else {
            panic!("the bounded source project must answer completely");
        };

        assert_eq!(completed.executions.len(), 3);
        assert!(
            completed
                .engine
                .environment()
                .contains(&Name::from_components(["first"]))
        );
        assert!(
            completed
                .engine
                .environment()
                .contains(&Name::from_components(["choose"]))
        );
        assert!(
            completed
                .engine
                .environment()
                .contains(&Name::from_components(["selected"]))
        );
        let VmExit::Returned(returned) = &completed.executions[2].exit else {
            panic!("the source call must return normally");
        };
        assert_eq!(returned.value.unbox(), 17);
    }

    #[test]
    fn bounded_source_batch_exposes_no_successor_after_a_later_refusal() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let base_root = engine.logical_root(&options);
        let empty: [&[u8]; 0] = [];
        assert_eq!(
            engine
                .execute_nat_definitions(&empty, &options, test_limits())
                .expect_err("a zero-command batch is not a successful project"),
            EngineExecutionError::EmptyBatch
        );

        let sources: [&[u8]; 2] = [b"def answer := 1", b"def answer := 2"];
        let error = engine
            .execute_nat_definitions(&sources, &options, test_limits())
            .expect_err("the duplicate second command must abort the batch");
        assert!(matches!(
            error,
            EngineExecutionError::BatchCommand {
                index: 1,
                error,
            } if matches!(
                error.as_ref(),
                EngineExecutionError::KernelRejected {
                    class: RejectClass::AlreadyDeclared,
                    ..
                }
            )
        ));
        assert_eq!(engine.logical_root(&options), base_root);
        assert_eq!(engine.environment().len(), 1);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["answer"]))
        );
    }
}
