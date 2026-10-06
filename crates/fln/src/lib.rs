//! **fln** — the embeddable library facade (plan §17.2).
//!
//! The first live surfaces are the typed diagnostic return adapter (bead
//! `franken_lean-wlan`) and a bounded, real engine path (bead `franken_lean-7kc`)
//! from a bounded exact Nat/String/Bool definition, checked scalar intrinsics,
//! pin-precedence scalar infix syntax (including bounded Nat/String `==`), or first-order application
//! source, or from an already-elaborated definition, through Crucible, the compiler's validated
//! FIR and canonical FLBC, and Golem. The source path is deliberately the
//! implemented grammar subset, not a claim of general Lean elaboration or
//! Prelude support. Already-elaborated axioms, definitions, theorems, opaques,
//! non-safe mutual definition blocks, fixed quotient initialization, and a
//! bounded class of nonrecursive `Type` inductives can also advance an immutable
//! engine snapshot through admission and publication without compiling or
//! executing a body. Embedders can also validate and execute an existing canonical FLBC
//! artifact without reaching into the compiler or VM crates, and inspect or
//! re-derive a real pinned-format `.olean` through the codec's audited reader.
//! Verdict's proof-producing `bv_decide` pipeline is also available through an
//! atomic engine transition whose theorem must survive both Verdict's proof
//! replay/K1 path and the facade's independent-checker council. A standalone
//! bounded `#check`, or one terminal check after a closed definition-only source
//! graph, can use those same two checker seats in a discarded scratch successor,
//! returning its checked type without publishing, compiling, or executing the
//! queried term. Lantern's typed
//! LSP diagnostic projection is reachable here as a pure protocol adapter; the
//! long-lived server transport remains a separate, unfinished product surface.

#![forbid(unsafe_code)]
// The one unstable feature, for one hook: a refused host allocation must unwind
// to the frontier's per-module guard instead of aborting every thread at once
// (fln-frontier-oom-abort-w9dx; see `install_host_allocation_failure_hook`).
#![feature(alloc_error_hook)]

mod olean_imports;
pub mod source_check;
mod source_execution;
#[cfg(test)]
mod source_nat_add_binding_tests;
mod source_records;
#[cfg(test)]
mod source_seed_names;
pub use source_check::{SourceCheckError, SourceCheckLimits, SourceFileCheck};

pub use fln_checker::admit::{
    AdmissionBudget as CheckerAdmissionBudget, AdmissionGround as CheckerAdmissionGround,
};
use fln_checker::admit::{
    BlockVerdict as CheckerBlockVerdict, InductiveVerdict as CheckerInductiveVerdict,
    QuotientVerdict as CheckerQuotientVerdict, Verdict as CheckerVerdict,
};
pub use fln_checker::environment::EnvironmentBudget as CheckerEnvironmentBudget;
use fln_checker::environment::{
    ConstantDeclaration as CheckerConstantDeclaration, ConstantEntry as CheckerConstantEntry,
    ConstantEnvironment as CheckerConstantEnvironment, ConstantKind as CheckerConstantKind,
    ConstantSafety as CheckerConstantSafety,
    ConstructorDeclaration as CheckerConstructorDeclaration,
    DefinitionBody as CheckerDefinitionBody, DefinitionSafety as CheckerDefinitionSafety,
    EnvironmentOutcome as CheckerEnvironmentOutcome,
    InductiveDeclaration as CheckerInductiveDeclaration, QuotientKind as CheckerQuotientKind,
    RecursorDeclaration as CheckerRecursorDeclaration, RecursorRule as CheckerRecursorRule,
    ReducibilityHint as CheckerReducibilityHint,
};
pub use fln_checker::wire::DecodeBudget as CheckerDecodeBudget;
use fln_checker::wire::{
    DecodeOutcome as CheckerDecodeOutcome, WireExpr as CheckerExpr, WireName as CheckerName,
    decode_expr_dag as checker_decode_expr_dag, decode_name as checker_decode_name,
};
pub use fln_comp::fir::LoweringError;
use fln_comp::fir::ValueType;
use fln_comp::flbc::CallableResultOwnership;
pub use fln_comp::flbc::{CodecError, CodecLimits, ValidatedProgram};
use fln_comp::ingress::{
    FunctionBinding, IngressResource, IntrinsicBinding, LambdaBinding, LambdaRecursion,
};
mod runtime;
pub use fln_comp::ingress::{IngressError, IngressLimits, ScalarConstructorBinding};
pub use fln_core::diag::{
    DiagnosticChannel, DiagnosticColorPolicy, DiagnosticEpoch, DiagnosticFormat,
    DiagnosticFrontend, DiagnosticOrderPolicy, DiagnosticPathPolicy, ExitClass, ProjectionRefusal,
    ProjectionRequest, ProjectionSnapshot, RelatedSpan, Severity, StructuredDiagnostic,
    StructuredInconclusive, StructuredInternalFault,
};
pub use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal, NatLit};
pub use fln_core::level::Level;
pub use fln_core::mode::{
    BuildProfileId, CgsePolicyId, ClosureComponent, ContentRoot, DeterminismClass, EpochId, Mode,
    ReproducibilityProfile, TargetId,
};
pub use fln_core::name::{LeafView, Name};
pub use fln_core::options::{DataValue, KVMap};
pub use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
pub use fln_elab::{
    DefinitionFrontendError, NatDefinitionFrontendError, seed::SeedEnvironmentError,
};
pub use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal,
    InductiveVal, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints,
    TheoremVal,
};
pub use fln_env::environment::{DeclarationBudget, Environment};
use fln_env::environment::{DeclarationCommitted, EnvironmentEntry};
pub use fln_env::module_apply::{
    AppliedExtensionRangeWitness, AppliedModulePayload, ExtensionPayload, ModuleApplyCheckpoint,
    ModuleApplyPrepareError, ModuleApplyState, ModuleApplyStateError, ModuleApplyTransactionId,
};
pub use fln_env::modules::{CancellationProbe, ModuleEpoch, ModuleGraph, ModuleId};
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
pub use fln_kernel::verdict::{Budget, EngineId, RejectClass};
pub use fln_olean::artifact::{
    ArtifactByteHash, ArtifactError, ArtifactIdentityPlane, ArtifactLimits, ArtifactMemberInput,
    ArtifactMemberRecord, ArtifactPointer, ArtifactPublication, ArtifactResource,
    ArtifactSemanticHash, ArtifactSetManifest, ArtifactSetRoot, ArtifactStore,
    ArtifactStoreDirectory, AtomicCreateError, AtomicCreateStep, BoundArtifactSet, InjectedIoError,
    PublicationControl, PublicationIoPoint, PublicationPoint, ResolvedArtifactSet,
    SCHEMA_ARTIFACT_SET_MANIFEST, StagedArtifactSet, artifact_byte_hash, artifact_semantic_hash,
    publish_file_atomic, publish_file_atomic_new,
};
pub use fln_olean::decl::DeclError as OleanDeclarationError;
use fln_olean::decl::{DeclDecoder, verify_private_superset};
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
pub use fln_parse::{
    DefinitionParseError, ParsedSourceCommand, PartitionedSourceModule, SourceCommandKind,
    parse_source_command, partition_source_module,
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
    InvalidFloatRepresentation { source_type: &'static str },
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
            Self::InvalidFloatRepresentation { source_type } => write!(
                formatter,
                "returned {source_type} did not use its boxed scalar representation"
            ),
        }
    }
}

impl std::error::Error for ClosedVmValueError {}

/// The exact bits of a typed source floating-point result. Keeping the bits
/// preserves signed zero and allows stable equality even for NaN results.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClosedFloatValue {
    Float(u64),
    Float32(u32),
}

impl fmt::Display for ClosedFloatValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let value = match *self {
            Self::Float(bits) => f64::from_bits(bits),
            Self::Float32(bits) => f64::from(f32::from_bits(bits)),
        };
        if value.is_nan() {
            formatter.write_str("NaN")
        } else {
            write!(formatter, "{value:.6}")
        }
    }
}

/// Project a floating-point result using its checked source runtime type.
///
/// Float boxes share their physical layout with other scalar boxes; the
/// untyped [`closed_vm_value`] therefore deliberately does not guess their
/// type. Pass the `runtime_type` carried by a source execution here. Unknown
/// types return `Ok(None)` and malformed boxes return a typed error.
pub fn closed_float_value(
    runtime_type: &Expr,
    exit: &VmExit,
) -> Result<Option<ClosedFloatValue>, ClosedVmValueError> {
    let ExprNode::Const { name, levels } = runtime_type.node() else {
        return Ok(None);
    };
    if !levels.is_empty() {
        return Ok(None);
    }
    let source_type = if name == &Name::from_components(["Float"]) {
        "Float"
    } else if name == &Name::from_components(["Float32"]) {
        "Float32"
    } else {
        return Ok(None);
    };
    let VmExit::Returned(returned) = exit else {
        return Err(ClosedVmValueError::NonReturningExit);
    };
    let value = &returned.value;
    let error = ClosedVmValueError::InvalidFloatRepresentation { source_type };
    if value.is_scalar() || value.header().tag != 0 || value.header().other != 0 {
        return Err(error);
    }
    if source_type == "Float" {
        value.try_ctor_scalar_u64(0).map(ClosedFloatValue::Float)
    } else {
        value.try_ctor_scalar_u32(0).map(ClosedFloatValue::Float32)
    }
    .map(Some)
    .ok_or(error)
}

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
    closed_obj_value(&returned.value)
}

/// [`closed_vm_value`] for one runtime object, returned or nested in one.
fn closed_obj_value(value: &fln_rt::obj::Obj) -> Result<Option<ClosedVmValue>, ClosedVmValueError> {
    if value.is_scalar() {
        return Ok(Some(ClosedVmValue::Scalar(value.unbox())));
    }
    if vm_value_kind(value) == VmValueKind::Mpz {
        return Ok(nat_decimal(value).map(ClosedVmValue::NonnegativeMpz));
    }
    if vm_value_kind(value) != VmValueKind::String {
        return Ok(None);
    }

    // `string_view` asserts. This door is embedder-facing: a hostile
    // header must be a typed `ClosedVmValueError`, never a process death.
    let Some((size, _, _, bytes)) = value.try_string_view() else {
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

/// How a closed result is read, decided by its source type: `Nat`, `String`, `Bool`, or a
/// `List` of one of these, nested to any depth. A list cannot be read without its type, since
/// `List.nil` and the `Nat` zero are the same boxed scalar.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClosedValueShape {
    Nat,
    String,
    Bool,
    List(Box<ClosedValueShape>),
}

/// A closed result read under a [`ClosedValueShape`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClosedShapedValue {
    /// Exact decimal digits.
    Nat(String),
    String(String),
    Bool(bool),
    List(Vec<ClosedShapedValue>),
}

/// Why a returned value could not be read under its shape. Distinct from
/// [`ClosedVmValueError`], whose String rules the leaves still apply.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClosedShapedValueError {
    Value(ClosedVmValueError),
    /// The value is not the shape's runtime representation: for example a `List` cell that is
    /// neither the boxed `List.nil` nor a two-field `List.cons` constructor, or a `Bool` scalar
    /// other than 0 or 1.
    Representation {
        expected: &'static str,
    },
    /// More cells and leaves than the caller allows.
    TooLarge {
        limit: usize,
    },
}

impl fmt::Display for ClosedShapedValueError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(error) => error.fmt(formatter),
            Self::Representation { expected } => {
                write!(formatter, "returned value is not a runtime {expected}")
            }
            Self::TooLarge { limit } => {
                write!(
                    formatter,
                    "returned value has more than {limit} cells and leaves"
                )
            }
        }
    }
}

impl std::error::Error for ClosedShapedValueError {}

/// Read a returned value under `shape`, visiting at most `max_nodes` list cells and leaves.
/// Iterative: neither a long list nor a deeply nested one recurses on the host stack.
/// `List.nil` is the boxed scalar 0 (the Marrow ABI's form) or a fieldless constructor object
/// with tag 0 (the form Golem's compiled code builds, measured 2026-10-06), and `List.cons h t`
/// a constructor object with tag 1 and exactly the two object fields `h` and `t`; anything else
/// is a typed refusal.
pub fn closed_vm_shaped_value(
    exit: &VmExit,
    shape: &ClosedValueShape,
    max_nodes: usize,
) -> Result<ClosedShapedValue, ClosedShapedValueError> {
    enum Task<'a> {
        Read(fln_rt::obj::Obj, &'a ClosedValueShape),
        Collect(usize),
    }
    let VmExit::Returned(returned) = exit else {
        return Err(ClosedShapedValueError::Value(
            ClosedVmValueError::NonReturningExit,
        ));
    };
    let mut budget = max_nodes;
    let mut spend = || {
        budget = budget
            .checked_sub(1)
            .ok_or(ClosedShapedValueError::TooLarge { limit: max_nodes })?;
        Ok::<(), ClosedShapedValueError>(())
    };
    let mut tasks = vec![Task::Read(returned.value.clone_ref(), shape)];
    let mut values: Vec<ClosedShapedValue> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Read(value, ClosedValueShape::List(element)) => {
                let mut heads = Vec::new();
                let mut cell = value;
                loop {
                    spend()?;
                    if cell.is_scalar() {
                        if cell.unbox() != 0 {
                            return Err(ClosedShapedValueError::Representation {
                                expected: "List",
                            });
                        }
                        break;
                    }
                    // Golem's compiled code also builds `List.nil` as a fieldless tag-0 object.
                    if vm_value_kind(&cell) == VmValueKind::Ctor(0) && cell.header().other == 0 {
                        break;
                    }
                    let cons = vm_value_kind(&cell) == VmValueKind::Ctor(1)
                        && cell.try_ctor_child(2).is_none();
                    let (Some(head), Some(tail), true) =
                        (cell.try_ctor_child(0), cell.try_ctor_child(1), cons)
                    else {
                        return Err(ClosedShapedValueError::Representation { expected: "List" });
                    };
                    heads.push(head);
                    cell = tail;
                }
                tasks.push(Task::Collect(heads.len()));
                for head in heads.into_iter().rev() {
                    tasks.push(Task::Read(head, element));
                }
            }
            Task::Read(value, leaf) => {
                spend()?;
                let read = closed_obj_value(&value).map_err(ClosedShapedValueError::Value)?;
                values.push(match (leaf, read) {
                    (ClosedValueShape::Nat, Some(ClosedVmValue::Scalar(n))) => {
                        ClosedShapedValue::Nat(n.to_string())
                    }
                    (ClosedValueShape::Nat, Some(ClosedVmValue::NonnegativeMpz(digits))) => {
                        ClosedShapedValue::Nat(digits)
                    }
                    (ClosedValueShape::String, Some(ClosedVmValue::String(text))) => {
                        ClosedShapedValue::String(text)
                    }
                    (ClosedValueShape::Bool, Some(ClosedVmValue::Scalar(0))) => {
                        ClosedShapedValue::Bool(false)
                    }
                    (ClosedValueShape::Bool, Some(ClosedVmValue::Scalar(1))) => {
                        ClosedShapedValue::Bool(true)
                    }
                    (ClosedValueShape::Nat, _) => {
                        return Err(ClosedShapedValueError::Representation { expected: "Nat" });
                    }
                    (ClosedValueShape::String, _) => {
                        return Err(ClosedShapedValueError::Representation { expected: "String" });
                    }
                    (ClosedValueShape::Bool, _) => {
                        return Err(ClosedShapedValueError::Representation { expected: "Bool" });
                    }
                    // List shapes are read by the arm above; this one only completes the match.
                    (ClosedValueShape::List(_), _) => {
                        return Err(ClosedShapedValueError::Representation { expected: "List" });
                    }
                });
            }
            Task::Collect(count) => {
                let start = values
                    .len()
                    .checked_sub(count)
                    .ok_or(ClosedShapedValueError::Representation { expected: "List" })?;
                let items = values.split_off(start);
                values.push(ClosedShapedValue::List(items));
            }
        }
    }
    match (values.pop(), values.is_empty()) {
        (Some(value), true) => Ok(value),
        _ => Err(ClosedShapedValueError::Representation {
            expected: "closed value",
        }),
    }
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
    /// The independent checker's own reading of the same bytes (bead
    /// `franken_lean-z8j.1.14`): what the checker seat compares every declaration
    /// it is asked to judge against.
    pub independent: IndependentReading,
    /// Whether the authoritative module-system server and private parts were
    /// loaded in addition to the exported public part.
    pub companion_parts_loaded: bool,
}

/// The independent checker's own reading of an artifact (bead
/// `franken_lean-z8j.1.14`), made by `fln_checker::olean` from the bytes, never from
/// `fln-olean`'s decoded values: each constant's name and reading digest in table
/// order, or why the checker could not read the artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IndependentReading {
    Read(Vec<(CheckerName, fln_hash::domain::Digest)>),
    Unread(String),
}

/// The checker's reading of `parts` (`[X.olean]`, or the module-system chain
/// `[X.olean, X.olean.server, X.olean.private]`), from their bytes alone.
///
/// This is the whole of the checker's `.olean` input path, and it is public so the
/// linker can measure that: `fln-conformance`'s `checker-reader-probe` references
/// nothing else, and its test refuses any `fln-core`, `fln-olean`, `fln-env`,
/// `fln-rt` or `fln-kernel` function the linker keeps reachable from here.
pub fn independent_reading(parts: &[&[u8]], limits: OleanDecodeLimits) -> IndependentReading {
    match fln_checker::olean::read_constants(parts, limits.declarations.max_objects) {
        Ok(reading) => IndependentReading::Read(
            reading
                .constants
                .iter()
                .map(|constant| (constant.name().clone(), constant.reading_digest()))
                .collect(),
        ),
        Err(error) => IndependentReading::Unread(error.to_string()),
    }
}

/// The checker's own reading of one artifact, by name, as its seat consults it.
struct ArtifactReadings(std::collections::HashMap<CheckerName, fln_hash::domain::Digest>);

/// Why the checker seat will not vouch for a declaration as the artifact's.
enum ReadingObjection {
    /// Its reading of the artifact says something else: one decoder is wrong, and
    /// a council must not agree on either reading.
    Differs(String),
    /// The declaration under review could not be projected for comparison.
    Unprojected(String),
}

impl ReadingObjection {
    fn review(&self) -> CheckerReview {
        match self {
            Self::Differs(detail) => CheckerReview::from_seat(
                SeatVerdict::Disagrees {
                    detail: detail.clone(),
                },
                None,
                None,
            ),
            Self::Unprojected(reason) => CheckerReview::no_answer(reason.clone()),
        }
    }
}

fn checker_name_text(name: &CheckerName) -> String {
    let parts: Vec<String> = name
        .parts()
        .iter()
        .map(|part| match part {
            fln_checker::wire::NamePart::Text(text) => text.clone(),
            fln_checker::wire::NamePart::Numeric { value, .. } => value.to_string(),
        })
        .collect();
    parts.join(".")
}

impl ArtifactReadings {
    /// Index a reading, or say why there is none to consult. An artifact the
    /// checker could not read, or that names one constant twice, gives it no
    /// independent answer about any of its declarations.
    fn new(reading: &IndependentReading) -> Result<Self, String> {
        let entries = match reading {
            IndependentReading::Read(entries) => entries,
            IndependentReading::Unread(reason) => {
                return Err(format!(
                    "fln-checker could not read the .olean itself: {reason}"
                ));
            }
        };
        let mut readings = std::collections::HashMap::new();
        readings
            .try_reserve(entries.len())
            .map_err(|_| format!("could not reserve {} checker readings", entries.len()))?;
        for (name, digest) in entries {
            if readings.insert(name.clone(), *digest).is_some() {
                return Err(format!(
                    "fln-checker read `{}` twice in one .olean",
                    checker_name_text(name)
                ));
            }
        }
        Ok(Self(readings))
    }

    /// The objection to judging `candidate` as the artifact's declaration of its name.
    fn objection_to(&self, candidate: &CheckerConstantEntry) -> Option<ReadingObjection> {
        let name = checker_name_text(candidate.name());
        match self.0.get(candidate.name()) {
            Some(digest) if *digest == candidate.reading_digest() => None,
            Some(_) => Some(ReadingObjection::Differs(format!(
                "fln-checker's own reading of the .olean declares `{name}` differently from the \
                 declaration under review"
            ))),
            None => Some(ReadingObjection::Differs(format!(
                "fln-checker's own reading of the .olean declares no `{name}`"
            ))),
        }
    }

    /// [`Self::objection_to`] for a primary-decoded constant.
    fn objection(
        &self,
        info: &ConstantInfo,
        budget: CheckerDecodeBudget,
    ) -> Option<ReadingObjection> {
        match checker_entry(info, budget) {
            Ok(candidate) => self.objection_to(&candidate),
            Err(detail) => Some(ReadingObjection::Unprojected(format!(
                "projection of `{}` into fln-checker failed: {detail}",
                info.name().to_display_string()
            ))),
        }
    }
}

/// A reading objection to a declaration no council reviews: a difference refuses
/// the module as a seat's disagreement would, and a failed projection leaves it
/// without an independent answer.
fn unreviewed_reading_refusal<T>(
    name: &Name,
    objection: ReadingObjection,
) -> Result<Outcome<T>, OleanCheckError> {
    match objection {
        ReadingObjection::Differs(detail) => Err(OleanCheckError::IndependentReadingDiffers {
            name: name.clone(),
            detail,
        }),
        ReadingObjection::Unprojected(reason) => Ok(Outcome::Inconclusive(
            Inconclusive::dependency_unavailable(reason),
        )),
    }
}

/// What the checker seat compares the declaration under review against (bead
/// `franken_lean-z8j.1.14`).
#[derive(Clone, Copy)]
enum ReadingCheck<'a> {
    /// A source declaration: no artifact was read, so there is nothing to compare.
    Unread,
    /// An `.olean` declaration: every candidate must be the artifact's declaration
    /// of its name in the checker's own reading.
    Artifact(&'a ArtifactReadings),
    /// Already compared by the caller, as the artifact states the declaration: a
    /// subsumed repeat is renamed before its council sees it.
    Settled(Option<&'a ReadingObjection>),
}

/// The seat's review when a candidate is not what its own reading says, else
/// `None` and the seat goes on to judge.
fn reading_review(
    candidates: &[CheckerConstantEntry],
    reading: ReadingCheck<'_>,
) -> Option<CheckerReview> {
    match reading {
        ReadingCheck::Unread => None,
        ReadingCheck::Settled(objection) => objection.map(ReadingObjection::review),
        ReadingCheck::Artifact(readings) => candidates
            .iter()
            .find_map(|candidate| readings.objection_to(candidate))
            .map(|objection| objection.review()),
    }
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
    /// A part's fixed header is not the pinned toolchain's: its `flags`, `githash`
    /// or `lean_version` differ (bead `fln-fur.1`). `part` is `None` for the
    /// exported `.olean`.
    HeaderNotPinned {
        part: Option<OleanCompanionPart>,
        mismatch: fln_olean::pin::HeaderPinMismatch,
    },
}

/// Refuse a part whose header is not the pinned toolchain's, before any further
/// decoding: the pinned loader refuses such a file as an "incompatible header".
fn require_pinned_header(
    file: &[u8],
    part: Option<OleanCompanionPart>,
) -> Result<(), OleanDecodeError> {
    fln_olean::pin::check_pinned_header(file)
        .map_err(|mismatch| OleanDecodeError::HeaderNotPinned { part, mismatch })
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
            Self::HeaderNotPinned {
                part: None,
                mismatch,
            } => write!(f, "incompatible .olean header: {mismatch}"),
            Self::HeaderNotPinned {
                part: Some(part),
                mismatch,
            } => write!(f, "incompatible {part} header: {mismatch}"),
        }
    }
}

impl std::error::Error for OleanDecodeError {}

impl OleanDecodeError {
    /// Whether this refusal is solely an explicit byte/object budget, or the host
    /// refusing a decode reservation, rather than malformed input or a
    /// companion-chain identity failure.
    ///
    /// A host refusal was reported as a decode `Budget` until fln-s97y gave it its
    /// own variant; it stays in this class so the CLI's non-answer exit is unchanged.
    pub const fn is_resource_exhaustion(&self) -> bool {
        self.is_host_allocation_refusal()
            || matches!(
                self,
                Self::ArtifactTooLarge { .. }
                    | Self::Region(
                        OleanRegionError::BudgetExhausted { .. }
                            | OleanRegionError::PayloadBudgetExhausted { .. }
                    )
                    | Self::Declaration(OleanDeclarationError::Budget { .. })
                    | Self::Declaration(OleanDeclarationError::Region(
                        OleanRegionError::BudgetExhausted { .. }
                            | OleanRegionError::PayloadBudgetExhausted { .. }
                    ))
                    | Self::CompanionRegion {
                        error: OleanRegionError::BudgetExhausted { .. }
                            | OleanRegionError::PayloadBudgetExhausted { .. },
                        ..
                    }
                    | Self::Declaration(OleanDeclarationError::ChainTooLarge { .. })
                    | Self::CompanionDeclaration {
                        error: OleanDeclarationError::Budget { .. }
                            | OleanDeclarationError::ChainTooLarge { .. },
                        ..
                    }
                    | Self::CompanionDeclaration {
                        error: OleanDeclarationError::Region(
                            OleanRegionError::BudgetExhausted { .. }
                                | OleanRegionError::PayloadBudgetExhausted { .. }
                        ),
                        ..
                    }
            )
    }

    /// The construct the decoder stopped at because it does not interpret it yet,
    /// when that is the whole reason: a limit of this implementation, not a fault in
    /// the input (FL-INV-07). Today that is a `Name.num` whose component needs an
    /// `mpz`.
    pub fn unsupported_construct(&self) -> Option<&'static str> {
        match self {
            Self::Declaration(OleanDeclarationError::Unsupported { what, .. })
            | Self::CompanionDeclaration {
                error: OleanDeclarationError::Unsupported { what, .. },
                ..
            } => Some(what),
            _ => None,
        }
    }

    /// Whether the host refused a reservation the decoder needed: a non-answer
    /// about this host, never a property of the input.
    pub const fn is_host_allocation_refusal(&self) -> bool {
        matches!(
            self,
            Self::Declaration(OleanDeclarationError::AllocationRefused { .. })
                | Self::CompanionDeclaration {
                    error: OleanDeclarationError::AllocationRefused { .. },
                    ..
                }
        )
    }

    /// The allowance this decode stop exceeded and what had been spent, when it is an
    /// explicit byte or object budget whose own numbers show it was exceeded
    /// (bead fln-s97y). The frontier reports such a stop as a typed resource
    /// exhaustion instead of a failed module. `None` for every other refusal, and
    /// for a budget error whose numbers do not show an overrun: a stop that cannot
    /// show its allowance is not reported as one.
    pub fn resource_usage(&self) -> Option<fln_core::outcome::ResourceUsage> {
        use fln_core::diag::{ResourceReason, StructuralUnit};
        let to_u64 = |value: usize| u64::try_from(value).unwrap_or(u64::MAX);
        let usage = |unit, allowed: u64, observed: u64| fln_core::outcome::ResourceUsage {
            reason: ResourceReason::StructuralBudget { unit },
            allowed,
            observed,
        };
        let region = |error: &OleanRegionError| match error {
            OleanRegionError::BudgetExhausted { visited, budget } => {
                Some(usage(StructuralUnit::ProducedNodes, *budget, *visited))
            }
            OleanRegionError::PayloadBudgetExhausted { required, budget } => Some(usage(
                StructuralUnit::InputBytes,
                to_u64(*budget),
                to_u64(*required),
            )),
            _ => None,
        };
        let declaration = |error: &OleanDeclarationError| match error {
            OleanDeclarationError::Budget { visited, budget } => {
                Some(usage(StructuralUnit::ProducedNodes, *budget, *visited))
            }
            OleanDeclarationError::ChainTooLarge { bytes, limit } => Some(usage(
                StructuralUnit::InputBytes,
                to_u64(*limit),
                to_u64(*bytes),
            )),
            OleanDeclarationError::Region(error) => region(error),
            _ => None,
        };
        let usage = match self {
            Self::ArtifactTooLarge { bytes, limit } => Some(usage(
                StructuralUnit::InputBytes,
                to_u64(*limit),
                to_u64(*bytes),
            )),
            Self::Region(error) | Self::CompanionRegion { error, .. } => region(error),
            Self::Declaration(error) | Self::CompanionDeclaration { error, .. } => {
                declaration(error)
            }
            _ => None,
        };
        usage.filter(fln_core::outcome::ResourceUsage::is_genuine_exhaustion)
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

/// One physical part of a module image, in the Reference's load order: the
/// exported `.olean`, then `.olean.server`, then `.olean.private`
/// (`saveModuleDataParts` writes them in that order, and each later part is
/// compacted against the earlier ones).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OleanModulePart {
    Exported,
    Server,
    Private,
}

impl OleanModulePart {
    /// Every part, in load order.
    pub const LOAD_ORDER: [Self; 3] = [Self::Exported, Self::Server, Self::Private];

    /// What the Reference appends to the exported file name to name this part
    /// (`OLeanLevel.adjustFileName`): nothing, `.server`, or `.private`.
    pub const fn file_suffix(self) -> &'static str {
        match self {
            Self::Exported => "",
            Self::Server => ".server",
            Self::Private => ".private",
        }
    }
}

impl fmt::Display for OleanModulePart {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Exported => ".olean",
            Self::Server => ".olean.server",
            Self::Private => ".olean.private",
        })
    }
}

/// Typed refusal from the public pinned `.olean` rebuild path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OleanRebuildError {
    /// The artifact, or a module chain's parts together, exceed the byte bound.
    ArtifactTooLarge { bytes: usize, limit: usize },
    /// A standalone artifact refused by the region rebuild.
    Region(OleanRegionError),
    /// One part of a module chain refused by the region rebuild, in the
    /// address space of the parts loaded before it.
    PartRegion {
        part: OleanModulePart,
        error: OleanRegionError,
    },
    /// `part` was supplied without `missing`, a part the Reference loads
    /// before it. A companion stores pointers into its predecessors, so it
    /// cannot be rebuilt without them.
    MissingPredecessor {
        part: OleanModulePart,
        missing: OleanModulePart,
    },
    /// `part`'s fixed header is not the pinned toolchain's: its `flags`,
    /// `githash` or `lean_version` differ (bead `fln-fur.1`). A standalone
    /// artifact is named [`OleanModulePart::Exported`]. The rebuild re-derives
    /// these fields from their parsed values, so without this a forged header
    /// rebuilds byte-identically and is reported as verified.
    HeaderNotPinned {
        part: OleanModulePart,
        mismatch: fln_olean::pin::HeaderPinMismatch,
    },
}

/// Refuse a part the pinned toolchain did not write before re-deriving it, in
/// the order every pinned decode door uses: the envelope first, so a malformed
/// file is still refused as itself, then the header. `region` maps an envelope
/// refusal to the caller's error shape.
fn require_pinned_rebuild_header(
    bytes: &[u8],
    part: OleanModulePart,
    region: impl FnOnce(OleanRegionError) -> OleanRebuildError,
) -> Result<(), OleanRebuildError> {
    OleanView::parse(bytes).map_err(region)?;
    fln_olean::pin::check_pinned_header(bytes)
        .map_err(|mismatch| OleanRebuildError::HeaderNotPinned { part, mismatch })
}

impl fmt::Display for OleanRebuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ArtifactTooLarge { bytes, limit } => {
                write!(f, ".olean artifact has {bytes} bytes; limit is {limit}")
            }
            Self::Region(error) => write!(f, ".olean rebuild: {error}"),
            Self::PartRegion { part, error } => write!(f, "{part} rebuild: {error}"),
            Self::MissingPredecessor { part, missing } => write!(
                f,
                "{part} cannot be rebuilt without its predecessor {missing}, the part \
                 it was compacted after"
            ),
            Self::HeaderNotPinned { part, mismatch } => {
                write!(f, "incompatible {part} header: {mismatch}")
            }
        }
    }
}

impl std::error::Error for OleanRebuildError {}

impl OleanRebuildError {
    /// Whether this refusal is solely an explicit byte/object budget rather
    /// than malformed or incomplete input.
    pub const fn is_resource_exhaustion(&self) -> bool {
        matches!(
            self,
            Self::ArtifactTooLarge { .. }
                | Self::Region(
                    OleanRegionError::BudgetExhausted { .. }
                        | OleanRegionError::PayloadBudgetExhausted { .. }
                )
                | Self::PartRegion {
                    error: OleanRegionError::BudgetExhausted { .. }
                        | OleanRegionError::PayloadBudgetExhausted { .. },
                    ..
                }
        )
    }
}

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
///
/// The artifact must be a standalone region. A module-system companion
/// (`.olean.server`, `.olean.private`) points into the parts written before
/// it and is refused here; rebuild it with [`rebuild_olean_module_artifacts`].
///
/// A header the pinned toolchain did not write is refused as
/// [`OleanRebuildError::HeaderNotPinned`] before anything is rebuilt.
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
    require_pinned_rebuild_header(
        artifact,
        OleanModulePart::Exported,
        OleanRebuildError::Region,
    )?;
    fln_olean::rebuild::rebuild(artifact).map_err(OleanRebuildError::from)
}

/// The physical parts of one module image handed to
/// [`rebuild_olean_module_artifacts`]. The exported `.olean` is required; a
/// companion is supplied only when the caller has it.
#[derive(Debug, Clone, Copy)]
pub struct OleanModuleParts<'a> {
    pub exported: &'a [u8],
    pub server: Option<&'a [u8]>,
    pub private: Option<&'a [u8]>,
}

/// One re-derived physical part of a module image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OleanPartRebuild {
    pub part: OleanModulePart,
    pub bytes: Vec<u8>,
    pub report: OleanRebuildReport,
}

/// Re-derive every supplied part of one module image, in load order.
///
/// This is [`rebuild_olean_artifact`]'s door for module-system chains. Each
/// part is rebuilt in the address space the Reference loads it in: the
/// exported part alone, `.olean.server` against the exported part, and
/// `.olean.private` against both. Bytes a part owns are re-derived exactly as
/// for a standalone image; a pointer into an earlier part is re-derived from
/// its validated address there, and the object it names is left to the part
/// that owns it. The result has one entry per supplied part, in load order, and
/// the caller compares each entry's bytes with that part's input.
///
/// Supplied parts must be a load-order prefix, the shape the Reference's
/// `readModuleDataParts` accepts: a private part without the server part is
/// [`OleanRebuildError::MissingPredecessor`]. `max_bytes` bounds the supplied
/// parts together and is checked before any parsing. A region refusal names
/// the part it came from, and the first refusal in load order stops the
/// rebuild. Like [`rebuild_olean_artifact`], this is not fresh emission, does
/// not resolve imports or kernel-check declarations, and does not establish
/// that the parts came from one build. Every part's header is held to the pin
/// before that part is rebuilt, and a refusal names the part
/// ([`OleanRebuildError::HeaderNotPinned`]).
pub fn rebuild_olean_module_artifacts(
    parts: OleanModuleParts<'_>,
    max_bytes: usize,
) -> Result<Vec<OleanPartRebuild>, OleanRebuildError> {
    if parts.private.is_some() && parts.server.is_none() {
        return Err(OleanRebuildError::MissingPredecessor {
            part: OleanModulePart::Private,
            missing: OleanModulePart::Server,
        });
    }
    let supplied: Vec<(OleanModulePart, &[u8])> = [
        (OleanModulePart::Exported, Some(parts.exported)),
        (OleanModulePart::Server, parts.server),
        (OleanModulePart::Private, parts.private),
    ]
    .into_iter()
    .filter_map(|(part, bytes)| bytes.map(|bytes| (part, bytes)))
    .collect();
    let bytes = supplied
        .iter()
        .try_fold(0_usize, |total, (_, bytes)| total.checked_add(bytes.len()))
        .ok_or(OleanRebuildError::ArtifactTooLarge {
            bytes: usize::MAX,
            limit: max_bytes,
        })?;
    if bytes > max_bytes {
        return Err(OleanRebuildError::ArtifactTooLarge {
            bytes,
            limit: max_bytes,
        });
    }
    // Each part sees exactly the parts loaded before it, never itself or a
    // later one.
    let mut loaded: Vec<&[u8]> = Vec::with_capacity(supplied.len());
    let mut rebuilt = Vec::with_capacity(supplied.len());
    for (part, bytes) in supplied {
        require_pinned_rebuild_header(bytes, part, |error| OleanRebuildError::PartRegion {
            part,
            error,
        })?;
        let (part_bytes, report) = fln_olean::rebuild::rebuild_with_dependencies(bytes, &loaded)
            .map_err(|error| OleanRebuildError::PartRegion { part, error })?;
        rebuilt.push(OleanPartRebuild {
            part,
            bytes: part_bytes,
            report,
        });
        loaded.push(bytes);
    }
    Ok(rebuilt)
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
    require_pinned_header(artifact, None)?;
    view.shared_audit()?;
    let walk = view.walk(limits.graph)?;
    let module = view.module_data(limits.module)?;
    let constants = DeclDecoder::new(&view, limits.declarations).decode_module_constants()?;

    Ok(DecodedOlean {
        header: view.header.clone(),
        walk,
        module,
        constants,
        independent: independent_reading(&[artifact], limits),
        companion_parts_loaded: false,
    })
}

/// The direct imports of one `.olean`, read from its exported part without
/// decoding its declarations: enough to compute an import closure before
/// deciding which artifacts to read in full.
pub fn olean_module_imports(
    artifact: &[u8],
    limits: OleanDecodeLimits,
) -> Result<Vec<Name>, OleanDecodeError> {
    if artifact.len() > limits.max_bytes {
        return Err(OleanDecodeError::ArtifactTooLarge {
            bytes: artifact.len(),
            limit: limits.max_bytes,
        });
    }
    let view = OleanView::parse(artifact)?;
    require_pinned_header(artifact, None)?;
    let module = view.module_data(limits.module)?;
    Ok(module
        .imports
        .iter()
        .map(|import| import.module.clone())
        .collect())
}

/// Audit and decode one complete module-system `.olean` artifact chain.
///
/// The exported part supplies the import graph and public module metadata.
/// The private part supplies the authoritative constant array used by Lean's
/// `import all` path, including definition bodies and private equation-compiler
/// auxiliaries. The server and private regions are parsed in their original
/// compacted address spaces, given the shared runtime's full-surface audit in
/// that same address space (every object, reachable or not, with pointers
/// allowed to land in the earlier parts), walked through their
/// dependency-aware object graphs, and their declarations validated before
/// any result is returned. A server whose declaration arrays reuse the exact
/// exported-region objects reuses their successful decode under the same
/// declaration budget; other server arrays are decoded in full. This function
/// does not resolve imports or admit any declaration into an [`Engine`].
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
    require_pinned_header(artifact, None)?;
    public_view.shared_audit()?;
    public_view.walk(limits.graph)?;
    let module = public_view.module_data(limits.module)?;
    if !module.is_module {
        return Err(OleanDecodeError::UnexpectedCompanionParts);
    }
    let exported_constants =
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
    require_pinned_header(server_artifact, Some(server_part))?;
    if !same_identity(&server_view.header) {
        return Err(OleanDecodeError::CompanionHeaderMismatch { part: server_part });
    }
    server_view
        .shared_audit()
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: server_part,
            error,
        })?;
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
    // The pinned server part points its declaration arrays back into the
    // exported region. Reuse that completed decode only when both arrays name
    // the same immutable objects under an unambiguous dependency map. Equal
    // names, counts or stored addresses alone are not a reuse proof.
    if !server_view
        .reuses_module_constant_arrays(&public_view)
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: server_part,
            error,
        })?
    {
        DeclDecoder::new(&server_view, limits.declarations)
            .decode_module_constants()
            .map_err(|error| OleanDecodeError::CompanionDeclaration {
                part: server_part,
                error,
            })?;
    }

    let private_part = OleanCompanionPart::Private;
    let private_view =
        OleanView::parse_with_dependencies(private_artifact, &[artifact, server_artifact])
            .map_err(|error| OleanDecodeError::CompanionRegion {
                part: private_part,
                error,
            })?;
    require_pinned_header(private_artifact, Some(private_part))?;
    if !same_identity(&private_view.header) {
        return Err(OleanDecodeError::CompanionHeaderMismatch { part: private_part });
    }
    private_view
        .shared_audit()
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: private_part,
            error,
        })?;
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

    // Returning the private array INSTEAD of the exported one is sound only
    // because it is a superset. That is a property of the Reference's emitter,
    // not something the format enforces, and an unguarded assumption here would
    // silently hand the kernel fewer declarations than the module declares —
    // franken_lean-timy's failure mode reached by a different cause. The
    // exported array was decoded above to validate it and was previously
    // discarded; this makes that work load-bearing instead of adding a pass.
    verify_private_superset(&exported_constants, &constants).map_err(|error| {
        OleanDecodeError::CompanionDeclaration {
            part: private_part,
            error,
        }
    })?;

    Ok(DecodedOlean {
        header: public_view.header.clone(),
        walk,
        module,
        constants,
        independent: independent_reading(&[artifact, server_artifact, private_artifact], limits),
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

/// [`CheckedOlean`] before its logical roots are computed.
struct UnrootedOlean {
    engine: Engine,
    decoded: DecodedOlean,
    declarations: Vec<OleanCheckedDeclaration>,
    /// Nothing was admitted: `engine` is the checking engine's clone, so the
    /// result root is the base root.
    unchanged: bool,
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

/// The frontier's verdict for a module whose check ended in an error.
///
/// FL-INV-07: a council whose objecting seats were all silent or ran out
/// ([`EngineAdmissionError::CouncilNoAnswer`]) and a planning budget that ran
/// out are non-answers, so the module is `Inconclusive`, never refused. Our own
/// accounting failing is an `InternalFault`. A kernel rejection, a council
/// disagreement and a malformed artifact stay `Failed`, and so, for now, does a
/// decode budget stop. A refused allocation is a non-answer too: it is not a
/// verdict about the module. It carries no declared allowance for a
/// [`ResourceUsage`](fln_core::outcome::ResourceUsage) to report, so, like a
/// silent council, it says what was unavailable (fln-frontier-oom-abort-w9dx).
fn frontier_error_verdict(error: OleanCheckError) -> OleanModuleVerdict {
    fn admission_leaf(error: &EngineAdmissionError) -> &EngineAdmissionError {
        match error {
            EngineAdmissionError::BatchDeclaration { error, .. } => admission_leaf(error),
            other => other,
        }
    }
    let fault = |detail: String| {
        OleanModuleVerdict::InternalFault(InternalFault::new("olean frontier", detail))
    };
    match &error {
        OleanCheckError::Admission(admission) => match admission_leaf(admission) {
            EngineAdmissionError::CouncilNoAnswer { summary } => OleanModuleVerdict::Inconclusive(
                Inconclusive::dependency_unavailable(format!("council had no answer: {summary}")),
            ),
            leaf @ EngineAdmissionError::AllocationFailure { .. } => {
                OleanModuleVerdict::Inconclusive(Inconclusive::dependency_unavailable(format!(
                    "host memory: {leaf}"
                )))
            }
            leaf @ (EngineAdmissionError::CheckerBridge { .. }
            | EngineAdmissionError::UnexpectedPublication { .. }) => fault(leaf.to_string()),
            _ => OleanModuleVerdict::Failed(error),
        },
        OleanCheckError::DependencyPresentationLimit { observed, limit }
        | OleanCheckError::DeclarationLimit { observed, limit } => {
            OleanModuleVerdict::Inconclusive(Inconclusive::resource(
                fln_core::outcome::ResourceUsage {
                    reason: fln_core::diag::ResourceReason::StructuralBudget {
                        unit: fln_core::diag::StructuralUnit::ProducedNodes,
                    },
                    allowed: u64::try_from(*limit).unwrap_or(u64::MAX),
                    observed: u64::try_from(*observed).unwrap_or(u64::MAX),
                },
            ))
        }
        OleanCheckError::AllocationFailure { .. } | OleanCheckError::HostMemory { .. } => {
            OleanModuleVerdict::Inconclusive(Inconclusive::dependency_unavailable(format!(
                "host memory: {error}"
            )))
        }
        // A decode stop is a non-answer when the decoder ran out of an explicit
        // allowance or the host refused it memory (fln-s97y). Malformed input and
        // identity failures stay `Failed`.
        OleanCheckError::Decode(decode) | OleanCheckError::ModuleDecode { error: decode, .. }
            if decode.is_host_allocation_refusal() =>
        {
            OleanModuleVerdict::Inconclusive(Inconclusive::dependency_unavailable(format!(
                "host memory: {error}"
            )))
        }
        // A construct this implementation cannot judge yet is a non-answer about the
        // tool, never evidence against the module (FL-INV-07): a payload the decoder
        // does not interpret, or an envelope the checker facade cannot rebuild.
        OleanCheckError::Decode(decode) | OleanCheckError::ModuleDecode { error: decode, .. }
            if decode.unsupported_construct().is_some() =>
        {
            OleanModuleVerdict::Inconclusive(Inconclusive::unsupported(error.to_string()))
        }
        OleanCheckError::UnsupportedDeclaration { .. }
        | OleanCheckError::MutualEnvelopeUnsupported { .. }
        | OleanCheckError::InductiveEnvelopeUnsupported { .. }
        | OleanCheckError::QuotientEnvelopeUnsupported { .. } => {
            OleanModuleVerdict::Inconclusive(Inconclusive::unsupported(error.to_string()))
        }
        OleanCheckError::Decode(decode) | OleanCheckError::ModuleDecode { error: decode, .. } => {
            match decode.resource_usage() {
                Some(usage) => OleanModuleVerdict::Inconclusive(Inconclusive::resource(usage)),
                None => OleanModuleVerdict::Failed(error),
            }
        }
        OleanCheckError::InternalInvariant { .. } => fault(error.to_string()),
        _ => OleanModuleVerdict::Failed(error),
    }
}

/// The panic payload [`install_host_allocation_failure_hook`] raises when the
/// host refuses an allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostAllocationFailure {
    /// The size of the refused request, in bytes.
    pub requested: usize,
}

/// Make a refused host allocation unwind instead of aborting the process
/// (fln-frontier-oom-abort-w9dx). Rust's default handler aborts every thread at
/// once, so one module's exhaustion used to end a whole frontier run and lose
/// every verdict in it. With this hook, the unwind reaches the frontier's
/// per-module guard, and that module's row is a typed non-answer while the run
/// continues. A binary calls this once, before any work. The process-wide hook
/// belongs to whoever owns the process, so the library never installs it.
pub fn install_host_allocation_failure_hook() {
    std::alloc::set_alloc_error_hook(host_allocation_failure);
}

fn host_allocation_failure(layout: std::alloc::Layout) {
    // The default handler's message; stderr is unbuffered, so this allocates
    // nothing.
    eprintln!("memory allocation of {} bytes failed", layout.size());
    std::panic::panic_any(HostAllocationFailure {
        requested: layout.size(),
    });
}

/// Run one module's check. An unwind out of it ends only that module, as its
/// row; it never ends the run. Without this, a panicking worker thread died
/// before reporting, and its scheduler waited for the module forever.
fn frontier_guarded(
    index: usize,
    retain: bool,
    started: std::time::Instant,
    check: impl FnOnce() -> FrontierDone,
) -> FrontierDone {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(check)).unwrap_or_else(|payload| {
        let error = frontier_unwound(payload);
        FrontierDone {
            index,
            verdict: frontier_error_verdict(error.clone()),
            accepted: None,
            engine: None,
            elapsed: started.elapsed(),
            retained: retain.then_some(FrontierRetained::Failed(error)),
        }
    })
}

/// What an unwind out of a module check means: the host refused an allocation,
/// or one of our invariants broke. A panic is never a verdict.
fn frontier_unwound(payload: Box<dyn std::any::Any + Send>) -> OleanCheckError {
    match payload.downcast::<HostAllocationFailure>() {
        Ok(failure) => OleanCheckError::HostMemory {
            requested: failure.requested,
        },
        Err(_) => OleanCheckError::InternalInvariant {
            detail: "a frontier module check panicked",
        },
    }
}

/// One module's outcome in an [`Engine::check_olean_frontier`] run.
#[derive(Debug)]
pub enum OleanModuleVerdict {
    /// Every declaration was admitted by K1 and the independent checker.
    Accepted { declarations: usize },
    /// The module was refused: its artifact, its import set, or one of its
    /// declarations.
    Failed(OleanCheckError),
    /// No verdict was reached (FL-INV-07). Counted neither as accepted nor rejected.
    Inconclusive(Inconclusive),
    /// An invariant failure while checking the module.
    InternalFault(InternalFault),
    /// Not checked, because the named import has no accepted verdict. A module is
    /// never checked against an import that was not itself admitted.
    Blocked { by: Name },
}

/// One row of a frontier run. `elapsed` is operational wall time, never part of any
/// logical identity.
#[derive(Debug)]
pub struct OleanFrontierRow {
    pub name: Name,
    pub verdict: OleanModuleVerdict,
    pub elapsed: std::time::Duration,
}

/// What a frontier observer is told: `Started` just before a module's
/// declarations go to the council, `Settled` the moment its row exists, and
/// `Decided` once its row and every earlier one exist. A module that is blocked,
/// or that failed to decode, settles and is decided without ever starting.
///
/// `Decided` arrives in frontier order, so that stream is the same at any thread
/// count. `Settled` arrives in completion order, which is not: it exists so a row
/// survives a crash that would have held it back behind a slower module still in
/// flight (bead fln-frontier-oom-abort-w9dx). Every module settles exactly once,
/// before it is decided, and both carry its frontier `position`.
#[derive(Debug, Clone, Copy)]
pub enum OleanFrontierEvent<'a> {
    Started {
        position: usize,
        total: usize,
        module: &'a Name,
    },
    Settled {
        position: usize,
        total: usize,
        row: &'a OleanFrontierRow,
    },
    Decided {
        position: usize,
        total: usize,
        row: &'a OleanFrontierRow,
    },
}

/// Per-module result of checking a closed `.olean` set without stopping at the first
/// failure.
#[derive(Debug)]
pub struct OleanFrontier {
    /// One engine holding exactly the accepted modules, if one can exist. Two
    /// accepted modules that never import each other may declare different
    /// constants under one name: Lean permits it (each of two executables has its
    /// own `main`), and no single environment holds both. Then this is the
    /// `DuplicateDeclaration` that stops the merge, and every row still stands.
    pub engine: Result<Engine, OleanCheckError>,
    pub rows: Vec<OleanFrontierRow>,
}

/// How a frontier run spreads its modules over threads. Neither field changes a
/// row or the returned engine (or its absence); see
/// [`Engine::check_olean_frontier_scheduled`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OleanFrontierJobs {
    /// Modules checked at once. One checks every module on the calling thread.
    pub threads: std::num::NonZeroUsize,
    /// Stack for each worker thread when `threads` is above one. The kernel budget
    /// in the run's limits must be calibrated for it, as for the calling thread.
    pub worker_stack_bytes: usize,
}

impl OleanFrontierJobs {
    /// One module at a time, on the calling thread.
    pub const SERIAL: OleanFrontierJobs = OleanFrontierJobs {
        threads: std::num::NonZeroUsize::MIN,
        worker_stack_bytes: 0,
    };
}

/// A module whose council check passed, as its importers need it.
struct FrontierAccepted {
    index: usize,
    position: usize,
    name: Name,
    /// Every constant the module added, with the digest its engine computed.
    admitted: Vec<EnvironmentEntry>,
}

/// The accepted import a module's closure engine starts from, and its closure.
struct FrontierBase {
    engine: std::sync::Arc<Engine>,
    closure: std::sync::Arc<BTreeSet<usize>>,
}

/// One module handed to the council, with the accepted modules of its closure.
struct FrontierJob {
    index: usize,
    position: usize,
    name: Name,
    artifact: DecodedOlean,
    base: Option<FrontierBase>,
    closure: Vec<std::sync::Arc<FrontierAccepted>>,
    /// Keep what [`Engine::check_olean_modules_scheduled`] reassembles the serial
    /// result from; the frontier itself keeps only verdicts.
    retain: bool,
}

struct FrontierDone {
    index: usize,
    verdict: OleanModuleVerdict,
    accepted: Option<FrontierAccepted>,
    /// The engine after checking an accepted module: its closure's environment
    /// plus what it admitted. A scheduler keeps it only while a module not yet
    /// dispatched will start from it ([`FrontierEngines`]).
    engine: Option<Engine>,
    elapsed: std::time::Duration,
    /// Present only for a [`FrontierJob::retain`] job that completed or failed.
    retained: Option<FrontierRetained>,
}

/// A retaining frontier job's own record: what the serial result is reassembled
/// from for a module whose check completed (its decoded artifact and checker
/// rows; for each decoded constant, the digest its own engine holds under that
/// name; each admitted constant's checker entry), or the exact error its check
/// returned, which the frontier's verdict reclassifies.
enum FrontierRetained {
    Checked {
        decoded: Box<DecodedOlean>,
        declarations: Vec<OleanCheckedDeclaration>,
        closure_digests: Vec<Option<fln_hash::domain::Digest>>,
        checker_entries: BTreeMap<Name, Result<CheckerConstantEntry, &'static str>>,
    },
    Failed(OleanCheckError),
}

/// The import a frontier module's closure engine starts from: the import with
/// the largest closure, the earlier on a tie. It depends only on the import
/// graph, so a scheduler can count each engine's future users before any check.
fn frontier_base_of(
    dependencies: &[BTreeSet<usize>],
    closures: &[std::sync::Arc<BTreeSet<usize>>],
    position: impl Fn(usize) -> usize,
    index: usize,
) -> Option<usize> {
    dependencies[index]
        .iter()
        .copied()
        .filter(|dependency| *dependency != index)
        .max_by(|left, right| {
            closures[*left]
                .len()
                .cmp(&closures[*right].len())
                .then(position(*right).cmp(&position(*left)))
        })
}

/// Each admitted constant's checker entry in `engine`'s retained projection,
/// which a scheduled module set reassembles its serial projection from. A
/// constant without one is recorded as the invariant the reassembly reports.
fn frontier_checker_entries(
    engine: &Engine,
    admitted: &[EnvironmentEntry],
    limits: OleanCheckLimits,
) -> BTreeMap<Name, Result<CheckerConstantEntry, &'static str>> {
    admitted
        .iter()
        .map(|entry| {
            let name = entry.declaration().name().clone();
            let checker = engine
                .checker_environment
                .as_ref()
                .ok_or("a module that admitted constants retains no checker projection")
                .and_then(|projection| {
                    let wire = decode_checker_name(&name, limits.admission.checker.decode)
                        .map_err(|_| "an admitted constant has no checker name")?;
                    let declaration = projection
                        .find(&wire)
                        .ok_or("an admitted constant is missing from its checker projection")?;
                    Ok(CheckerConstantEntry::new(wire, declaration.clone()))
                });
            (name, checker)
        })
        .collect()
}

/// Accepted engines a frontier still needs. Each module's engine is kept only
/// while a module not yet dispatched (or decided without a check) will start
/// from it; every other module of a closure contributes only its admitted
/// entries. Without this, every accepted module's whole engine, with the
/// checker terms it decoded for itself, lived until the run ended.
struct FrontierEngines {
    base_of: Vec<Option<usize>>,
    users: Vec<usize>,
    engines: Vec<Option<std::sync::Arc<Engine>>>,
}

impl FrontierEngines {
    fn new(base_of: Vec<Option<usize>>) -> Self {
        let mut users = vec![0_usize; base_of.len()];
        for base in base_of.iter().flatten() {
            users[*base] += 1;
        }
        let engines = (0..base_of.len()).map(|_| None).collect();
        Self {
            base_of,
            users,
            engines,
        }
    }

    /// Keep an accepted module's engine if some later module starts from it.
    fn keep(&mut self, index: usize, engine: Option<Engine>) {
        if self.users[index] > 0 {
            self.engines[index] = engine.map(std::sync::Arc::new);
        }
    }

    /// `index` leaves the schedule: dispatched (`take` its base) or decided
    /// without a check. Its base loses a user and is dropped at the last one.
    fn release(
        &mut self,
        index: usize,
        closures: &[std::sync::Arc<BTreeSet<usize>>],
        take: bool,
    ) -> Result<Option<FrontierBase>, OleanCheckError> {
        let Some(base) = self.base_of[index] else {
            return Ok(None);
        };
        self.users[base] =
            self.users[base]
                .checked_sub(1)
                .ok_or(OleanCheckError::InternalInvariant {
                    detail: "a frontier base engine lost more users than it had",
                })?;
        let engine = if take {
            Some(
                self.engines[base]
                    .clone()
                    .ok_or(OleanCheckError::InternalInvariant {
                        detail: "a dispatched module's base engine was not kept",
                    })?,
            )
        } else {
            None
        };
        if self.users[base] == 0 {
            self.engines[base] = None;
        }
        Ok(engine.map(|engine| FrontierBase {
            engine,
            closure: std::sync::Arc::clone(&closures[base]),
        }))
    }
}

/// One module of a scheduled set whose check completed, with what the serial result
/// keeps of it.
struct ScheduledOleanModule {
    module: std::sync::Arc<FrontierAccepted>,
    decoded: DecodedOlean,
    declarations: Vec<OleanCheckedDeclaration>,
    /// For each of `decoded.constants`, the digest the module's own engine held
    /// under that name after its check.
    closure_digests: Vec<Option<fln_hash::domain::Digest>>,
    checker_entries: BTreeMap<Name, Result<CheckerConstantEntry, &'static str>>,
}

/// The rows the serial planner gives a module checked after `before`, the
/// environment of every module ahead of it in the serial order, built from the
/// agreements the module's own check against its closure issued. Names the serial
/// planner finds present carry the grounds it records for them; a repeat it would
/// recheck under a scratch name carries the agreement issued for this module's copy.
fn serial_olean_rows(
    before: &Environment,
    decoded: &DecodedOlean,
    own: Vec<OleanCheckedDeclaration>,
    limits: OleanCheckLimits,
) -> Result<Vec<OleanCheckedDeclaration>, OleanCheckError> {
    let plan = plan_olean_declarations(before, &decoded.constants, limits)?;
    let agreements: BTreeMap<Name, CheckerAgreement> =
        own.into_iter().map(|row| (row.name, row.checker)).collect();
    let agreement = |name: &Name| {
        agreements
            .get(name)
            .copied()
            .ok_or(OleanCheckError::InternalInvariant {
                detail: "a serial row has no agreement from its module's own check",
            })
    };
    let mut rows = Vec::new();
    rows.try_reserve_exact(decoded.constants.len())
        .map_err(|_| OleanCheckError::AllocationFailure {
            resource: ".olean reassembled declaration records",
            requested: decoded.constants.len(),
        })?;
    for unit_index in &plan.order {
        let Some(unit) = plan.units.get(*unit_index) else {
            return Err(OleanCheckError::InternalInvariant {
                detail: "planned declaration unit is outside the unit table",
            });
        };
        for name in &unit.names {
            rows.push(OleanCheckedDeclaration {
                name: name.clone(),
                checker: agreement(name)?,
            });
        }
    }
    for (name, checker) in plan.already_present {
        rows.push(OleanCheckedDeclaration { name, checker });
    }
    for repeat in plan.subsumed {
        let name = repeat.name().clone();
        let checker = match repeat {
            ConstantInfo::Thm(_) => agreement(&name)?,
            ConstantInfo::Axiom(_) => CheckerAgreement {
                schema: "fln-checker/v1",
                ground: CheckerAdmissionGround::AxiomPreamble,
            },
            _ => {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "only theorems and axioms can subsume an admitted repeat",
                });
            }
        };
        rows.push(OleanCheckedDeclaration { name, checker });
    }
    if rows.len() != decoded.constants.len() {
        return Err(OleanCheckError::InternalInvariant {
            detail: "reassembled declaration count differs from the decoded declaration table",
        });
    }
    Ok(rows)
}

/// Add one admitted constant to an import closure under the serial planner's
/// rule for a repeated name: an identical copy is already there, a copy that
/// subsumes or is subsumed by the present one keeps the present one, and any
/// other pair cannot be imported together.
fn merge_frontier_entry(
    environment: Environment,
    entry: &EnvironmentEntry,
) -> Result<Environment, OleanCheckError> {
    let name = entry.declaration().name();
    let Some(present) = environment.entry(name) else {
        return environment.with_entry(entry.clone()).map_err(|_| {
            OleanCheckError::InternalInvariant {
                detail: "an absent frontier constant could not be added",
            }
        });
    };
    if present.digest() == entry.digest() {
        return Ok(environment);
    }
    let lookup = |name: &Name| environment.find(name);
    if olean_imports::subsumes_info(&lookup, present.declaration(), entry.declaration())
        || olean_imports::subsumes_info(&lookup, entry.declaration(), present.declaration())
    {
        return Ok(environment);
    }
    Err(OleanCheckError::DuplicateDeclaration { name: name.clone() })
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
/// This production slice handles closed import sets and reconstructs complete
/// non-safe mutual definition envelopes, the fixed quotient initializer, and
/// safe bounded nonrecursive `Type` inductive units as authority transitions. Other
/// inductive shapes remain explicit checker non-answers rather than silently
/// entering trusted context. Safe definitions, theorems, and opaques retain
/// their multi-name metadata and check individually inside the atomic artifact
/// batch when their actual dependency graph is acyclic. Environment extensions
/// are decoded and counted by [`DecodedOlean`] but are not interpreted by this
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
    /// The host refused an allocation, and its handler unwound instead of
    /// aborting ([`install_host_allocation_failure_hook`]). `requested` is in
    /// bytes, where [`OleanCheckError::AllocationFailure`] counts entries.
    HostMemory {
        requested: usize,
    },
    DuplicateDeclaration {
        name: Name,
    },
    /// Two modules of one closed set decode to declarations sharing a name
    /// where neither subsumes the other.
    ///
    /// Re-generated equation and congruence lemmas legitimately repeat a name
    /// across modules, so a name collision alone is not a fault, and neither
    /// is a repeat the Reference's import accepts (`subsumesInfo`). A
    /// collision neither side subsumes is: the set has no single coherent
    /// meaning for that name, and admitting it in dependency order would let
    /// whichever module sorted first silently win while the other was rejected
    /// as already-declared — a kernel-shaped complaint about what is really a
    /// property of the input set.
    ConflictingModuleDeclaration {
        name: Name,
        first_module: Name,
        second_module: Name,
    },
    UnsupportedDeclaration {
        name: Name,
        kind: &'static str,
    },
    MutualEnvelopeUnsupported {
        name: Name,
        members: Vec<Name>,
    },
    InductiveEnvelopeUnsupported {
        name: Name,
        members: Vec<Name>,
    },
    QuotientEnvelopeUnsupported {
        names: Vec<Name>,
    },
    MissingConstants {
        declaration: Name,
        names: Vec<Name>,
    },
    DependencyCycle {
        declarations: Vec<Name>,
    },
    /// The independent checker's own reading of the artifact differs from the
    /// primary decode for a declaration no council reviews: one already present,
    /// or an axiom repeat, each reported checked because the primary decode
    /// equals one already admitted (bead `franken_lean-z8j.1.14`). One of the two
    /// decoders is wrong, so the module is not checked; it is the same objection
    /// a council seat raises for a declaration it does review.
    IndependentReadingDiffers {
        name: Name,
        detail: String,
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
            Self::HostMemory { requested } => write!(
                formatter,
                "the host refused an allocation of {requested} bytes"
            ),
            Self::DuplicateDeclaration { name } => write!(
                formatter,
                ".olean repeats declaration `{}`",
                name.to_display_string()
            ),
            Self::ConflictingModuleDeclaration {
                name,
                first_module,
                second_module,
            } => write!(
                formatter,
                "modules `{}` and `{}` decode to different declarations both named `{}`",
                first_module.to_display_string(),
                second_module.to_display_string(),
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
            Self::InductiveEnvelopeUnsupported { name, members } => write!(
                formatter,
                "cannot reconstruct the inductive declaration envelope for `{}` from {}",
                name.to_display_string(),
                display_names(members)
            ),
            Self::QuotientEnvelopeUnsupported { names } => write!(
                formatter,
                "cannot reconstruct the four-row quotient initialization envelope from {}",
                display_names(names)
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
            Self::IndependentReadingDiffers { name, detail } => write!(
                formatter,
                "the independent checker's reading of `{}` is not the primary decode's: {detail}",
                name.to_display_string()
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
        ConstantInfo::Defn(value) => Ok(Declaration::Defn(value.clone())),
        ConstantInfo::Thm(value) => Ok(Declaration::Thm(value.clone())),
        ConstantInfo::Opaque(value) => Ok(Declaration::Opaque(value.clone())),
        ConstantInfo::Quot(_)
        | ConstantInfo::Induct(_)
        | ConstantInfo::Ctor(_)
        | ConstantInfo::Rec(_) => Err(OleanCheckError::UnsupportedDeclaration {
            name,
            kind: info.kind_name(),
        }),
    }
}

#[derive(Debug, Clone)]
struct OleanDeclarationUnit {
    constant_indices: Vec<usize>,
    names: Vec<Name>,
    declaration: Declaration,
}

#[derive(Debug)]
struct OleanDeclarationPlan {
    units: Vec<OleanDeclarationUnit>,
    order: Vec<usize>,
    already_present: Vec<(Name, CheckerAgreement)>,
    /// Non-identical repeats of an admitted name that the Reference's import
    /// accepts (`subsumesInfo`); their own bodies still need a check.
    subsumed: Vec<ConstantInfo>,
}

fn unsupported_mutual_envelope(value: &DefinitionVal) -> OleanCheckError {
    OleanCheckError::MutualEnvelopeUnsupported {
        name: value.base.name.clone(),
        members: value.all.clone(),
    }
}

fn unsupported_inductive_envelope(name: &Name, members: Vec<Name>) -> OleanCheckError {
    OleanCheckError::InductiveEnvelopeUnsupported {
        name: name.clone(),
        members,
    }
}

fn quotient_initialization_names() -> [Name; 4] {
    [
        Name::from_components(["Quot"]),
        Name::from_components(["Quot", "mk"]),
        Name::from_components(["Quot", "lift"]),
        Name::from_components(["Quot", "ind"]),
    ]
}

fn unsupported_quotient_envelope(constants: &[ConstantInfo]) -> OleanCheckError {
    OleanCheckError::QuotientEnvelopeUnsupported {
        names: constants
            .iter()
            .filter(|constant| matches!(constant, ConstantInfo::Quot(_)))
            .map(|constant| constant.name().clone())
            .collect(),
    }
}

fn build_olean_declaration_units(
    constants: &[ConstantInfo],
    owners: &BTreeMap<Name, usize>,
) -> Result<(Vec<OleanDeclarationUnit>, Vec<usize>), OleanCheckError> {
    let mut units = Vec::new();
    units
        .try_reserve_exact(constants.len())
        .map_err(|_| OleanCheckError::AllocationFailure {
            resource: ".olean declaration units",
            requested: constants.len(),
        })?;
    let mut constant_units = vec![usize::MAX; constants.len()];

    for (index, info) in constants.iter().enumerate() {
        if constant_units[index] != usize::MAX {
            continue;
        }
        if let ConstantInfo::Induct(inductive) = info {
            if inductive.all.first() != Some(&inductive.base.name) {
                continue;
            }
            let mut member_indices = Vec::new();
            let mut members = Vec::new();
            let mut unique = BTreeSet::new();
            for type_name in &inductive.all {
                if !unique.insert(type_name.clone()) {
                    return Err(unsupported_inductive_envelope(
                        &inductive.base.name,
                        inductive.all.clone(),
                    ));
                }
                let Some(&type_index) = owners.get(type_name) else {
                    return Err(unsupported_inductive_envelope(
                        &inductive.base.name,
                        inductive.all.clone(),
                    ));
                };
                let Some(ConstantInfo::Induct(member)) = constants.get(type_index) else {
                    return Err(unsupported_inductive_envelope(
                        &inductive.base.name,
                        inductive.all.clone(),
                    ));
                };
                if member.all != inductive.all || constant_units[type_index] != usize::MAX {
                    return Err(unsupported_inductive_envelope(
                        &inductive.base.name,
                        inductive.all.clone(),
                    ));
                }
                member_indices.push(type_index);
                members.push(member.base.name.clone());
                for (ctor_index, ctor_name) in member.ctors.iter().enumerate() {
                    let Some(&constant_index) = owners.get(ctor_name) else {
                        return Err(unsupported_inductive_envelope(
                            &inductive.base.name,
                            inductive.all.clone(),
                        ));
                    };
                    let Some(ConstantInfo::Ctor(constructor)) = constants.get(constant_index)
                    else {
                        return Err(unsupported_inductive_envelope(
                            &inductive.base.name,
                            inductive.all.clone(),
                        ));
                    };
                    if constructor.induct != member.base.name
                        || usize::try_from(constructor.cidx).ok() != Some(ctor_index)
                        || constant_units[constant_index] != usize::MAX
                    {
                        return Err(unsupported_inductive_envelope(
                            &inductive.base.name,
                            inductive.all.clone(),
                        ));
                    }
                    member_indices.push(constant_index);
                    members.push(constructor.base.name.clone());
                }
            }
            for (constant_index, candidate) in constants.iter().enumerate() {
                let ConstantInfo::Rec(recursor) = candidate else {
                    continue;
                };
                if recursor.all.first() == Some(&inductive.base.name) {
                    if constant_units[constant_index] != usize::MAX {
                        return Err(unsupported_inductive_envelope(
                            &inductive.base.name,
                            inductive.all.clone(),
                        ));
                    }
                    member_indices.push(constant_index);
                    members.push(recursor.base.name.clone());
                }
            }
            let mut types = Vec::new();
            let mut constructors = Vec::new();
            let mut recursors = Vec::new();
            for member_index in &member_indices {
                match &constants[*member_index] {
                    ConstantInfo::Induct(value) => types.push(value.clone()),
                    ConstantInfo::Ctor(value) => constructors.push(value.clone()),
                    ConstantInfo::Rec(value) => recursors.push(value.clone()),
                    _ => {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "inductive unit contains a non-inductive row",
                        });
                    }
                }
            }
            let unit = units.len();
            for member_index in &member_indices {
                constant_units[*member_index] = unit;
            }
            units.push(OleanDeclarationUnit {
                constant_indices: member_indices,
                names: members,
                declaration: Declaration::Inductive(fln_kernel::InductiveBlock {
                    types,
                    ctors: constructors,
                    recursors,
                }),
            });
            continue;
        }
        if matches!(info, ConstantInfo::Ctor(_) | ConstantInfo::Rec(_)) {
            continue;
        }
        if matches!(info, ConstantInfo::Quot(_)) {
            let names = quotient_initialization_names();
            let mut member_indices = Vec::new();
            member_indices.try_reserve_exact(names.len()).map_err(|_| {
                OleanCheckError::AllocationFailure {
                    resource: ".olean quotient member indices",
                    requested: names.len(),
                }
            })?;
            let mut members = Vec::new();
            members.try_reserve_exact(names.len()).map_err(|_| {
                OleanCheckError::AllocationFailure {
                    resource: ".olean quotient declarations",
                    requested: names.len(),
                }
            })?;
            for name in &names {
                let Some(&member_index) = owners.get(name) else {
                    return Err(unsupported_quotient_envelope(constants));
                };
                if constant_units[member_index] != usize::MAX {
                    return Err(unsupported_quotient_envelope(constants));
                }
                let Some(ConstantInfo::Quot(member)) = constants.get(member_index) else {
                    return Err(unsupported_quotient_envelope(constants));
                };
                member_indices.push(member_index);
                members.push(member.clone());
            }
            if !names.contains(info.name()) {
                return Err(unsupported_quotient_envelope(constants));
            }
            let unit = units.len();
            for member_index in &member_indices {
                constant_units[*member_index] = unit;
            }
            units.push(OleanDeclarationUnit {
                constant_indices: member_indices,
                names: names.to_vec(),
                declaration: Declaration::Quotient(members),
            });
            continue;
        }
        let ConstantInfo::Defn(definition) = info else {
            let declaration = checked_olean_declaration(info)?;
            let unit = units.len();
            constant_units[index] = unit;
            units.push(OleanDeclarationUnit {
                constant_indices: vec![index],
                names: vec![info.name().clone()],
                declaration,
            });
            continue;
        };
        // Lean adds every partial definition as a `mutualDefnDecl`, a singleton
        // included, and the pin's `add_definition` would refuse a partial one that
        // recurses (fln-tio5). So a partial definition is presented as the mutual
        // unit it was admitted as; a singleton unsafe one keeps `add_definition`'s
        // unsafe branch, which accepts the same recursion.
        let singleton_definition = definition.all.is_empty()
            || (definition.all.len() == 1 && definition.safety != DefinitionSafety::Partial);
        if singleton_definition || definition.safety == DefinitionSafety::Safe {
            let declaration = checked_olean_declaration(info)?;
            let unit = units.len();
            constant_units[index] = unit;
            units.push(OleanDeclarationUnit {
                constant_indices: vec![index],
                names: vec![info.name().clone()],
                declaration,
            });
            continue;
        }
        // Mathlib's `compile_inductive` (Mathlib/Util/CompileInductive.lean)
        // builds each compiled recursor as `{ rv with name, value, .. }`, so its
        // `all` is the recursor's inductive block (`[List]`), not the
        // definitions it was admitted with. The pin's `add_mutual` never reads
        // `all`. A definition whose `all` does not name it is grouped with every
        // non-safe definition of the same safety sharing that `all`: the one
        // `mutualDefnDecl` that built them.
        if !definition.all.contains(&definition.base.name) {
            let mut member_indices = Vec::new();
            let mut members = Vec::new();
            for (candidate_index, candidate) in constants.iter().enumerate() {
                let ConstantInfo::Defn(candidate) = candidate else {
                    continue;
                };
                if candidate.safety == definition.safety
                    && candidate.all == definition.all
                    && !candidate.all.contains(&candidate.base.name)
                    && constant_units[candidate_index] == usize::MAX
                {
                    member_indices.push(candidate_index);
                    members.push(candidate.clone());
                }
            }
            let unit = units.len();
            for member_index in &member_indices {
                constant_units[*member_index] = unit;
            }
            units.push(OleanDeclarationUnit {
                constant_indices: member_indices,
                names: members
                    .iter()
                    .map(|member| member.base.name.clone())
                    .collect(),
                declaration: Declaration::Mutual(members),
            });
            continue;
        }
        let mut member_indices = Vec::new();
        member_indices
            .try_reserve_exact(definition.all.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean mutual member indices",
                requested: definition.all.len(),
            })?;
        let mut members = Vec::new();
        members
            .try_reserve_exact(definition.all.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean mutual definitions",
                requested: definition.all.len(),
            })?;
        let mut unique = BTreeSet::new();
        for name in &definition.all {
            if !unique.insert(name.clone()) {
                return Err(unsupported_mutual_envelope(definition));
            }
            let Some(&member_index) = owners.get(name) else {
                return Err(unsupported_mutual_envelope(definition));
            };
            if constant_units[member_index] != usize::MAX {
                return Err(unsupported_mutual_envelope(definition));
            }
            let Some(ConstantInfo::Defn(member)) = constants.get(member_index) else {
                return Err(unsupported_mutual_envelope(definition));
            };
            if member.safety == DefinitionSafety::Safe || member.all != definition.all {
                return Err(unsupported_mutual_envelope(definition));
            }
            member_indices.push(member_index);
            members.push(member.clone());
        }
        if !unique.contains(&definition.base.name) {
            return Err(unsupported_mutual_envelope(definition));
        }

        let unit = units.len();
        for member_index in &member_indices {
            constant_units[*member_index] = unit;
        }
        units.push(OleanDeclarationUnit {
            constant_indices: member_indices,
            names: definition.all.clone(),
            declaration: Declaration::Mutual(members),
        });
    }

    if let Some((index, _)) = constant_units
        .iter()
        .enumerate()
        .find(|(_, unit)| **unit == usize::MAX)
    {
        let name = constants[index].name();
        let members = match &constants[index] {
            ConstantInfo::Induct(value) => value.all.clone(),
            ConstantInfo::Ctor(value) => vec![value.induct.clone(), value.base.name.clone()],
            ConstantInfo::Rec(value) => value.all.clone(),
            _ => Vec::new(),
        };
        return Err(unsupported_inductive_envelope(name, members));
    }
    Ok((units, constant_units))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstantReferenceCollectionError {
    PresentationLimit { observed: usize, limit: usize },
    AllocationFailure { requested: usize },
}

/// Collect the constants `expression` names. A decoded term is a DAG whose
/// subterms are shared, so each distinct node is presented once: walked as a
/// tree, `blastDivSubtractShift_decl_eq` alone presents 69,111,656 nodes over
/// 1,719 distinct ones (bead fln-32rr).
fn collect_constant_references(
    expression: &Expr,
    names: &mut BTreeSet<Name>,
    presentations: &mut usize,
    limit: usize,
) -> Result<(), ConstantReferenceCollectionError> {
    use fln_core::expr::ExprNode;

    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| ConstantReferenceCollectionError::AllocationFailure { requested: 1 })?;
    pending.push(expression);
    let mut seen = std::collections::HashSet::<*const ExprNode>::new();
    while let Some(expression) = pending.pop() {
        seen.try_reserve(1)
            .map_err(|_| ConstantReferenceCollectionError::AllocationFailure {
                requested: seen.len().saturating_add(1),
            })?;
        if !seen.insert(std::ptr::from_ref(expression.node())) {
            continue;
        }
        *presentations = presentations.saturating_add(1);
        if *presentations > limit {
            return Err(ConstantReferenceCollectionError::PresentationLimit {
                observed: *presentations,
                limit,
            });
        }
        match expression.node() {
            ExprNode::Const { name, .. } => {
                names.insert(name.clone());
            }
            ExprNode::App { f, a } => {
                pending.try_reserve(2).map_err(|_| {
                    ConstantReferenceCollectionError::AllocationFailure {
                        requested: pending.len().saturating_add(2),
                    }
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
                pending.try_reserve(2).map_err(|_| {
                    ConstantReferenceCollectionError::AllocationFailure {
                        requested: pending.len().saturating_add(2),
                    }
                })?;
                pending.push(body);
                pending.push(binder_type);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.try_reserve(3).map_err(|_| {
                    ConstantReferenceCollectionError::AllocationFailure {
                        requested: pending.len().saturating_add(3),
                    }
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

fn collect_olean_dependencies(
    expression: &Expr,
    names: &mut BTreeSet<Name>,
    presentations: &mut usize,
    limit: usize,
) -> Result<(), OleanCheckError> {
    collect_constant_references(expression, names, presentations, limit).map_err(
        |error| match error {
            ConstantReferenceCollectionError::PresentationLimit { observed, limit } => {
                OleanCheckError::DependencyPresentationLimit { observed, limit }
            }
            ConstantReferenceCollectionError::AllocationFailure { requested } => {
                OleanCheckError::AllocationFailure {
                    resource: ".olean dependency worklist",
                    requested,
                }
            }
        },
    )
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

/// Whole-set bounds for a closed `.olean` module set: non-empty, within the module and
/// byte limits, and no module named twice. Returns each module's input index by name.
fn olean_module_owners(
    modules: &[OleanModuleInput<'_>],
    limits: OleanCheckLimits,
) -> Result<BTreeMap<Name, usize>, OleanCheckError> {
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
    Ok(owners)
}

/// Decode one module of a closed set, requiring the server and private parts exactly
/// when the artifact is a module-system `.olean`.
fn decode_olean_module_input(
    module: &OleanModuleInput<'_>,
    limits: OleanCheckLimits,
) -> Result<DecodedOlean, OleanCheckError> {
    match (module.server_artifact, module.private_artifact) {
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
    })
}

fn plan_olean_declarations(
    base: &Environment,
    constants: &[ConstantInfo],
    limits: OleanCheckLimits,
) -> Result<OleanDeclarationPlan, OleanCheckError> {
    if constants.len() > limits.max_declarations {
        return Err(OleanCheckError::DeclarationLimit {
            observed: constants.len(),
            limit: limits.max_declarations,
        });
    }

    let mut seen_names = BTreeSet::new();
    let mut owners = BTreeMap::new();
    let mut already_present = Vec::new();
    let mut subsumed = Vec::new();
    let mut new_constants = Vec::new();

    for info in constants {
        if !seen_names.insert(info.name().clone()) {
            return Err(OleanCheckError::DuplicateDeclaration {
                name: info.name().clone(),
            });
        }

        if let Some(existing) = base.find(info.name()) {
            if *existing != *info {
                let lookup = |name: &Name| base.find(name);
                if olean_imports::subsumes_info(&lookup, existing, info)
                    || olean_imports::subsumes_info(&lookup, info, existing)
                {
                    subsumed.push(info.clone());
                    continue;
                }
                return Err(OleanCheckError::DuplicateDeclaration {
                    name: info.name().clone(),
                });
            }
            let ground = match info {
                ConstantInfo::Thm(_) | ConstantInfo::Defn(_) | ConstantInfo::Opaque(_) => {
                    CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
                }
                ConstantInfo::Axiom(_) => CheckerAdmissionGround::AxiomPreamble,
                ConstantInfo::Quot(_) => CheckerAdmissionGround::QuotientPrimitiveChecked,
                ConstantInfo::Induct(_) | ConstantInfo::Ctor(_) | ConstantInfo::Rec(_) => {
                    CheckerAdmissionGround::InductiveNonrecursiveChecked
                }
            };
            already_present.push((
                info.name().clone(),
                CheckerAgreement {
                    schema: "fln-checker/v1",
                    ground,
                },
            ));
            continue;
        }

        owners.insert(info.name().clone(), new_constants.len());
        new_constants.push(info.clone());
    }

    let (units, constant_units) = build_olean_declaration_units(&new_constants, &owners)?;

    let mut remaining = vec![0_usize; units.len()];
    let mut dependents = vec![Vec::new(); units.len()];
    let mut presentations = 0_usize;
    for (unit_index, unit) in units.iter().enumerate() {
        let mut missing = BTreeSet::new();
        let mut dependencies = BTreeSet::new();
        for constant_index in &unit.constant_indices {
            let Some(info) = new_constants.get(*constant_index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "authority unit names a declaration outside the decoded table",
                });
            };
            for dependency in olean_dependencies(
                info,
                &mut presentations,
                limits.max_dependency_presentations,
            )? {
                match owners.get(&dependency).copied() {
                    Some(owner) => {
                        let Some(&dependency_unit) = constant_units.get(owner) else {
                            return Err(OleanCheckError::InternalInvariant {
                                detail: "declaration owner has no authority unit",
                            });
                        };
                        if dependency_unit != unit_index {
                            dependencies.insert(dependency_unit);
                        }
                    }
                    None if base.find(&dependency).is_some() => {}
                    None => {
                        missing.insert(dependency);
                    }
                }
            }
        }
        if !missing.is_empty() {
            return Err(OleanCheckError::MissingConstants {
                declaration: unit.names[0].clone(),
                names: missing.into_iter().collect(),
            });
        }
        remaining[unit_index] = dependencies.len();
        for dependency in dependencies {
            dependents[dependency].push(unit_index);
        }
    }

    let mut ready: BTreeSet<(Name, usize)> = units
        .iter()
        .enumerate()
        .filter(|(index, _)| remaining[*index] == 0)
        .map(|(index, unit)| {
            let key = unit
                .names
                .iter()
                .min()
                .cloned()
                .unwrap_or_else(Name::anonymous);
            (key, index)
        })
        .collect();
    let mut order = Vec::new();
    order
        .try_reserve_exact(units.len())
        .map_err(|_| OleanCheckError::AllocationFailure {
            resource: ".olean declaration order",
            requested: units.len(),
        })?;
    while let Some((_, index)) = ready.pop_first() {
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
                let Some(unit) = units.get(*dependent) else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "ready dependent is outside the constant table",
                    });
                };
                let key = unit
                    .names
                    .iter()
                    .min()
                    .cloned()
                    .unwrap_or_else(Name::anonymous);
                ready.insert((key, *dependent));
            }
        }
    }
    if order.len() != units.len() {
        let declarations = units
            .iter()
            .enumerate()
            .filter(|(index, _)| remaining[*index] != 0)
            .flat_map(|(_, unit)| unit.names.iter().cloned())
            .collect();
        return Err(OleanCheckError::DependencyCycle { declarations });
    }
    Ok(OleanDeclarationPlan {
        units,
        order,
        already_present,
        subsumed,
    })
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
/// The live source constructors seed only the declarations needed by their
/// bounded frontends: opaque `Nat : Sort 1`, or exact Nat/String type rows plus
/// the pin-shaped Bool block and checked scalar extern signatures. Neither seed
/// is the real Prelude. Successful admission or execution returns a new
/// `Engine` snapshot containing the published declaration; the receiver is
/// never mutated.
/// Configurable builder for embeddable [`Engine`] sessions (plan §17.2).
///
/// Follows bead `franken_lean-7kc`: toolchain epoch, semantic mode,
/// reproducibility profile, options, and admission/execution limits are explicit
/// configuration inputs.
#[derive(Debug, Clone, PartialEq)]
pub struct EngineBuilder {
    epoch: ModuleEpoch,
    mode: Mode,
    reproducibility: ReproducibilityProfile,
    options: KVMap,
    admission_limits: Option<EngineAdmissionLimits>,
    execution_limits: Option<EngineExecutionLimits>,
}

impl EngineBuilder {
    /// Create a new builder configured with the toolchain's pinned epoch,
    /// standard sound mode, standard reproducibility, and empty options.
    pub fn new() -> Self {
        Self {
            epoch: ModuleEpoch::new(OLEAN_PIN_TAG, OLEAN_PIN_COMMIT),
            mode: Mode::DEFAULT,
            reproducibility: ReproducibilityProfile::Standard,
            options: KVMap::new(),
            admission_limits: None,
            execution_limits: None,
        }
    }

    /// Set the toolchain epoch against which modules and artifacts are validated.
    pub fn toolchain_epoch(mut self, epoch: ModuleEpoch) -> Self {
        self.epoch = epoch;
        self
    }

    /// Set the semantic mode (Faithful, Sound, or Frontier).
    pub fn mode(mut self, mode: Mode) -> Self {
        self.mode = mode;
        self
    }

    /// Set the reproducibility profile (Standard or Certified).
    pub fn reproducibility(mut self, profile: ReproducibilityProfile) -> Self {
        self.reproducibility = profile;
        self
    }

    /// Set the options participating in the environment's logical root.
    pub fn options(mut self, options: KVMap) -> Self {
        self.options = options;
        self
    }

    /// Set caller-supplied admission bounds.
    pub fn admission_limits(mut self, limits: EngineAdmissionLimits) -> Self {
        self.admission_limits = Some(limits);
        self
    }

    /// Set caller-supplied execution bounds.
    pub fn execution_limits(mut self, limits: EngineExecutionLimits) -> Self {
        self.execution_limits = Some(limits);
        self
    }

    /// Set both admission and execution limits from an explicit kernel budget.
    pub fn kernel_budget(mut self, budget: Budget) -> Self {
        self.admission_limits = Some(EngineAdmissionLimits::new(budget));
        self.execution_limits = Some(EngineExecutionLimits::new(budget));
        self
    }

    /// The configured toolchain epoch.
    pub fn epoch(&self) -> &ModuleEpoch {
        &self.epoch
    }

    /// The configured semantic mode.
    pub fn get_mode(&self) -> Mode {
        self.mode
    }

    /// The configured reproducibility profile.
    pub fn get_reproducibility(&self) -> ReproducibilityProfile {
        self.reproducibility
    }

    /// The configured options map.
    pub fn get_options(&self) -> &KVMap {
        &self.options
    }

    /// The configured admission limits, if set.
    pub fn get_admission_limits(&self) -> Option<EngineAdmissionLimits> {
        self.admission_limits
    }

    /// The configured execution limits, if set.
    pub fn get_execution_limits(&self) -> Option<EngineExecutionLimits> {
        self.execution_limits
    }

    /// Construct an empty engine with an empty environment.
    pub fn build_empty(&self) -> Engine {
        Engine {
            environment: Environment::new(),
            checker_environment: None,
            imported_modules: std::sync::Arc::default(),
            imported_environment: None,
            imported_module_dependencies: std::sync::Arc::default(),
            epoch: self.epoch.clone(),
            mode: self.mode,
            reproducibility: self.reproducibility,
            options: self.options.clone(),
        }
    }

    /// Attach the configured engine facade to an existing immutable environment.
    pub fn build_from_environment(&self, environment: Environment) -> Engine {
        Engine {
            environment,
            checker_environment: None,
            imported_modules: std::sync::Arc::default(),
            imported_environment: None,
            imported_module_dependencies: std::sync::Arc::default(),
            epoch: self.epoch.clone(),
            mode: self.mode,
            reproducibility: self.reproducibility,
            options: self.options.clone(),
        }
    }

    /// Attach the configured engine facade to an applied module state,
    /// adopting its committed environment, epoch, and options (supplemented by
    /// any non-empty builder options) while preserving the builder's mode and
    /// reproducibility profile.
    pub fn build_from_module_state(&self, state: &ModuleApplyState) -> Engine {
        let mut options = state.options().clone();
        for (k, v) in self.options.entries() {
            options.insert(k.clone(), v.clone());
        }
        Engine {
            environment: state.environment().clone(),
            checker_environment: None,
            imported_modules: std::sync::Arc::default(),
            imported_environment: None,
            imported_module_dependencies: std::sync::Arc::default(),
            epoch: state.graph().epoch().clone(),
            mode: self.mode,
            reproducibility: self.reproducibility,
            options,
        }
    }

    /// Construct a bounded Nat-seed engine using the specified admission limits.
    pub fn build_with_nat_seed(
        &self,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<Engine>, EngineAdmissionError> {
        self.build_empty()
            .admit_declaration(
                fln_elab::seed::nat_seed_declaration(),
                &self.options,
                limits,
            )
            .map(|outcome| outcome.map_complete(|admission| admission.engine))
    }

    /// Construct a bounded Nat-seed engine using configured or default calibrated limits.
    pub fn build_nat_seed(&self) -> Result<Outcome<Engine>, EngineAdmissionError> {
        let limits = self.admission_limits.unwrap_or_else(|| {
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
        });
        self.build_with_nat_seed(limits)
    }

    /// Construct a bounded source-seed engine using the specified admission limits.
    ///
    /// The seed's constants carry the pin's `protected` marks (bead `fln-8xz8`): a
    /// headerless file is checked against this seed rather than an imported closure,
    /// so without them `open Nat` would make the pin's protected `Nat.add` available
    /// as `add`. The marks are the generated `fln_elab::seed::protected` table, one
    /// journal entry, as one imported module's tags are.
    pub fn build_with_source_seed(
        &self,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<Engine>, EngineAdmissionError> {
        let mut engine = match self.build_unmarked_source_seed(limits)? {
            Outcome::Complete(engine) => engine,
            other => return Ok(other),
        };
        let protected = fln_elab::seed::protected::seed_protected_names().map_err(|_| {
            EngineAdmissionError::UnexpectedPublication {
                detail: "source seed protected table is malformed",
            }
        })?;
        engine.environment =
            fln_elab::protected_names::register_module(&engine.environment, &protected).map_err(
                |_| EngineAdmissionError::UnexpectedPublication {
                    detail: "source seed protected registration failed",
                },
            )?;
        Ok(Outcome::Complete(engine))
    }

    /// The source seed's constants and registrations, without the `protected` marks:
    /// what `scripts/extract/gen_seed_protected.sh` asks the pin about, so a seed that
    /// gained or lost constants can still be listed for regeneration.
    fn build_unmarked_source_seed(
        &self,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<Engine>, EngineAdmissionError> {
        let mut engine = self.build_empty();
        for declaration in fln_elab::seed::source_seed_declarations() {
            let admission = engine.admit_declaration(declaration, &self.options, limits)?;
            match admission {
                Outcome::Complete(admission) => engine = admission.engine,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
        }
        // The pin's generated recursion helpers are reducible, except the
        // matcher and Nat.add itself, which are implicit_reducible. Their
        // Abbrev hints alone must not override the effective source status.
        for (name, status) in [
            (
                "Nat.casesOn",
                fln_elab::reducibility::Reducibility::Reducible,
            ),
            ("Nat.below", fln_elab::reducibility::Reducibility::Reducible),
            (
                "Nat.brecOn.go",
                fln_elab::reducibility::Reducibility::Reducible,
            ),
            (
                "Nat.brecOn",
                fln_elab::reducibility::Reducibility::Reducible,
            ),
            (
                "Nat.add.match_1",
                fln_elab::reducibility::Reducibility::ImplicitReducible,
            ),
            (
                "Nat.add._f",
                fln_elab::reducibility::Reducibility::Reducible,
            ),
            (
                "Nat.add",
                fln_elab::reducibility::Reducibility::ImplicitReducible,
            ),
        ] {
            engine.environment = fln_elab::reducibility::register(
                &engine.environment,
                &Name::from_components(name.split('.')),
                status,
            )
            .map_err(|_| EngineAdmissionError::UnexpectedPublication {
                detail: "Nat recursion source reducibility registration failed",
            })?;
        }
        for class in ["Inhabited", "Decidable"] {
            engine.environment = fln_elab::instances::register_class(
                &engine.environment,
                &Name::from_components([class]),
            )
            .map_err(|_| EngineAdmissionError::UnexpectedPublication {
                detail: "source class registration failed",
            })?;
        }
        for name in [
            "instInhabitedNat",
            "instInhabitedString",
            "instInhabitedBool",
            "instDecidableTrue",
            "instDecidableFalse",
            "instDecidableNot",
            "instDecidableAnd",
            "instDecidableOr",
            "instDecidableImplies",
            "instDecidableIff",
            "instDecidableEqBool",
            "instDecidableEqNat",
        ] {
            engine.environment = fln_elab::instances::register_instance(
                &engine.environment,
                &Name::from_components([name]),
                1000,
            )
            .map_err(|_| EngineAdmissionError::UnexpectedPublication {
                detail: "source instance registration failed",
            })?;
        }
        let numeric = fln_elab::seed::float_numeric_seed().map_err(|_| {
            EngineAdmissionError::UnexpectedPublication {
                detail: "numeric source seed construction failed",
            }
        })?;
        engine = match engine.admit_declarations(&numeric.declarations, &self.options, limits)? {
            Outcome::Complete(batch) => batch.engine,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        for name in numeric.classes {
            engine.environment = fln_elab::instances::register_class(&engine.environment, &name)
                .map_err(|_| EngineAdmissionError::UnexpectedPublication {
                    detail: "numeric source class registration failed",
                })?;
        }
        for name in numeric.instances {
            let priority = numeric
                .priorities
                .iter()
                .find_map(|(candidate, priority)| (candidate == &name).then_some(*priority))
                .unwrap_or(1000);
            engine.environment =
                fln_elab::instances::register_instance(&engine.environment, &name, priority)
                    .map_err(|_| EngineAdmissionError::UnexpectedPublication {
                        detail: "numeric source instance registration failed",
                    })?;
        }
        for (name, priority) in numeric.defaults {
            engine.environment =
                fln_elab::instances::defaults::register(&engine.environment, &name, priority)
                    .map_err(|_| EngineAdmissionError::UnexpectedPublication {
                        detail: "numeric source default registration failed",
                    })?;
        }
        Ok(Outcome::Complete(engine))
    }

    /// Construct a bounded source-seed engine using configured or default calibrated limits.
    pub fn build_source_seed(&self) -> Result<Outcome<Engine>, EngineAdmissionError> {
        let limits = self.admission_limits.unwrap_or_else(|| {
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
        });
        self.build_with_source_seed(limits)
    }
}

impl Default for EngineBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
pub struct Engine {
    environment: Environment,
    checker_environment: Option<CheckerConstantEnvironment>,
    /// Modules whose `.olean` declarations this engine's environment admitted
    /// through [`Engine::check_olean_modules`]; source imports of them are
    /// satisfied by the base rather than by a source module.
    imported_modules: std::sync::Arc<BTreeSet<Name>>,
    /// Exact environment produced solely by independently checked, named
    /// imports. Later admission preserves this snapshot so artifact production
    /// can detect any ambient declarations or extension changes.
    imported_environment: Option<Environment>,
    /// Direct import edges retained from each checked module's decoded header.
    imported_module_dependencies: std::sync::Arc<BTreeMap<Name, Vec<Name>>>,
    epoch: ModuleEpoch,
    mode: Mode,
    reproducibility: ReproducibilityProfile,
    options: KVMap,
}

fn bounded_source_module_name_depth(
    module: &Name,
    limit: usize,
) -> Result<usize, EngineExecutionError> {
    let mut cursor = module.clone();
    let mut depth = 0_usize;
    while !cursor.is_anonymous() {
        match cursor.leaf_view() {
            LeafView::Str(component) if !component.is_empty() => {}
            LeafView::Anonymous | LeafView::Num(_) | LeafView::Str(_) => {
                return Err(EngineExecutionError::InvalidSourceModuleName {
                    module: module.clone(),
                });
            }
        }
        depth =
            depth
                .checked_add(1)
                .ok_or_else(|| EngineExecutionError::SourceModuleNameLimit {
                    module: module.clone(),
                    observed: usize::MAX,
                    limit,
                })?;
        if depth > limit {
            return Err(EngineExecutionError::SourceModuleNameLimit {
                module: module.clone(),
                observed: depth,
                limit,
            });
        }
        cursor = cursor.parent();
    }
    if depth == 0 {
        return Err(EngineExecutionError::InvalidSourceModuleName {
            module: module.clone(),
        });
    }
    Ok(depth)
}

/// Generate a fresh anonymous-numeric name that does not collide with any
/// existing constant in the environment. The convention is `_root_.<N>` where
/// N begins at `command_index` and increments until a free slot is found.
///
/// This is the same algorithm the bounded source runner uses for synthesized
/// `#eval` and `#check` command declarations. Embedding consumers that batch
/// their own declarations can call this to stay collision-free.
pub fn fresh_generated_command_name(
    environment: &Environment,
    command_index: usize,
) -> Result<Name, EngineExecutionError> {
    let start =
        u64::try_from(command_index).map_err(|_| EngineExecutionError::AllocationFailure {
            resource: "generated source command name space",
            requested: command_index,
        })?;
    for offset in 0..=environment.len() {
        let offset =
            u64::try_from(offset).map_err(|_| EngineExecutionError::AllocationFailure {
                resource: "generated source command name space",
                requested: offset,
            })?;
        let Some(component) = start.checked_add(offset) else {
            break;
        };
        let candidate = Name::num(Name::anonymous(), component);
        if !environment.contains(&candidate) {
            return Ok(candidate);
        }
    }
    Err(EngineExecutionError::UnexpectedPublication {
        detail: "bounded source command could not derive a fresh generated name",
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SourceModuleCommandPolicy {
    ExecutableOnly,
    DefinitionPrefix,
    MixedPrefix,
}

impl SourceModuleCommandPolicy {
    fn require_entry_command(self) -> bool {
        matches!(self, Self::ExecutableOnly)
    }

    fn allow_empty_batch(self) -> bool {
        !matches!(self, Self::ExecutableOnly)
    }

    fn allow_scratch_checks(self) -> bool {
        matches!(self, Self::MixedPrefix)
    }
}

struct PlannedSourceModuleExecution {
    batch: DefinitionBatchExecution,
    command_count: usize,
    execution_command_indices: Option<Vec<usize>>,
}

struct SourceModuleVisibilitySubjects<'a> {
    execution_owners: &'a [usize],
    command_owners: &'a [usize],
    completed: &'a DefinitionBatchExecution,
    check_owners: &'a [usize],
    checks: &'a [SourceCheck],
}

fn verify_source_module_visibility(
    modules: &[SourceModuleInput<'_>],
    dependencies: &[Vec<usize>],
    order: &[usize],
    subjects: SourceModuleVisibilitySubjects<'_>,
    limit: usize,
) -> Result<(), EngineExecutionError> {
    if subjects.execution_owners.len() != subjects.completed.executions.len() {
        return Err(EngineExecutionError::UnexpectedPublication {
            detail: "source command ownership does not cover every completed execution",
        });
    }
    if subjects.check_owners.len() != subjects.checks.len() {
        return Err(EngineExecutionError::UnexpectedPublication {
            detail: "source command ownership does not cover every completed scratch check",
        });
    }
    if subjects
        .execution_owners
        .iter()
        .chain(subjects.check_owners)
        .any(|owner| *owner >= modules.len())
    {
        return Err(EngineExecutionError::UnexpectedPublication {
            detail: "source command ownership names an unknown module",
        });
    }

    let words = modules.len().div_ceil(u64::BITS as usize);
    let cells =
        modules
            .len()
            .checked_mul(words)
            .ok_or(EngineExecutionError::AllocationFailure {
                resource: "source module visibility matrix",
                requested: usize::MAX,
            })?;
    let mut visible = Vec::new();
    visible
        .try_reserve_exact(cells)
        .map_err(|_| EngineExecutionError::AllocationFailure {
            resource: "source module visibility matrix",
            requested: cells,
        })?;
    visible.resize(cells, 0_u64);
    for &module in order {
        let row = module
            .checked_mul(words)
            .ok_or(EngineExecutionError::UnexpectedPublication {
                detail: "source module visibility row overflowed",
            })?;
        visible[row + module / u64::BITS as usize] |= 1_u64 << (module % u64::BITS as usize);
        for &dependency in &dependencies[module] {
            let dependency_row = dependency.checked_mul(words).ok_or(
                EngineExecutionError::UnexpectedPublication {
                    detail: "source dependency visibility row overflowed",
                },
            )?;
            for word in 0..words {
                visible[row + word] |= visible[dependency_row + word];
            }
        }
    }

    source_execution::verify_declarations(modules, subjects, &visible, words, limit)
}

impl Engine {
    /// Construct a new [`EngineBuilder`] configured with the toolchain's pinned
    /// epoch, default mode, standard reproducibility, and empty options.
    pub fn builder() -> EngineBuilder {
        EngineBuilder::new()
    }

    /// The pinned toolchain epoch constant.
    pub fn pinned_epoch() -> ModuleEpoch {
        ModuleEpoch::new(OLEAN_PIN_TAG, OLEAN_PIN_COMMIT)
    }

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
            imported_modules: std::sync::Arc::default(),
            imported_environment: None,
            imported_module_dependencies: std::sync::Arc::default(),
            epoch: Self::pinned_epoch(),
            mode: Mode::DEFAULT,
            reproducibility: ReproducibilityProfile::Standard,
            options: KVMap::new(),
        }
    }

    /// Construct an engine directly from an applied module state, adopting its
    /// committed environment, epoch, and options while preserving standard mode
    /// and reproducibility.
    pub fn from_module_apply_state(state: &ModuleApplyState) -> Self {
        Self::builder().build_from_module_state(state)
    }

    /// Advance this engine's environment and epoch from a newly committed
    /// module state, retaining this engine's mode and reproducibility profile.
    pub fn apply_module_state(&self, state: &ModuleApplyState) -> Self {
        Self {
            environment: state.environment().clone(),
            checker_environment: None,
            imported_modules: std::sync::Arc::default(),
            imported_environment: None,
            imported_module_dependencies: std::sync::Arc::default(),
            epoch: state.graph().epoch().clone(),
            mode: self.mode,
            reproducibility: self.reproducibility,
            options: state.options().clone(),
        }
    }

    /// The toolchain epoch associated with this engine session.
    pub fn toolchain_epoch(&self) -> &ModuleEpoch {
        &self.epoch
    }

    /// The semantic product mode (Faithful, Sound, or Frontier).
    pub fn mode(&self) -> Mode {
        self.mode
    }

    /// The reproducibility profile (Standard or Certified).
    pub fn reproducibility(&self) -> ReproducibilityProfile {
        self.reproducibility
    }

    /// The active options contributing to the logical root.
    pub fn options(&self) -> &KVMap {
        &self.options
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
        Self::builder().build_with_nat_seed(limits)
    }

    /// Construct the bounded Nat/String/Bool source engine through the ordinary K1
    /// and independent-checker council, retaining every checker projection.
    ///
    /// Opaque Nat/String type names plus the exact Bool inductive block check
    /// literals, Bool comparison results, and exact first-order signatures.
    /// The remaining declarations are an exact allowlist of checked Nat
    /// operations with scalar-or-mpz results plus String operations recognized
    /// by the compiler's generated-row bridge. This is not a Prelude substitute:
    /// only Bool's two nullary constructors are live, without source pattern or
    /// recursor elaboration.
    pub fn with_source_seed(
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<Self>, EngineAdmissionError> {
        Self::builder().build_with_source_seed(limits)
    }

    /// Admit one declaration using this engine's active options.
    pub fn admit_decl(
        &self,
        declaration: Declaration,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationAdmission>, EngineAdmissionError> {
        self.admit_declaration(declaration, &self.options, limits)
    }

    /// The immutable environment snapshot against which the next declaration
    /// will be checked.
    pub fn environment(&self) -> &Environment {
        &self.environment
    }

    /// Modules admitted from `.olean` artifacts into this engine's environment.
    pub fn imported_modules(&self) -> &BTreeSet<Name> {
        &self.imported_modules
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
    /// method reconstructs validated non-safe mutual definition units, derives
    /// a stable Kahn order from exact inter-unit constant references, then sends
    /// every unit through the same K1-plus-independent-checker council as
    /// [`Self::admit_declaration`]. Acyclic safe definitions, theorems, and
    /// opaques preserve multi-name metadata while remaining individual units.
    /// The artifact must be import-free:
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
        let ordered = self.decode_olean_module_set(modules, limits)?;
        let bound_base = (self.environment == Environment::new()
            || self
                .imported_environment
                .as_ref()
                .is_some_and(|snapshot| snapshot == &self.environment))
            && modules
                .iter()
                .all(|module| !self.imported_modules.contains(module.name));
        let base_logical_root = self.logical_root(options);
        let mut engine = self.clone();
        let mut checked_modules = Vec::new();
        checked_modules
            .try_reserve_exact(ordered.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean checked module records",
                requested: ordered.len(),
            })?;
        for (name, artifact) in ordered {
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
        let mut imported = (*engine.imported_modules).clone();
        imported.extend(checked_modules.iter().map(|module| module.name.clone()));
        engine.imported_modules = std::sync::Arc::new(imported);
        let mut dependencies = (*self.imported_module_dependencies).clone();
        for module in &checked_modules {
            dependencies.insert(
                module.name.clone(),
                module
                    .decoded
                    .module
                    .imports
                    .iter()
                    .map(|import| import.module.clone())
                    .collect(),
            );
        }
        engine.imported_module_dependencies = std::sync::Arc::new(dependencies);
        engine.imported_environment = bound_base.then(|| engine.environment.clone());
        let result_logical_root = engine.logical_root(options);
        Ok(Outcome::Complete(CheckedOleanSet {
            engine,
            base_logical_root,
            result_logical_root,
            modules: checked_modules,
        }))
    }

    /// Check a closed set of named `.olean` modules module by module, reporting a
    /// verdict for every one instead of stopping at the first failure.
    ///
    /// Modules are visited in the same deterministic import-topological order as
    /// [`Engine::check_olean_modules`]. A module whose artifact does not decode, whose
    /// imports are not all in the set, or which sits on an import cycle is `Failed`;
    /// a module any of whose imports lacks an accepted verdict is `Blocked` and is
    /// never checked. Only whole-set problems (an empty set, the module or byte limit,
    /// a module named twice) are returned as an error.
    pub fn check_olean_frontier(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<OleanFrontier, OleanCheckError> {
        self.check_olean_frontier_observed(modules, options, limits, &mut |_| {})
    }

    /// [`Engine::check_olean_frontier`], reporting each [`OleanFrontierEvent`] as it
    /// happens, so a long lane always names the module in flight and a run stopped
    /// part-way still leaves the rows it had decided. The observer sees the rows in
    /// the order of the returned frontier and cannot change them.
    pub fn check_olean_frontier_observed(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        on_event: &mut dyn FnMut(OleanFrontierEvent<'_>),
    ) -> Result<OleanFrontier, OleanCheckError> {
        self.check_olean_frontier_scheduled(
            modules,
            options,
            limits,
            OleanFrontierJobs::SERIAL,
            on_event,
        )
    }

    /// [`Engine::check_olean_frontier_observed`] over `jobs.threads` modules at once.
    ///
    /// Each module is checked against the environment of exactly its own import
    /// closure: this engine's environment plus what every module of the closure
    /// admitted, merged in frontier order under the rule the serial planner applies
    /// to a repeated name. An identical copy is one constant; a copy that subsumes
    /// or is subsumed by the first keeps the first; any other pair is a
    /// `DuplicateDeclaration` for the importing module. So a verdict depends only on
    /// the module and its closure, never on what ran beside it or finished first,
    /// and the rows and the returned engine are the same at every thread count.
    /// `Decided` events arrive in row order; `Started` events arrive as modules are
    /// dispatched, which above one thread is not row order.
    pub fn check_olean_frontier_scheduled(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        on_event: &mut dyn FnMut(OleanFrontierEvent<'_>),
    ) -> Result<OleanFrontier, OleanCheckError> {
        let owners = olean_module_owners(modules, limits)?;
        let mut decoded: Vec<Option<Result<DecodedOlean, OleanCheckError>>> = modules
            .iter()
            .map(|module| Some(decode_olean_module_input(module, limits)))
            .collect();

        let mut dependencies: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); modules.len()];
        for (index, entry) in decoded.iter_mut().enumerate() {
            let Some(Ok(artifact)) = entry.as_ref() else {
                continue;
            };
            let mut missing = BTreeSet::new();
            for import in &artifact.module.imports {
                match owners.get(&import.module).copied() {
                    Some(owner) if owner != index => {
                        dependencies[index].insert(owner);
                    }
                    Some(_) => {
                        dependencies[index].insert(index);
                    }
                    None => {
                        missing.insert(import.module.clone());
                    }
                }
            }
            if !missing.is_empty() {
                dependencies[index].clear();
                *entry = Some(Err(OleanCheckError::MissingModuleImports {
                    module: modules[index].name.clone(),
                    imports: missing.into_iter().collect(),
                }));
            }
        }

        let mut remaining: Vec<usize> = dependencies.iter().map(BTreeSet::len).collect();
        let mut dependents = vec![Vec::new(); modules.len()];
        for (index, deps) in dependencies.iter().enumerate() {
            for dependency in deps {
                dependents[*dependency].push(index);
            }
        }
        let mut ready: BTreeSet<Name> = modules
            .iter()
            .enumerate()
            .filter(|(index, _)| remaining[*index] == 0)
            .map(|(_, module)| module.name.clone())
            .collect();
        let mut order = Vec::with_capacity(modules.len());
        while let Some(name) = ready.pop_first() {
            let index = owners[&name];
            order.push(index);
            for dependent in &dependents[index] {
                remaining[*dependent] -= 1;
                if remaining[*dependent] == 0 {
                    ready.insert(modules[*dependent].name.clone());
                }
            }
        }
        let cycle: Vec<Name> = modules
            .iter()
            .enumerate()
            .filter(|(index, _)| remaining[*index] != 0)
            .map(|(_, module)| module.name.clone())
            .collect();
        for (index, left) in remaining.iter().enumerate() {
            if *left != 0 {
                decoded[index] = Some(Err(OleanCheckError::ModuleImportCycle {
                    modules: cycle.clone(),
                }));
                order.push(index);
            }
        }

        let count = modules.len();
        let mut position = vec![0_usize; count];
        for (at, index) in order.iter().enumerate() {
            position[*index] = at;
        }
        // Each module's transitive import closure, itself included. Frontier order
        // is topological, so every import's closure exists before its importer's.
        let mut closures: Vec<std::sync::Arc<BTreeSet<usize>>> =
            vec![std::sync::Arc::default(); count];
        for index in &order {
            let mut closure = BTreeSet::new();
            for dependency in &dependencies[*index] {
                if dependency != index {
                    closure.extend(closures[*dependency].iter().copied());
                }
            }
            closure.insert(*index);
            closures[*index] = std::sync::Arc::new(closure);
        }

        // A row waits here from its decision until every earlier row has left.
        let mut pending_rows: Vec<Option<OleanFrontierRow>> = (0..count).map(|_| None).collect();
        let mut decided = vec![false; count];
        let mut accepted: Vec<Option<std::sync::Arc<FrontierAccepted>>> = vec![None; count];
        let mut engines = FrontierEngines::new(
            (0..count)
                .map(|index| frontier_base_of(&dependencies, &closures, |i| position[i], index))
                .collect(),
        );
        let mut rows = Vec::with_capacity(count);
        let threads = jobs.threads.get();

        let base = self;
        let check = |job: FrontierJob| base.frontier_check_module(job, options, limits);
        std::thread::scope(|scope| -> Result<(), OleanCheckError> {
            let (job_sender, job_receiver) = std::sync::mpsc::channel::<FrontierJob>();
            let (done_sender, done_receiver) = std::sync::mpsc::channel::<FrontierDone>();
            let job_receiver = std::sync::Arc::new(std::sync::Mutex::new(job_receiver));
            if threads > 1 {
                for worker in 0..threads {
                    let job_receiver = std::sync::Arc::clone(&job_receiver);
                    let done_sender = done_sender.clone();
                    let check = &check;
                    std::thread::Builder::new()
                        .name(format!("fln-frontier-{worker}"))
                        .stack_size(jobs.worker_stack_bytes)
                        .spawn_scoped(scope, move || {
                            loop {
                                let next = match job_receiver.lock() {
                                    Ok(receiver) => receiver.recv(),
                                    Err(_) => return,
                                };
                                let Ok(job) = next else { return };
                                if done_sender.send(check(job)).is_err() {
                                    return;
                                }
                            }
                        })
                        .map_err(|_| OleanCheckError::InternalInvariant {
                            detail: "could not start a frontier worker thread",
                        })?;
                }
            }
            drop(done_sender);

            let mut running = vec![false; count];
            let mut in_flight = 0_usize;
            // A council result's row, reported the moment it exists.
            let settle =
                |index: usize,
                 pending_rows: &[Option<OleanFrontierRow>],
                 on_event: &mut dyn FnMut(OleanFrontierEvent<'_>)| {
                    if let Some(row) = &pending_rows[index] {
                        on_event(OleanFrontierEvent::Settled {
                            position: position[index] + 1,
                            total: count,
                            row,
                        });
                    }
                };
            let record =
                |done: FrontierDone,
                 running: &mut Vec<bool>,
                 decided: &mut Vec<bool>,
                 accepted: &mut Vec<Option<std::sync::Arc<FrontierAccepted>>>,
                 engines: &mut FrontierEngines,
                 pending_rows: &mut Vec<Option<OleanFrontierRow>>| {
                    running[done.index] = false;
                    decided[done.index] = true;
                    accepted[done.index] = done.accepted.map(std::sync::Arc::new);
                    engines.keep(done.index, done.engine);
                    pending_rows[done.index] = Some(OleanFrontierRow {
                        name: modules[done.index].name.clone(),
                        verdict: done.verdict,
                        elapsed: done.elapsed,
                    });
                };
            loop {
                // Decide every module that needs no council, and collect the ready.
                let mut ready = Vec::new();
                for index in &order {
                    let index = *index;
                    if decided[index] || running[index] {
                        continue;
                    }
                    let verdict = match &decoded[index] {
                        Some(Ok(_)) => {
                            if !dependencies[index]
                                .iter()
                                .all(|dependency| decided[*dependency])
                            {
                                continue;
                            }
                            match dependencies[index]
                                .iter()
                                .find(|dependency| accepted[**dependency].is_none())
                            {
                                Some(blocker) => OleanModuleVerdict::Blocked {
                                    by: modules[*blocker].name.clone(),
                                },
                                None => {
                                    ready.push(index);
                                    continue;
                                }
                            }
                        }
                        Some(Err(_)) => match decoded[index].take() {
                            Some(Err(error)) => frontier_error_verdict(error),
                            _ => continue,
                        },
                        None => frontier_error_verdict(OleanCheckError::InternalInvariant {
                            detail: "frontier module was visited twice",
                        }),
                    };
                    decided[index] = true;
                    engines.release(index, &closures, false)?;
                    let row = pending_rows[index].insert(OleanFrontierRow {
                        name: modules[index].name.clone(),
                        verdict,
                        elapsed: std::time::Duration::ZERO,
                    });
                    on_event(OleanFrontierEvent::Settled {
                        position: position[index] + 1,
                        total: count,
                        row,
                    });
                }

                // Rows leave in frontier order, as soon as every earlier row exists.
                while let Some(row) = order
                    .get(rows.len())
                    .and_then(|index| pending_rows[*index].take())
                {
                    on_event(OleanFrontierEvent::Decided {
                        position: rows.len() + 1,
                        total: count,
                        row: &row,
                    });
                    rows.push(row);
                }
                if rows.len() == count {
                    break;
                }

                let mut dispatched = 0_usize;
                for index in ready {
                    if in_flight >= threads {
                        break;
                    }
                    let Some(Ok(artifact)) = decoded[index].take() else {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "a ready frontier module has no decoded artifact",
                        });
                    };
                    let base = engines.release(index, &closures, true)?;
                    let mut closure: Vec<_> = closures[index]
                        .iter()
                        .filter(|member| **member != index)
                        .filter_map(|member| accepted[*member].clone())
                        .collect();
                    closure.sort_by_key(|module| module.position);
                    on_event(OleanFrontierEvent::Started {
                        position: position[index] + 1,
                        total: count,
                        module: modules[index].name,
                    });
                    running[index] = true;
                    in_flight += 1;
                    dispatched += 1;
                    let job = FrontierJob {
                        index,
                        position: position[index],
                        name: modules[index].name.clone(),
                        artifact,
                        base,
                        closure,
                        retain: false,
                    };
                    if threads == 1 {
                        // Serial: finish this module before deciding anything else,
                        // so the events keep the one-at-a-time order.
                        let done = check(job);
                        in_flight -= 1;
                        let index = done.index;
                        record(
                            done,
                            &mut running,
                            &mut decided,
                            &mut accepted,
                            &mut engines,
                            &mut pending_rows,
                        );
                        settle(index, &pending_rows, on_event);
                        break;
                    }
                    if job_sender.send(job).is_err() {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "every frontier worker thread has stopped",
                        });
                    }
                }
                if threads == 1 {
                    if dispatched == 0 {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "the frontier stalled with modules undecided",
                        });
                    }
                    continue;
                }
                if in_flight == 0 {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "the frontier stalled with modules undecided",
                    });
                }
                let done =
                    done_receiver
                        .recv()
                        .map_err(|_| OleanCheckError::InternalInvariant {
                            detail: "every frontier worker thread has stopped",
                        })?;
                in_flight -= 1;
                let index = done.index;
                record(
                    done,
                    &mut running,
                    &mut decided,
                    &mut accepted,
                    &mut engines,
                    &mut pending_rows,
                );
                settle(index, &pending_rows, on_event);
            }
            drop(job_sender);
            Ok(())
        })?;

        // A merge conflict between modules that never meet is not an error of the
        // run: every row above is already decided (fln-elp6's stdlib run lost its
        // whole --json to two executables' `main`).
        let engine = self
            .frontier_union_engine(order.iter().filter_map(|index| accepted[*index].as_deref()));
        Ok(OleanFrontier { engine, rows })
    }

    /// One engine holding exactly these accepted modules, merged in this order by
    /// the same rule as every closure, or the duplicate that rules it out.
    fn frontier_union_engine<'a>(
        &self,
        accepted: impl IntoIterator<Item = &'a FrontierAccepted>,
    ) -> Result<Engine, OleanCheckError> {
        let mut engine = self.clone();
        let mut environment = self.environment.clone();
        let mut imported = (*self.imported_modules).clone();
        for module in accepted {
            for entry in &module.admitted {
                environment = merge_frontier_entry(environment, entry)?;
            }
            imported.insert(module.name.clone());
        }
        engine.environment = environment;
        engine.checker_environment = None;
        engine.imported_modules = std::sync::Arc::new(imported);
        Ok(engine)
    }

    /// [`Engine::check_olean_modules`] over `jobs.threads` modules at once, returning
    /// what the serial door returns.
    ///
    /// The set is decoded, refused and ordered by the serial door's own planner, so
    /// every whole-set refusal is the serial one. Each module then goes through the
    /// frontier's per-module council ([`Engine::check_olean_frontier_scheduled`])
    /// against exactly its own import closure, and the serial result is reassembled
    /// in the serial order: one environment merged from what each module admitted,
    /// each module's two logical roots over that cumulative environment, its checker
    /// rows, and the retained checker projection of every admitted declaration. A
    /// module that repeats a name which an earlier module outside its closure
    /// declared is re-planned against the cumulative environment, so its rows split
    /// as the serial planner splits them.
    ///
    /// The serial door stops at the first module of that order whose check does not
    /// complete, and so does this one: it returns that module's error, non-answer or
    /// fault. Once a module has stopped no later module is dispatched; earlier ones
    /// still finish, since one of them may be the first to stop.
    ///
    /// One thread, or a base engine whose environment is not empty, takes the serial
    /// door itself: over a nonempty base the serial projection also holds the base
    /// constants each review covered, which the per-module projections do not
    /// reproduce. `cancellation` is sampled whenever a module is decided; a running
    /// council is not interrupted, and a set whose answer is already fixed is
    /// returned rather than discarded.
    pub fn check_olean_modules_scheduled(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<CheckedOleanSet>, OleanCheckError> {
        if jobs.threads.get() == 1 || !self.environment.is_empty() {
            return self.check_olean_modules(modules, options, limits);
        }
        let ordered = self.decode_olean_module_set(modules, limits)?;
        let bound_base = (self.environment == Environment::new()
            || self
                .imported_environment
                .as_ref()
                .is_some_and(|snapshot| snapshot == &self.environment))
            && modules
                .iter()
                .all(|module| !self.imported_modules.contains(module.name));
        let names: Vec<Name> = ordered.iter().map(|(name, _)| name.clone()).collect();
        let scheduled =
            match self.schedule_olean_module_set(ordered, options, limits, jobs, cancellation)? {
                Outcome::Complete(scheduled) => scheduled,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        self.reassemble_olean_module_set(names, scheduled, bound_base, options, limits)
            .map(Outcome::Complete)
    }

    /// Check a decoded set, in the serial door's order, over `jobs.threads` workers,
    /// each module against its own import closure, keeping what the serial result
    /// is reassembled from. The answer is the serial one: the first module of the
    /// order whose check did not complete decides it.
    fn schedule_olean_module_set(
        &self,
        ordered: Vec<(Name, DecodedOlean)>,
        options: &KVMap,
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<Vec<ScheduledOleanModule>>, OleanCheckError> {
        let count = ordered.len();
        let positions: BTreeMap<Name, usize> = ordered
            .iter()
            .enumerate()
            .map(|(position, (name, _))| (name.clone(), position))
            .collect();
        let mut names = Vec::with_capacity(count);
        let mut artifacts = Vec::with_capacity(count);
        let mut dependencies: Vec<BTreeSet<usize>> = Vec::with_capacity(count);
        // Each module's transitive import closure, itself included.
        let mut closures: Vec<std::sync::Arc<BTreeSet<usize>>> = Vec::with_capacity(count);
        for (position, (name, artifact)) in ordered.into_iter().enumerate() {
            let mut imports = BTreeSet::new();
            let mut closure = BTreeSet::new();
            for import in &artifact.module.imports {
                let Some(&dependency) = positions
                    .get(&import.module)
                    .filter(|dependency| **dependency < position)
                else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "a serially ordered module imports a module that is not before it",
                    });
                };
                imports.insert(dependency);
                closure.extend(closures[dependency].iter().copied());
            }
            closure.insert(position);
            names.push(name);
            artifacts.push(Some(artifact));
            dependencies.push(imports);
            closures.push(std::sync::Arc::new(closure));
        }

        let threads = jobs.threads.get();
        let mut accepted: Vec<Option<std::sync::Arc<FrontierAccepted>>> = vec![None; count];
        let mut engines = FrontierEngines::new(
            (0..count)
                .map(|index| frontier_base_of(&dependencies, &closures, |i| i, index))
                .collect(),
        );
        let mut retained: Vec<Option<FrontierRetained>> = (0..count).map(|_| None).collect();
        let mut decided = vec![false; count];
        let mut running = vec![false; count];
        // The first position whose check did not complete, and how it ended.
        let mut stop_at = count;
        let mut stopped: Option<(OleanModuleVerdict, Option<FrontierRetained>)> = None;
        let mut cancelled = false;
        let base = self;
        let check = |job: FrontierJob| base.frontier_check_module(job, options, limits);
        std::thread::scope(|scope| -> Result<(), OleanCheckError> {
            let (job_sender, job_receiver) = std::sync::mpsc::channel::<FrontierJob>();
            let (done_sender, done_receiver) = std::sync::mpsc::channel::<FrontierDone>();
            let job_receiver = std::sync::Arc::new(std::sync::Mutex::new(job_receiver));
            for worker in 0..threads {
                let job_receiver = std::sync::Arc::clone(&job_receiver);
                let done_sender = done_sender.clone();
                let check = &check;
                std::thread::Builder::new()
                    .name(format!("fln-olean-set-{worker}"))
                    .stack_size(jobs.worker_stack_bytes)
                    .spawn_scoped(scope, move || {
                        loop {
                            let next = match job_receiver.lock() {
                                Ok(receiver) => receiver.recv(),
                                Err(_) => return,
                            };
                            let Ok(job) = next else { return };
                            if done_sender.send(check(job)).is_err() {
                                return;
                            }
                        }
                    })
                    .map_err(|_| OleanCheckError::InternalInvariant {
                        detail: "could not start a module-set worker thread",
                    })?;
            }
            drop(done_sender);

            let mut in_flight = 0_usize;
            loop {
                cancelled = cancelled || cancellation.is_some_and(CancellationProbe::is_cancelled);
                // Dispatch in serial order, never past the first stopped module: a
                // module is ready once every import it names has been accepted.
                if !cancelled {
                    for index in 0..stop_at {
                        if in_flight >= threads {
                            break;
                        }
                        if decided[index]
                            || running[index]
                            || !dependencies[index]
                                .iter()
                                .all(|dependency| accepted[*dependency].is_some())
                        {
                            continue;
                        }
                        let Some(artifact) = artifacts[index].take() else {
                            return Err(OleanCheckError::InternalInvariant {
                                detail: "a ready module-set member has no decoded artifact",
                            });
                        };
                        let base = engines.release(index, &closures, true)?;
                        let mut closure: Vec<_> = closures[index]
                            .iter()
                            .filter(|member| **member != index)
                            .filter_map(|member| accepted[*member].clone())
                            .collect();
                        closure.sort_by_key(|module| module.position);
                        running[index] = true;
                        in_flight += 1;
                        let job = FrontierJob {
                            index,
                            position: index,
                            name: names[index].clone(),
                            artifact,
                            base,
                            closure,
                            retain: true,
                        };
                        if job_sender.send(job).is_err() {
                            return Err(OleanCheckError::InternalInvariant {
                                detail: "every module-set worker thread has stopped",
                            });
                        }
                    }
                }
                if in_flight == 0 {
                    if cancelled || decided[..stop_at].iter().all(|done| *done) {
                        break;
                    }
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "the module-set schedule stalled with modules undecided",
                    });
                }
                let done =
                    done_receiver
                        .recv()
                        .map_err(|_| OleanCheckError::InternalInvariant {
                            detail: "every module-set worker thread has stopped",
                        })?;
                in_flight -= 1;
                let FrontierDone {
                    index,
                    verdict,
                    accepted: module,
                    engine,
                    retained: kept,
                    ..
                } = done;
                running[index] = false;
                decided[index] = true;
                match (module, kept) {
                    (Some(module), Some(checked @ FrontierRetained::Checked { .. })) => {
                        accepted[index] = Some(std::sync::Arc::new(module));
                        engines.keep(index, engine);
                        retained[index] = Some(checked);
                    }
                    (Some(_), _) => {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "an accepted module-set member kept no checked record",
                        });
                    }
                    (None, kept) => {
                        if index < stop_at {
                            stop_at = index;
                            stopped = Some((verdict, kept));
                        }
                    }
                }
            }
            drop(job_sender);
            Ok(())
        })?;

        if !decided[..stop_at].iter().all(|done| *done) {
            // Cancelled before the answer was fixed.
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "olean-modules/scheduled",
            )));
        }
        if let Some((verdict, kept)) = stopped {
            return match (kept, verdict) {
                (Some(FrontierRetained::Failed(error)), _) => Err(error),
                (_, OleanModuleVerdict::Inconclusive(reason)) => Ok(Outcome::Inconclusive(reason)),
                (_, OleanModuleVerdict::InternalFault(fault)) => Ok(Outcome::InternalFault(fault)),
                _ => Err(OleanCheckError::InternalInvariant {
                    detail: "a stopped module-set member kept neither its error nor its non-answer",
                }),
            };
        }
        let mut scheduled = Vec::with_capacity(count);
        for (module, kept) in accepted.into_iter().zip(retained) {
            let (
                Some(module),
                Some(FrontierRetained::Checked {
                    decoded,
                    declarations,
                    closure_digests,
                    checker_entries,
                }),
            ) = (module, kept)
            else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "a decided module-set member lost its checked record",
                });
            };
            scheduled.push(ScheduledOleanModule {
                module,
                decoded: *decoded,
                declarations,
                closure_digests,
                checker_entries,
            });
        }
        Ok(Outcome::Complete(scheduled))
    }

    /// The serial door's [`CheckedOleanSet`] from modules each checked against its
    /// own closure, visited in the serial order. The environment, roots, rows and
    /// retained checker projection are those of admitting the modules one after
    /// another into this (empty) engine.
    fn reassemble_olean_module_set(
        &self,
        names: Vec<Name>,
        scheduled: Vec<ScheduledOleanModule>,
        bound_base: bool,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<CheckedOleanSet, OleanCheckError> {
        let invariant = |detail| OleanCheckError::InternalInvariant { detail };
        let base_logical_root = self.logical_root(options);
        let mut environment = self.environment.clone();
        let mut root = base_logical_root;
        let mut admitted_any = false;
        let mut candidates = Vec::new();
        let mut checked_modules = Vec::new();
        checked_modules
            .try_reserve_exact(scheduled.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean checked module records",
                requested: scheduled.len(),
            })?;
        for (name, scheduled) in names.into_iter().zip(scheduled) {
            let ScheduledOleanModule {
                module,
                decoded,
                declarations,
                closure_digests,
                checker_entries,
            } = scheduled;
            if closure_digests.len() != decoded.constants.len() {
                return Err(invariant(
                    "a module's closure digests do not cover its constants",
                ));
            }
            let module_base_root = root;
            // A constant the serial environment already holds, while this module's
            // closure did not (or held another copy), is planned differently there.
            let own: BTreeSet<&Name> = module
                .admitted
                .iter()
                .map(|entry| entry.declaration().name())
                .collect();
            let repeats = decoded
                .constants
                .iter()
                .zip(&closure_digests)
                .any(|(info, copy)| {
                    environment.entry(info.name()).is_some_and(|present| {
                        own.contains(info.name())
                            || copy.is_none_or(|copy| copy != present.digest())
                    })
                });
            let declarations = if repeats {
                serial_olean_rows(&environment, &decoded, declarations, limits)?
            } else {
                declarations
            };
            let mut added = Vec::new();
            for entry in &module.admitted {
                let name = entry.declaration().name();
                if environment.contains(name) {
                    environment = merge_frontier_entry(environment, entry)?;
                } else {
                    environment = environment
                        .with_entry(entry.clone())
                        .map_err(|_| invariant("an absent admitted constant could not be added"))?;
                    added.push(name.clone());
                }
            }
            if !added.is_empty() {
                admitted_any = true;
                root = environment.logical_root(options);
                for name in added {
                    match checker_entries.get(&name) {
                        Some(Ok(entry)) => candidates.push(entry.clone()),
                        Some(Err(detail)) => return Err(invariant(detail)),
                        None => {
                            return Err(invariant(
                                "an admitted constant is missing from its checker projection",
                            ));
                        }
                    }
                }
            }
            checked_modules.push(CheckedOleanModule {
                name,
                decoded,
                base_logical_root: module_base_root,
                result_logical_root: root,
                declarations,
            });
        }

        // Serially, every admission extends the retained projection with its own
        // candidate; over an empty base nothing else is ever covered.
        let checker_environment = if admitted_any {
            let mut projection = self.checker_environment.clone().unwrap_or_default();
            for entry in candidates {
                projection = match projection.extend(entry, limits.admission.checker.environment) {
                    CheckerEnvironmentOutcome::Complete { environment, .. } => environment,
                    _ => {
                        return Err(invariant(
                            "the admitted checker entries could not be reassembled",
                        ));
                    }
                };
            }
            Some(projection)
        } else {
            self.checker_environment.clone()
        };
        let mut imported = (*self.imported_modules).clone();
        imported.extend(checked_modules.iter().map(|module| module.name.clone()));
        let mut dependencies = (*self.imported_module_dependencies).clone();
        for module in &checked_modules {
            dependencies.insert(
                module.name.clone(),
                module
                    .decoded
                    .module
                    .imports
                    .iter()
                    .map(|import| import.module.clone())
                    .collect(),
            );
        }
        let imported_environment = bound_base.then(|| environment.clone());
        let engine = Engine {
            environment,
            checker_environment,
            imported_modules: std::sync::Arc::new(imported),
            imported_environment,
            imported_module_dependencies: std::sync::Arc::new(dependencies),
            epoch: self.epoch.clone(),
            mode: self.mode,
            reproducibility: self.reproducibility,
            options: if admitted_any {
                options.clone()
            } else {
                self.options.clone()
            },
        };
        Ok(CheckedOleanSet {
            engine,
            base_logical_root,
            result_logical_root: root,
            modules: checked_modules,
        })
    }

    /// Check one frontier module against its import closure's environment.
    fn frontier_check_module(
        &self,
        job: FrontierJob,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> FrontierDone {
        let started = std::time::Instant::now();
        let (index, retain) = (job.index, job.retain);
        frontier_guarded(index, retain, started, || {
            self.frontier_check_module_unguarded(job, options, limits, started)
        })
    }

    fn frontier_check_module_unguarded(
        &self,
        job: FrontierJob,
        options: &KVMap,
        limits: OleanCheckLimits,
        started: std::time::Instant,
    ) -> FrontierDone {
        let index = job.index;
        let retain = job.retain;
        let finish = |verdict: OleanModuleVerdict,
                      accepted: Option<(FrontierAccepted, Engine)>,
                      retained: Option<FrontierRetained>| {
            let (accepted, engine) = accepted.unzip();
            FrontierDone {
                index,
                verdict,
                accepted,
                engine,
                elapsed: started.elapsed(),
                retained,
            }
        };
        let failed = |error: OleanCheckError| {
            let retained = retain.then(|| FrontierRetained::Failed(error.clone()));
            finish(frontier_error_verdict(error), None, retained)
        };
        let engine = match self.frontier_closure_engine(&job) {
            Ok(engine) => engine,
            Err(error) => return failed(error),
        };
        let start = engine.environment.clone();
        match engine.check_decoded_olean_unrooted(job.artifact, options, limits) {
            Ok(Outcome::Complete(checked)) => {
                let declarations = checked.declarations.len();
                let admitted: Vec<EnvironmentEntry> = checked
                    .decoded
                    .constants
                    .iter()
                    .filter(|info| !start.contains(info.name()))
                    .filter_map(|info| checked.engine.environment.entry(info.name()))
                    .collect();
                let mut engine = checked.engine;
                let mut imported = (*engine.imported_modules).clone();
                imported.insert(job.name.clone());
                engine.imported_modules = std::sync::Arc::new(imported);
                let retained = retain.then(|| FrontierRetained::Checked {
                    closure_digests: checked
                        .decoded
                        .constants
                        .iter()
                        .map(|info| engine.environment.entry(info.name()).map(|e| e.digest()))
                        .collect(),
                    checker_entries: frontier_checker_entries(&engine, &admitted, limits),
                    decoded: Box::new(checked.decoded),
                    declarations: checked.declarations,
                });
                finish(
                    OleanModuleVerdict::Accepted { declarations },
                    Some((
                        FrontierAccepted {
                            index,
                            position: job.position,
                            name: job.name,
                            admitted,
                        },
                        engine,
                    )),
                    retained,
                )
            }
            Ok(Outcome::Inconclusive(reason)) => {
                finish(OleanModuleVerdict::Inconclusive(reason), None, None)
            }
            Ok(Outcome::InternalFault(fault)) => {
                finish(OleanModuleVerdict::InternalFault(fault), None, None)
            }
            Err(error) => failed(error),
        }
    }

    /// The engine a frontier module is checked with: its import with the largest
    /// closure (the earlier on a tie), plus what the rest of its closure admitted.
    fn frontier_closure_engine(&self, job: &FrontierJob) -> Result<Engine, OleanCheckError> {
        let Some(base) = &job.base else {
            return Ok(self.clone());
        };
        let mut engine = (*base.engine).clone();
        let mut environment = engine.environment.clone();
        let mut imported = (*engine.imported_modules).clone();
        for module in &job.closure {
            if base.closure.contains(&module.index) {
                continue;
            }
            for entry in &module.admitted {
                environment = merge_frontier_entry(environment, entry)?;
            }
            imported.insert(module.name.clone());
        }
        engine.environment = environment;
        engine.imported_modules = std::sync::Arc::new(imported);
        Ok(engine)
    }

    /// Decode a closed set of named `.olean` modules and return them in the
    /// deterministic import-topological order both import trust levels use.
    ///
    /// Every direct import must name another input row, and a name declared by
    /// several modules must be a repeat the Reference's import accepts
    /// (`subsumesInfo`); nothing is admitted here.
    fn decode_olean_module_set(
        &self,
        modules: &[OleanModuleInput<'_>],
        limits: OleanCheckLimits,
    ) -> Result<Vec<(Name, DecodedOlean)>, OleanCheckError> {
        let owners = olean_module_owners(modules, limits)?;

        let mut decoded = Vec::new();
        decoded.try_reserve_exact(modules.len()).map_err(|_| {
            OleanCheckError::AllocationFailure {
                resource: ".olean decoded module set",
                requested: modules.len(),
            }
        })?;
        for module in modules {
            let artifact = decode_olean_module_input(module, limits)?;
            decoded.push(Some((module.name.clone(), artifact)));
        }

        // The per-module companion guard (see `decode_olean_module_artifacts`)
        // proves no single module loses a declaration its exported part
        // declared. It says nothing about the SET: two modules can decode to
        // declarations sharing a name, and at corpus scale they do. Across the
        // 2,431 pinned modules that carry a complete chain, 215,111 per-module
        // constants collapse to 214,919 distinct names — 128 names are declared
        // by more than one module, all re-generated `eq_N` and `congr_simp`
        // lemmas.
        //
        // A repeat is therefore NOT a fault by itself, and refusing one would
        // reject the real corpus. Nor does a repeat need to be byte-identical:
        // the Reference's import accepts one copy that subsumes the other
        // (`subsumesInfo`: the same name, level parameters, and a statement
        // equal up to binder names and binder info, with the kind rules in
        // `olean_imports`), and the pinned `Init` closure carries 16 such pairs:
        // identical statements, different proof terms, so the per-module plan
        // rechecks each repeat's own proof. A repeat that
        // neither side subsumes is a fault: the set has no single meaning for
        // that name, and admission in dependency order would let whichever
        // module sorted first silently win while the loser surfaced as an
        // already-declared rejection from the kernel — attributing to the
        // kernel what is a property of the input. This names both modules
        // instead, at decode time.
        let mut declared: BTreeMap<&Name, (&Name, &ConstantInfo)> = BTreeMap::new();
        for entry in &decoded {
            let Some((module_name, artifact)) = entry.as_ref() else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "decoded module disappeared before the set-wide declaration scan",
                });
            };
            for info in &artifact.constants {
                match declared.get(info.name()) {
                    Some(&(owner, previous)) if previous != info => {
                        let lookup = |name: &Name| {
                            declared
                                .get(name)
                                .map(|entry| entry.1)
                                .or_else(|| self.environment.find(name))
                        };
                        if !olean_imports::subsumes_info(&lookup, previous, info)
                            && !olean_imports::subsumes_info(&lookup, info, previous)
                        {
                            return Err(OleanCheckError::ConflictingModuleDeclaration {
                                name: info.name().clone(),
                                first_module: owner.clone(),
                                second_module: module_name.clone(),
                            });
                        }
                    }
                    // An identical or subsuming repeat is coherent. Keep the
                    // first owner so a later conflict is reported against it;
                    // the per-module plan rechecks a subsuming copy's body.
                    Some(_) => {}
                    None => {
                        declared.insert(info.name(), (module_name, info));
                    }
                }
            }
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

        let mut ordered = Vec::new();
        ordered
            .try_reserve_exact(order.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean ordered module set",
                requested: order.len(),
            })?;
        for index in order {
            let Some(slot) = decoded.get_mut(index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "topological module is outside the decoded table",
                });
            };
            let Some(module) = slot.take() else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "topological module was consumed more than once",
                });
            };
            ordered.push(module);
        }
        Ok(ordered)
    }

    pub fn check_decoded_olean(
        &self,
        decoded: DecodedOlean,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<CheckedOlean>, OleanCheckError> {
        let checked = match self.check_decoded_olean_unrooted(decoded, options, limits)? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let base_logical_root = self.logical_root(options);
        let result_logical_root = if checked.unchanged {
            base_logical_root
        } else {
            checked.engine.logical_root(options)
        };
        Ok(Outcome::Complete(CheckedOlean {
            engine: checked.engine,
            decoded: checked.decoded,
            base_logical_root,
            result_logical_root,
            declarations: checked.declarations,
        }))
    }

    /// [`Engine::check_decoded_olean`] without the two whole-environment logical
    /// roots, for the frontier, whose rows carry neither. Each root encodes and
    /// hashes every constant of the environment, which on a Mathlib-sized closure
    /// is a large share of a small module's check.
    fn check_decoded_olean_unrooted(
        &self,
        decoded: DecodedOlean,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<UnrootedOlean>, OleanCheckError> {
        let plan = plan_olean_declarations(&self.environment, &decoded.constants, limits)?;
        // The checker seat judges each declaration against its own reading of the
        // artifact (bead `franken_lean-z8j.1.14`); without one it has no
        // independent answer about any of them.
        let readings = match ArtifactReadings::new(&decoded.independent) {
            Ok(readings) => readings,
            Err(reason) => {
                return Ok(Outcome::Inconclusive(Inconclusive::dependency_unavailable(
                    reason,
                )));
            }
        };
        // A constant already present is reported checked because the primary
        // decode equals one admitted earlier, and no council reviews it.
        if !plan.already_present.is_empty() {
            let by_name: BTreeMap<&Name, &ConstantInfo> = decoded
                .constants
                .iter()
                .map(|info| (info.name(), info))
                .collect();
            for (name, _) in &plan.already_present {
                let Some(info) = by_name.get(name) else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "an already-present declaration is not in the decoded table",
                    });
                };
                if let Some(objection) = readings.objection(info, limits.admission.checker.decode) {
                    return unreviewed_reading_refusal(name, objection);
                }
            }
        }
        let reading = ReadingCheck::Artifact(&readings);
        if plan.order.is_empty() {
            let mut checked: Vec<OleanCheckedDeclaration> = plan
                .already_present
                .into_iter()
                .map(|(name, checker)| OleanCheckedDeclaration { name, checker })
                .collect();
            match self.recheck_subsumed_repeats(
                plan.subsumed,
                options,
                limits.admission,
                reading,
            )? {
                Outcome::Complete(rechecked) => checked.extend(rechecked),
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
            return Ok(Outcome::Complete(UnrootedOlean {
                engine: self.clone(),
                decoded,
                declarations: checked,
                unchanged: true,
            }));
        }

        let mut declarations = Vec::new();
        declarations
            .try_reserve_exact(plan.order.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean declaration batch",
                requested: plan.order.len(),
            })?;
        for index in &plan.order {
            let Some(unit) = plan.units.get(*index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "planned declaration unit is outside the unit table",
                });
            };
            declarations.push(unit.declaration.clone());
        }
        let (engine, checkers) = match self
            .admit_declarations_unrooted(&declarations, options, limits.admission, reading)
            .map_err(OleanCheckError::Admission)?
        {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        if checkers.len() != plan.order.len() {
            return Err(OleanCheckError::InternalInvariant {
                detail: "admission result count differs from the authority-unit plan",
            });
        }
        let mut checked = Vec::new();
        checked
            .try_reserve_exact(decoded.constants.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean completed declaration records",
                requested: decoded.constants.len(),
            })?;
        for (unit_index, checker) in plan.order.iter().zip(&checkers) {
            let Some(unit) = plan.units.get(*unit_index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "completed declaration unit is outside the unit table",
                });
            };
            for name in &unit.names {
                checked.push(OleanCheckedDeclaration {
                    name: name.clone(),
                    checker: *checker,
                });
            }
        }
        for (name, checker) in plan.already_present {
            checked.push(OleanCheckedDeclaration { name, checker });
        }
        match engine.recheck_subsumed_repeats(plan.subsumed, options, limits.admission, reading)? {
            Outcome::Complete(rechecked) => checked.extend(rechecked),
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        }
        if checked.len() != decoded.constants.len() {
            return Err(OleanCheckError::InternalInvariant {
                detail: "checked declaration count differs from the decoded declaration table",
            });
        }
        Ok(Outcome::Complete(UnrootedOlean {
            engine,
            decoded,
            declarations: checked,
            unchanged: false,
        }))
    }

    /// Check the body of each repeat the Reference's import accepts over an
    /// already admitted copy (`subsumesInfo`), so that "checked" stays literal.
    ///
    /// A theorem is admitted under a fresh scratch name against this engine and
    /// the successor is discarded: the published environment keeps the first
    /// copy. An axiom repeat has no body, and its statement is equal up to
    /// binder names and binder info to one already checked.
    ///
    /// Each repeat is compared with the checker's own reading as the artifact
    /// states it, before any renaming: a theorem's council then carries that
    /// comparison, and an axiom repeat, which no council reviews, is refused on a
    /// difference here.
    fn recheck_subsumed_repeats(
        &self,
        repeats: Vec<ConstantInfo>,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        reading: ReadingCheck<'_>,
    ) -> Result<Outcome<Vec<OleanCheckedDeclaration>>, OleanCheckError> {
        let mut checked = Vec::new();
        for repeat in repeats {
            let name = repeat.name().clone();
            let objection = match reading {
                ReadingCheck::Artifact(readings) => {
                    readings.objection(&repeat, limits.checker.decode)
                }
                ReadingCheck::Unread | ReadingCheck::Settled(_) => None,
            };
            let checker = match repeat {
                ConstantInfo::Thm(mut theorem) => {
                    let mut scratch = Name::str(name.clone(), "_fln_subsumed_repeat");
                    let mut suffix = 0_u64;
                    while self.environment.contains(&scratch) {
                        suffix += 1;
                        scratch =
                            Name::num(Name::str(name.clone(), "_fln_subsumed_repeat"), suffix);
                    }
                    theorem.base.name = scratch.clone();
                    for member in &mut theorem.all {
                        if *member == name {
                            *member = scratch.clone();
                        }
                    }
                    let reading = match reading {
                        ReadingCheck::Artifact(_) => ReadingCheck::Settled(objection.as_ref()),
                        other => other,
                    };
                    match self
                        .admit_declaration_unrooted(
                            Declaration::Thm(theorem),
                            options,
                            limits,
                            reading,
                        )
                        .map_err(OleanCheckError::Admission)?
                    {
                        Outcome::Complete(admission) => admission.checker,
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    }
                }
                ConstantInfo::Axiom(_) => {
                    if let Some(objection) = objection {
                        return unreviewed_reading_refusal(&name, objection);
                    }
                    CheckerAgreement {
                        schema: "fln-checker/v1",
                        ground: CheckerAdmissionGround::AxiomPreamble,
                    }
                }
                _ => {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "only theorems and axioms can subsume an admitted repeat",
                    });
                }
            };
            checked.push(OleanCheckedDeclaration { name, checker });
        }
        Ok(Outcome::Complete(checked))
    }

    /// Admit and publish one declaration without compiling or executing it.
    ///
    /// This is the environment-building counterpart to
    /// [`Self::execute_definition`]. It currently accepts the declaration kinds
    /// on which both K1 and the independent checker can issue a completed
    /// verdict: axioms, definitions, theorems, opaques, non-safe mutual
    /// definition blocks, the fixed quotient initialization unit, and safe,
    /// nonrecursive, non-nested, parameter-free `Type` inductives with bounded
    /// constructor fields. Other inductive families remain checker
    /// non-answers until an independent complete-unit ground exists for them.
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
        let admitted = match self.admit_declaration_unrooted(
            declaration,
            options,
            limits,
            ReadingCheck::Unread,
        )? {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // `self` is immutable, so its root is the same before or after the council.
        let base_logical_root = self.logical_root(options);
        let result_logical_root = admitted.engine.environment.logical_root(options);
        Ok(Outcome::Complete(DeclarationAdmission {
            engine: admitted.engine,
            declaration: admitted.declaration,
            base_logical_root,
            result_logical_root,
            checker: admitted.checker,
        }))
    }

    /// [`Self::admit_declaration`] without the two logical roots. Each root is a
    /// pass over the whole environment (every constant's name encoded and sorted),
    /// about 0.8 s at Mathlib's 133K constants; the `.olean` check admits a module
    /// one declaration at a time and reads neither, so it pays for them nowhere.
    ///
    /// `reading` is what the checker seat compares the declaration against: an
    /// `.olean` declaration must be the one the checker itself read from the
    /// artifact (bead `franken_lean-z8j.1.14`).
    fn admit_declaration_unrooted(
        &self,
        declaration: Declaration,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        reading: ReadingCheck<'_>,
    ) -> Result<Outcome<UnrootedAdmission>, EngineAdmissionError> {
        if !matches!(
            declaration,
            Declaration::Axiom(_)
                | Declaration::Defn(_)
                | Declaration::Thm(_)
                | Declaration::Opaque(_)
                | Declaration::Mutual(_)
                | Declaration::Inductive(_)
                | Declaration::Quotient(_)
        ) {
            return Err(EngineAdmissionError::UnsupportedDeclaration {
                kind: declaration_kind(&declaration),
            });
        }

        let checker_review = review_with_independent_checker(
            &self.environment,
            self.checker_environment.as_ref(),
            &declaration,
            limits.checker,
            reading,
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
            // A halt with no disagreement is a non-answer about the declaration
            // (FL-INV-07); only a disagreement is evidence against it.
            CouncilOutcome::Halted(halt) if halt.is_purely_resource() => {
                return Err(EngineAdmissionError::CouncilNoAnswer {
                    summary: halt.summary(),
                });
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
        let expects_block = matches!(
            declaration,
            Declaration::Mutual(_) | Declaration::Inductive(_) | Declaration::Quotient(_)
        );
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

        Ok(Outcome::Complete(UnrootedAdmission {
            engine: Engine {
                environment,
                checker_environment: Some(checker_environment),
                imported_modules: std::sync::Arc::clone(&self.imported_modules),
                imported_environment: self.imported_environment.clone(),
                imported_module_dependencies: std::sync::Arc::clone(
                    &self.imported_module_dependencies,
                ),
                epoch: self.epoch.clone(),
                mode: self.mode,
                reproducibility: self.reproducibility,
                options: options.clone(),
            },
            declaration,
            checker,
        }))
    }

    /// The `.olean` check's batch: [`Self::admit_declarations`] without the root
    /// transitions it records for continuity checks, which the check never reads.
    /// A Mathlib module of a few hundred declarations spent most of its council
    /// time recomputing them, two whole-environment passes per declaration.
    fn admit_declarations_unrooted(
        &self,
        declarations: &[Declaration],
        options: &KVMap,
        limits: EngineAdmissionLimits,
        reading: ReadingCheck<'_>,
    ) -> Result<Outcome<(Engine, Vec<CheckerAgreement>)>, EngineAdmissionError> {
        if declarations.is_empty() {
            return Err(EngineAdmissionError::EmptyBatch);
        }
        let mut checkers = Vec::new();
        checkers
            .try_reserve_exact(declarations.len())
            .map_err(|_| EngineAdmissionError::AllocationFailure {
                resource: "declaration batch results",
                requested: declarations.len(),
            })?;
        let mut engine = self.clone();
        for (index, declaration) in declarations.iter().cloned().enumerate() {
            let admitted =
                match engine.admit_declaration_unrooted(declaration, options, limits, reading) {
                    Ok(Outcome::Complete(admitted)) => admitted,
                    Ok(Outcome::Inconclusive(reason)) => return Ok(Outcome::Inconclusive(reason)),
                    Ok(Outcome::InternalFault(fault)) => return Ok(Outcome::InternalFault(fault)),
                    Err(error) => {
                        return Err(EngineAdmissionError::BatchDeclaration {
                            index,
                            error: Box::new(error),
                        });
                    }
                };
            engine = admitted.engine;
            checkers.push(admitted.checker);
        }
        Ok(Outcome::Complete((engine, checkers)))
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

    /// Parse, elaborate and dual-check one source definition or theorem without
    /// attempting to compile or execute a proof. Publication remains the same
    /// immutable K1-plus-independent-checker transition as `admit_declaration`.
    /// Kernel nonanswers during elaboration use the same `Outcome` arms as
    /// admission; semantic frontend errors remain in the `Err` channel.
    pub fn admit_source_declaration(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationAdmission>, EngineExecutionError> {
        let parsed = fln_parse::parse_definition(source)
            .map_err(DefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        let declaration = match source_records::elaboration_outcome(
            fln_elab::elaborate_definition_in_with_budget(
                parsed.syntax(),
                self.environment(),
                limits.kernel,
            ),
        )? {
            Outcome::Complete(declaration) => declaration,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let registration = fln_elab::source::instance_registration(parsed.syntax())
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        let simp = fln_elab::source::scope::simp::registration(parsed.syntax())
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        let protected = fln_elab::source::protected_registration(parsed.syntax())
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?
            .map(|name| fln_elab::source::scope::SourceScope::default().declaration_name(&name))
            .transpose()
            .map_err(|error| {
                EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                    fln_elab::NatDefinitionElabError::Inference(
                        fln_elab::source::SourceInferenceError::NameScope(error),
                    ),
                ))
            })?;
        let result = self
            .admit_declaration(declaration, options, limits)
            .map_err(EngineExecutionError::from)?;
        Ok(match result {
            Outcome::Complete(mut admitted) => {
                if let Some((name, priority)) = registration {
                    admitted.engine.environment = fln_elab::instances::register_instance(
                        admitted.engine.environment(),
                        &name,
                        priority,
                    )
                    .map_err(|error| {
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::InstanceRegistry(error),
                            ),
                        ))
                    })?;
                    admitted.result_logical_root = admitted.engine.logical_root(options);
                }
                if let Some((name, priority, reverse)) = simp {
                    let name = fln_elab::source::scope::SourceScope::default()
                        .declaration_name(&name)
                        .map_err(|error| {
                            EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                                fln_elab::NatDefinitionElabError::Inference(
                                    fln_elab::source::SourceInferenceError::NameScope(error),
                                ),
                            ))
                        })?;
                    admitted.engine.environment = fln_elab::source::scope::simp::update(
                        admitted.engine.environment(),
                        &name,
                        Some((priority, reverse)),
                    )
                    .map_err(|error| {
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::SimpSet(error),
                            ),
                        ))
                    })?;
                    admitted.result_logical_root = admitted.engine.logical_root(options);
                }
                if let Some(name) = protected {
                    admitted.engine.environment =
                        source_records::tag_protected(&admitted.engine, &name)?;
                    admitted.result_logical_root = admitted.engine.logical_root(options);
                }
                Outcome::Complete(admitted)
            }
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        })
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
        let declaration = match source_records::elaboration_outcome(
            fln_elab::elaborate_nat_definition_in(parsed.syntax(), self.environment()),
        )? {
            Outcome::Complete(declaration) => declaration,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
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

    /// Elaborate and dual-check one standalone bounded `#check` command.
    ///
    /// The inferred type is validated by admitting an unspellable generated
    /// definition into a scratch successor through K1 and the independent
    /// checker. The successor is discarded before this method returns: the
    /// queried engine remains unchanged, and neither compiler ingress nor Golem
    /// executes the term.
    pub fn check_source_command(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<SourceCheck>, EngineExecutionError> {
        let parsed = fln_parse::parse_source_command(source)
            .map_err(DefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        if parsed.kind() != fln_parse::SourceCommandKind::Check {
            return Err(EngineExecutionError::StandaloneCheckRequired);
        }
        self.check_parsed_source_command(parsed, options, limits, 0)
    }

    fn check_parsed_source_command(
        &self,
        parsed: ParsedSourceCommand,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        command_index: usize,
    ) -> Result<Outcome<SourceCheck>, EngineExecutionError> {
        self.check_parsed_source_command_in_scope(
            parsed,
            options,
            limits,
            command_index,
            &fln_elab::source::scope::SourceScope::default(),
        )
    }

    fn check_parsed_source_command_in_scope(
        &self,
        parsed: ParsedSourceCommand,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        command_index: usize,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<SourceCheck>, EngineExecutionError> {
        let name = fresh_generated_command_name(self.environment(), command_index)?;
        let declaration = source_records::elaboration_outcome(match parsed.kind() {
            SourceCommandKind::Example => fln_elab::source::scope::elaborate_example(
                parsed.syntax(),
                name,
                self.environment(),
                limits.kernel,
                scope,
            ),
            SourceCommandKind::Check => fln_elab::elaborate_check_in_with_budget(
                parsed.syntax(),
                name,
                self.environment(),
                limits.kernel,
            ),
            _ => return Err(EngineExecutionError::StandaloneCheckRequired),
        })?;
        let declaration = match declaration {
            Outcome::Complete(declaration) => declaration,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let checked_type = match &declaration {
            Declaration::Defn(definition) => definition.base.type_.clone(),
            _ => {
                return Err(EngineExecutionError::UnexpectedPublication {
                    detail: "source check elaboration returned a non-definition candidate",
                });
            }
        };
        Ok(
            match self.admit_declaration(declaration, options, limits)? {
                Outcome::Complete(admission) => Outcome::Complete(SourceCheck {
                    parsed,
                    declaration: admission.declaration,
                    checked_type,
                    environment_root: admission.base_logical_root,
                    checker: admission.checker,
                }),
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        )
    }

    /// Execute one import-free source command stream containing definitions,
    /// evaluations, and scratch-only `#check` queries in source order.
    ///
    /// Executable definitions and evaluations use the ordinary dual-check,
    /// publication, compiler, codec, and Golem path. Parametric definitions are
    /// admitted as templates for concrete call-site specialization; instance
    /// commands use the source registry and neither fabricates a VM result. Each query observes the exact immutable
    /// successor produced by the preceding executable commands, but its
    /// generated candidate is admitted only into a discarded scratch successor.
    /// A later frontend/admission/compiler refusal or non-answer returns no
    /// result, so callers cannot expose a partial output stream or retain a
    /// partially advanced engine. Completed non-returning VM exits remain
    /// explicit in the execution batch; a presentation must inspect all of them
    /// before exposing its buffered output. A parsed empty stream completes with
    /// an identity engine/root transition and no output rows.
    pub fn execute_source_commands_with_checks(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<SourceCommandBatchExecution>, EngineExecutionError> {
        let partitioned = fln_parse::partition_source_module(source)
            .map_err(DefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        if !partitioned.imports.is_empty() {
            return Err(EngineExecutionError::ImportsRequireResolver {
                imports: partitioned.imports,
            });
        }
        if partitioned.commands.is_empty() {
            return Ok(Outcome::Complete(
                self.empty_source_command_execution(options),
            ));
        }
        self.execute_source_command_stream(partitioned.commands, options, limits, true)
    }

    fn empty_source_command_execution(&self, options: &KVMap) -> SourceCommandBatchExecution {
        let root = self.logical_root(options);
        SourceCommandBatchExecution {
            batch: DefinitionBatchExecution {
                engine: self.clone(),
                base_logical_root: root,
                result_logical_root: root,
                executions: Vec::new(),
                source_module_order: Vec::new(),
                source_evaluation_indices: Vec::new(),
                source_admissions: Vec::new(),
                source_execution_command_indices: Vec::new(),
            },
            command_count: 0,
            execution_command_indices: Vec::new(),
            outputs: Vec::new(),
            checks: Vec::new(),
        }
    }

    fn execute_source_command_stream(
        &self,
        commands: Vec<(fln_parse::BytePos, &[u8])>,
        options: &KVMap,
        limits: EngineExecutionLimits,
        allow_checks: bool,
    ) -> Result<Outcome<SourceCommandBatchExecution>, EngineExecutionError> {
        if commands.is_empty() {
            return Err(EngineExecutionError::EmptyBatch);
        }

        let command_count = commands.len();
        let mut executions = Vec::new();
        executions.try_reserve_exact(command_count).map_err(|_| {
            EngineExecutionError::AllocationFailure {
                resource: "source command execution results",
                requested: command_count,
            }
        })?;
        let mut execution_command_indices = Vec::new();
        execution_command_indices
            .try_reserve_exact(command_count)
            .map_err(|_| EngineExecutionError::AllocationFailure {
                resource: "source command execution index table",
                requested: command_count,
            })?;
        let mut outputs = Vec::new();
        outputs.try_reserve_exact(command_count).map_err(|_| {
            EngineExecutionError::AllocationFailure {
                resource: "source command output table",
                requested: command_count,
            }
        })?;
        let mut checks = Vec::new();
        checks.try_reserve_exact(command_count).map_err(|_| {
            EngineExecutionError::AllocationFailure {
                resource: "source command check table",
                requested: command_count,
            }
        })?;
        let mut evaluation_indices = Vec::new();
        evaluation_indices
            .try_reserve_exact(command_count)
            .map_err(|_| EngineExecutionError::AllocationFailure {
                resource: "source evaluation command index table",
                requested: command_count,
            })?;

        let mut source_admissions = Vec::new();
        source_admissions
            .try_reserve_exact(command_count)
            .map_err(|_| EngineExecutionError::AllocationFailure {
                resource: "source admission table",
                requested: command_count,
            })?;
        let base_logical_root = self.logical_root(options);
        let mut engine = self.clone();
        for (command_index, (original_offset, command_source)) in commands.into_iter().enumerate() {
            if fln_parse::command_scope::mutual::parse(command_source)
                .map_err(|error| error.with_original_offset(original_offset))
                .map_err(DefinitionFrontendError::Parse)
                .map_err(|error| EngineExecutionError::BatchCommand {
                    index: command_index,
                    error: Box::new(EngineExecutionError::Frontend(error)),
                    at: Some(original_offset),
                })?
                .is_some()
            {
                // Keep the whole mutual block on the existing two-checker
                // admission path. Never publish members sequentially or treat
                // declarations as VM executions merely to advance the stream.
                let admission = match engine
                    .admit_source_command(command_source, options, limits.admission())
                    .map_err(|error| EngineExecutionError::BatchCommand {
                        index: command_index,
                        error: Box::new(error),
                        at: Some(original_offset),
                    })? {
                    Outcome::Complete(admission) => admission,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                engine = admission.engine.clone();
                source_admissions.push(SourceCommandAdmission {
                    command_index,
                    admission,
                });
                continue;
            }
            let parsed = fln_parse::parse_source_command(command_source)
                .map_err(|error| error.with_original_offset(original_offset))
                .map_err(DefinitionFrontendError::Parse)
                .map_err(|error| EngineExecutionError::BatchCommand {
                    index: command_index,
                    error: Box::new(EngineExecutionError::Frontend(error)),
                    at: Some(original_offset),
                })?;
            if matches!(
                parsed.kind(),
                SourceCommandKind::Check | SourceCommandKind::Example
            ) {
                let is_example = parsed.kind() == SourceCommandKind::Example;
                if !allow_checks && !is_example {
                    return Err(EngineExecutionError::BatchCommand {
                        index: command_index,
                        error: Box::new(EngineExecutionError::StandaloneCheckRequired),
                        at: Some(original_offset),
                    });
                }
                let checked = match engine.check_parsed_source_command(
                    parsed,
                    options,
                    limits.admission(),
                    command_index,
                ) {
                    Ok(Outcome::Complete(checked)) => checked,
                    Ok(Outcome::Inconclusive(reason)) => {
                        return Ok(Outcome::Inconclusive(reason));
                    }
                    Ok(Outcome::InternalFault(fault)) => {
                        return Ok(Outcome::InternalFault(fault));
                    }
                    Err(error) => {
                        return Err(EngineExecutionError::BatchCommand {
                            index: command_index,
                            error: Box::new(error),
                            at: Some(original_offset),
                        });
                    }
                };
                let check_index = checks.len();
                checks.push(checked);
                outputs.push(if is_example {
                    SourceCommandOutput::Example {
                        command_index,
                        check_index,
                    }
                } else {
                    SourceCommandOutput::Check {
                        command_index,
                        check_index,
                    }
                });
                continue;
            }

            let is_instance = parsed.kind() == fln_parse::SourceCommandKind::Definition
                && fln_elab::source::instance_registration(parsed.syntax())
                    .map_err(DefinitionFrontendError::Elaborate)
                    .map_err(EngineExecutionError::Frontend)
                    .map_err(|error| EngineExecutionError::BatchCommand {
                        index: command_index,
                        error: Box::new(error),
                        at: Some(original_offset),
                    })?
                    .is_some();
            if fln_elab::source::is_record(parsed.syntax())
                || fln_elab::source::is_inductive(parsed.syntax())
                || is_instance
            {
                let admission = match engine
                    .admit_source_command(command_source, options, limits.admission())
                    .map_err(|error| EngineExecutionError::BatchCommand {
                        index: command_index,
                        error: Box::new(error),
                        at: Some(original_offset),
                    })? {
                    Outcome::Complete(admission) => admission,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                engine = admission.engine.clone();
                source_admissions.push(SourceCommandAdmission {
                    command_index,
                    admission,
                });
                continue;
            }

            let is_evaluation = parsed.kind() == fln_parse::SourceCommandKind::Evaluation;
            let declaration = source_records::elaboration_outcome(match parsed.kind() {
                fln_parse::SourceCommandKind::Evaluation => {
                    let name = fresh_generated_command_name(engine.environment(), command_index)
                        .map_err(|error| EngineExecutionError::BatchCommand {
                            index: command_index,
                            error: Box::new(error),
                            at: Some(original_offset),
                        })?;
                    fln_elab::elaborate_evaluation_in_with_budget(
                        parsed.syntax(),
                        name,
                        engine.environment(),
                        limits.kernel,
                    )
                }
                fln_parse::SourceCommandKind::Definition => {
                    fln_elab::elaborate_definition_in_with_budget(
                        parsed.syntax(),
                        engine.environment(),
                        limits.kernel,
                    )
                }
                fln_parse::SourceCommandKind::Check | fln_parse::SourceCommandKind::Example => {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "source check escaped its scratch-only command branch",
                    });
                }
            })
            .map_err(|error| EngineExecutionError::BatchCommand {
                index: command_index,
                error: Box::new(error),
                at: Some(original_offset),
            })?;
            let declaration = match declaration {
                Outcome::Complete(declaration) => declaration,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            // Parametric definitions are checked templates, not standalone VM
            // entry points. Compile concrete uses on demand; never use a failed
            // compilation as a reason to silently admit an executable command.
            let is_template = !is_evaluation
                && matches!(&declaration,
                Declaration::Defn(definition) if runtime::is_template(definition));
            if matches!(declaration, Declaration::Thm(_)) || is_template {
                let admission = match engine
                    .admit_declarations(&[declaration], options, limits.admission())
                    .map_err(|error| EngineExecutionError::BatchCommand {
                        index: command_index,
                        error: Box::new(error.into()),
                        at: Some(original_offset),
                    })? {
                    Outcome::Complete(admission) => admission,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                engine = admission.engine.clone();
                source_admissions.push(SourceCommandAdmission {
                    command_index,
                    admission,
                });
                continue;
            }
            let execution = match engine.execute_definition(declaration, options, limits) {
                Ok(Outcome::Complete(execution)) => execution,
                Ok(Outcome::Inconclusive(reason)) => return Ok(Outcome::Inconclusive(reason)),
                Ok(Outcome::InternalFault(fault)) => {
                    return Ok(Outcome::InternalFault(fault));
                }
                Err(error) => {
                    return Err(EngineExecutionError::BatchCommand {
                        index: command_index,
                        error: Box::new(error),
                        at: Some(original_offset),
                    });
                }
            };
            let execution_index = executions.len();
            engine = execution.engine.clone();
            executions.push(execution);
            execution_command_indices.push(command_index);
            if is_evaluation {
                evaluation_indices.push(execution_index);
                outputs.push(SourceCommandOutput::Evaluation {
                    command_index,
                    execution_index,
                });
            }
        }

        let mut execution_indices = Vec::new();
        execution_indices
            .try_reserve_exact(execution_command_indices.len())
            .map_err(|_| EngineExecutionError::AllocationFailure {
                resource: "retained source execution index table",
                requested: execution_command_indices.len(),
            })?;
        execution_indices.extend_from_slice(&execution_command_indices);
        let result_logical_root = engine.logical_root(options);
        Ok(Outcome::Complete(SourceCommandBatchExecution {
            batch: DefinitionBatchExecution {
                engine,
                base_logical_root,
                result_logical_root,
                executions,
                source_module_order: Vec::new(),
                source_evaluation_indices: evaluation_indices,
                source_admissions,
                source_execution_command_indices: execution_indices,
            },
            command_count,
            execution_command_indices,
            outputs,
            checks,
        }))
    }

    /// Execute a definition-only prefix, then dual-check one terminal `#check`.
    ///
    /// The prefix uses the ordinary checked definition pipeline and is retained
    /// only when the terminal query also completes. The query observes that
    /// successor but its generated declaration is admitted only in a discarded
    /// scratch successor. Imports, evaluations, and earlier checks remain
    /// outside this bounded command shape.
    pub fn check_terminal_source_command(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<TerminalSourceCheck>, EngineExecutionError> {
        let mut commands = fln_parse::partition_definition_commands(source)
            .map_err(DefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        let terminal_index =
            commands
                .len()
                .checked_sub(1)
                .ok_or(EngineExecutionError::UnexpectedPublication {
                    detail: "source command partition returned an empty command table",
                })?;
        let (terminal_offset, terminal_source) =
            commands
                .pop()
                .ok_or(EngineExecutionError::UnexpectedPublication {
                    detail: "source command partition lost its terminal command",
                })?;
        let terminal = fln_parse::parse_source_command(terminal_source)
            .map_err(|error| error.with_original_offset(terminal_offset))
            .map_err(DefinitionFrontendError::Parse)
            .map_err(|error| EngineExecutionError::BatchCommand {
                index: terminal_index,
                error: Box::new(EngineExecutionError::Frontend(error)),
                at: Some(terminal_offset),
            })?;
        if terminal.kind() != fln_parse::SourceCommandKind::Check {
            return Err(EngineExecutionError::TerminalCheckRequired);
        }
        for (index, (original_offset, command_source)) in commands.iter().enumerate() {
            let parsed = fln_parse::parse_source_command(command_source)
                .map_err(|error| error.with_original_offset(*original_offset))
                .map_err(DefinitionFrontendError::Parse)
                .map_err(|error| EngineExecutionError::BatchCommand {
                    index,
                    error: Box::new(EngineExecutionError::Frontend(error)),
                    at: Some(*original_offset),
                })?;
            if !matches!(
                parsed.kind(),
                SourceCommandKind::Definition | SourceCommandKind::Example
            ) {
                return Err(EngineExecutionError::TerminalCheckDefinitionPrefix { index });
            }
        }

        let definition_prefix = if commands.is_empty() {
            None
        } else {
            match self.execute_source_commands(commands, options, limits)? {
                Outcome::Complete(completed) => Some(completed),
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
        };
        let query_engine = definition_prefix
            .as_ref()
            .map_or(self, |completed| &completed.engine);
        let checked = query_engine
            .check_source_command(terminal_source, options, limits.admission())
            .map_err(|error| EngineExecutionError::BatchCommand {
                index: terminal_index,
                error: Box::new(error),
                at: Some(terminal_offset),
            })?;
        Ok(match checked {
            Outcome::Complete(check) => Outcome::Complete(TerminalSourceCheck {
                definition_prefix,
                source_module_order: Vec::new(),
                check,
            }),
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        })
    }

    /// Execute a closed definition-only module graph, then check the entry's
    /// terminal query against its exact completed environment.
    ///
    /// Every nonterminal command in every module must be a definition. The
    /// entry may contain no definition of its own: imported definitions still
    /// form the query environment. Graph planning, dependency visibility, and
    /// definition execution use the ordinary closed-module path. The terminal
    /// query itself is admitted only in a discarded scratch successor.
    pub fn check_terminal_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<TerminalSourceCheck>, EngineExecutionError> {
        if modules.is_empty() {
            return Err(EngineExecutionError::EmptyBatch);
        }
        if modules.len() > limits.source_modules.max_modules {
            return Err(EngineExecutionError::SourceModuleLimit {
                observed: modules.len(),
                limit: limits.source_modules.max_modules,
            });
        }
        let entry_matches = modules.iter().filter(|module| module.name == entry).count();
        match entry_matches {
            0 => {
                return Err(EngineExecutionError::MissingSourceEntry {
                    module: entry.clone(),
                });
            }
            1 => {}
            _ => {
                return Err(EngineExecutionError::DuplicateSourceModule {
                    module: entry.clone(),
                });
            }
        }

        let mut query_source = None;
        let mut rewritten = Vec::new();
        rewritten.try_reserve_exact(modules.len()).map_err(|_| {
            EngineExecutionError::AllocationFailure {
                resource: "terminal-check source module table",
                requested: modules.len(),
            }
        })?;
        for module in modules {
            let partitioned = fln_parse::partition_source_module(module.source)
                .map_err(DefinitionFrontendError::Parse)
                .map_err(EngineExecutionError::Frontend)?;
            let prefix_len = if module.name == entry {
                let terminal_index = partitioned
                    .commands
                    .len()
                    .checked_sub(1)
                    .ok_or(EngineExecutionError::TerminalCheckRequired)?;
                let (terminal_offset, terminal_source) =
                    partitioned.commands.last().copied().ok_or(
                        EngineExecutionError::UnexpectedPublication {
                            detail: "terminal source command disappeared after indexing",
                        },
                    )?;
                let terminal = fln_parse::parse_source_command(terminal_source)
                    .map_err(|error| error.with_original_offset(terminal_offset))
                    .map_err(DefinitionFrontendError::Parse)
                    .map_err(|error| EngineExecutionError::BatchCommand {
                        index: terminal_index,
                        error: Box::new(EngineExecutionError::Frontend(error)),
                        at: Some(terminal_offset),
                    })?;
                if terminal.kind() != fln_parse::SourceCommandKind::Check {
                    return Err(EngineExecutionError::TerminalCheckRequired);
                }
                query_source = Some(terminal_source);
                terminal_index
            } else {
                partitioned.commands.len()
            };
            for (index, (original_offset, command_source)) in
                partitioned.commands.iter().take(prefix_len).enumerate()
            {
                let parsed = fln_parse::parse_source_command(command_source)
                    .map_err(|error| error.with_original_offset(*original_offset))
                    .map_err(DefinitionFrontendError::Parse)
                    .map_err(|error| EngineExecutionError::BatchCommand {
                        index,
                        error: Box::new(EngineExecutionError::Frontend(error)),
                        at: Some(*original_offset),
                    })?;
                if !matches!(
                    parsed.kind(),
                    SourceCommandKind::Definition | SourceCommandKind::Example
                ) {
                    return Err(EngineExecutionError::TerminalCheckModuleDefinitionPrefix {
                        module: module.name.clone(),
                        index,
                    });
                }
            }
            let source = if module.name == entry {
                let (terminal_offset, _) = partitioned.commands.get(prefix_len).copied().ok_or(
                    EngineExecutionError::UnexpectedPublication {
                        detail: "terminal source command disappeared after preflight",
                    },
                )?;
                module.source.get(..terminal_offset.0).ok_or(
                    EngineExecutionError::UnexpectedPublication {
                        detail: "terminal source command offset escaped its module bytes",
                    },
                )?
            } else {
                module.source
            };
            rewritten.push(SourceModuleInput {
                name: module.name,
                source,
            });
        }
        let query_source = query_source.ok_or(EngineExecutionError::TerminalCheckRequired)?;
        let completed = match self.execute_source_modules_internal(
            &rewritten,
            entry,
            options,
            limits,
            SourceModuleCommandPolicy::DefinitionPrefix,
        )? {
            Outcome::Complete(completed) => completed.batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let query_index = completed.executions.len() + completed.source_admissions.len();
        let checked = completed
            .engine
            .check_source_command(query_source, options, limits.admission())
            .map_err(|error| EngineExecutionError::BatchCommand {
                index: query_index,
                error: Box::new(error),
                at: None,
            })?;
        Ok(match checked {
            Outcome::Complete(check) => {
                let mut completed = completed;
                let source_module_order = std::mem::take(&mut completed.source_module_order);
                let definition_prefix =
                    if completed.executions.is_empty() && completed.source_admissions.is_empty() {
                        None
                    } else {
                        Some(completed)
                    };
                Outcome::Complete(TerminalSourceCheck {
                    definition_prefix,
                    source_module_order,
                    check,
                })
            }
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        })
    }

    /// Execute a closed local source-module graph with a mixed command stream
    /// in the selected entry module.
    ///
    /// Every dependency module executes definitions and evaluations silently in
    /// the ordinary deterministic dependency order. Dependency `#check` queries
    /// are likewise silent and scratch-only: each candidate is dual-checked,
    /// attributed to its source module, and included in the same transitive
    /// visibility proof as published declarations before its scratch successor
    /// is discarded. The entry then runs definitions, evaluations, and checks in
    /// source order against the exact completed dependency environment.
    /// Dependency execution and entry output are retained separately so a
    /// presentation can reject any non-returning VM exit before exposing the
    /// entry's buffered output. An import-only entry completes as an empty entry
    /// stream after the dependency closure; no dependency result is promoted to
    /// entry output.
    pub fn execute_source_modules_with_entry_checks(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<SourceModuleCommandBatchExecution>, EngineExecutionError> {
        if modules.is_empty() {
            return Err(EngineExecutionError::EmptyBatch);
        }
        if modules.len() > limits.source_modules.max_modules {
            return Err(EngineExecutionError::SourceModuleLimit {
                observed: modules.len(),
                limit: limits.source_modules.max_modules,
            });
        }
        let entry_matches = modules.iter().filter(|module| module.name == entry).count();
        match entry_matches {
            0 => {
                return Err(EngineExecutionError::MissingSourceEntry {
                    module: entry.clone(),
                });
            }
            1 => {}
            _ => {
                return Err(EngineExecutionError::DuplicateSourceModule {
                    module: entry.clone(),
                });
            }
        }

        let mut entry_commands = None;
        let mut rewritten = Vec::new();
        rewritten.try_reserve_exact(modules.len()).map_err(|_| {
            EngineExecutionError::AllocationFailure {
                resource: "mixed-entry source module table",
                requested: modules.len(),
            }
        })?;
        for module in modules {
            let partitioned = fln_parse::partition_source_module(module.source)
                .map_err(DefinitionFrontendError::Parse)
                .map_err(EngineExecutionError::Frontend)?;
            let source = if module.name == entry {
                let first_offset = partitioned.commands.first().map(|(offset, _)| *offset);
                entry_commands = Some(partitioned.commands);
                match first_offset {
                    Some(first_offset) => module.source.get(..first_offset.0).ok_or(
                        EngineExecutionError::UnexpectedPublication {
                            detail: "entry source command offset escaped its module bytes",
                        },
                    )?,
                    None => module.source,
                }
            } else {
                module.source
            };
            rewritten.push(SourceModuleInput {
                name: module.name,
                source,
            });
        }
        let entry_commands =
            entry_commands.ok_or_else(|| EngineExecutionError::MissingSourceEntry {
                module: entry.clone(),
            })?;
        let dependency_plan = match self.execute_source_modules_internal(
            &rewritten,
            entry,
            options,
            limits,
            SourceModuleCommandPolicy::MixedPrefix,
        )? {
            Outcome::Complete(completed) => completed,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let dependency_command_count = dependency_plan.command_count;
        let dependency_execution_command_indices = dependency_plan
            .execution_command_indices
            .ok_or(EngineExecutionError::UnexpectedPublication {
                detail: "mixed dependency execution omitted its source command index table",
            })?;
        let mut dependency_prefix = dependency_plan.batch;
        let entry_execution = if entry_commands.is_empty() {
            dependency_prefix
                .engine
                .empty_source_command_execution(options)
        } else {
            match dependency_prefix.engine.execute_source_command_stream(
                entry_commands,
                options,
                limits,
                true,
            )? {
                Outcome::Complete(completed) => completed,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
        };
        let source_module_order = std::mem::take(&mut dependency_prefix.source_module_order);
        let dependency_prefix = if dependency_prefix.executions.is_empty()
            && dependency_prefix.source_admissions.is_empty()
        {
            None
        } else {
            Some(dependency_prefix)
        };
        Ok(Outcome::Complete(SourceModuleCommandBatchExecution {
            dependency_prefix,
            dependency_command_count,
            dependency_execution_command_indices,
            source_module_order,
            entry: entry_execution,
        }))
    }

    fn execute_parsed_source_definition(
        &self,
        parsed: fln_parse::ParsedDefinition,
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionExecution>, EngineExecutionError> {
        if fln_elab::source::scope::simp::registration(parsed.syntax())
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?
            .is_some()
        {
            return Err(EngineExecutionError::Frontend(
                DefinitionFrontendError::Elaborate(
                    fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                        expected: "an executable definition; use check-source for simp attributes",
                    },
                ),
            ));
        }
        if fln_elab::source::instance_registration(parsed.syntax())
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?
            .is_some()
        {
            return Err(EngineExecutionError::Frontend(
                DefinitionFrontendError::Elaborate(
                    fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                        expected: "an executable definition; use check-source for instance declarations",
                    },
                ),
            ));
        }
        let declaration = match source_records::elaboration_outcome(
            fln_elab::elaborate_definition_in_with_budget(
                parsed.syntax(),
                self.environment(),
                limits.kernel,
            ),
        )? {
            Outcome::Complete(declaration) => declaration,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
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
                        at: None,
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
            let partitioned = fln_parse::partition_source_module(source).map_err(|error| {
                EngineExecutionError::BatchCommand {
                    index: commands.len(),
                    error: Box::new(EngineExecutionError::Frontend(
                        DefinitionFrontendError::Parse(error),
                    )),
                    at: None,
                }
            })?;
            if !partitioned.imports.is_empty() {
                return Err(EngineExecutionError::ImportsRequireResolver {
                    imports: partitioned.imports,
                });
            }
            let requested = commands
                .len()
                .checked_add(partitioned.commands.len())
                .ok_or(EngineExecutionError::AllocationFailure {
                    resource: "definition command table",
                    requested: usize::MAX,
                })?;
            commands
                .try_reserve(partitioned.commands.len())
                .map_err(|_| EngineExecutionError::AllocationFailure {
                    resource: "definition command table",
                    requested,
                })?;
            commands.extend(partitioned.commands);
        }
        self.execute_source_commands(commands, options, limits)
    }

    /// Execute an exact, caller-named closed source-module import graph.
    ///
    /// Every direct import must name another supplied module. The entry must
    /// reach every row, so an unused file cannot silently influence which final
    /// definition is reported. Modules are dependency-sorted with structural
    /// [`Name`] order as the CGSE tie-break; definitions retain source order
    /// within a module. A completed declaration may reference definitions from
    /// only its own module or a transitive import; scheduling order grants no
    /// visibility. Graph refusal, frontend refusal, admission non-answer, or
    /// execution failure exposes no successor engine.
    pub fn execute_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionBatchExecution>, EngineExecutionError> {
        Ok(self
            .execute_source_modules_internal(
                modules,
                entry,
                options,
                limits,
                SourceModuleCommandPolicy::ExecutableOnly,
            )?
            .map_complete(|completed| completed.batch))
    }

    fn execute_source_modules_internal(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: EngineExecutionLimits,
        policy: SourceModuleCommandPolicy,
    ) -> Result<Outcome<PlannedSourceModuleExecution>, EngineExecutionError> {
        if modules.is_empty() {
            return Err(EngineExecutionError::EmptyBatch);
        }
        if modules.len() > limits.source_modules.max_modules {
            return Err(EngineExecutionError::SourceModuleLimit {
                observed: modules.len(),
                limit: limits.source_modules.max_modules,
            });
        }

        let mut owners = BTreeMap::new();
        for (index, module) in modules.iter().enumerate() {
            bounded_source_module_name_depth(module.name, limits.source_modules.max_name_depth)?;
            if owners.insert(module.name.clone(), index).is_some() {
                return Err(EngineExecutionError::DuplicateSourceModule {
                    module: module.name.clone(),
                });
            }
        }
        let Some(&entry_index) = owners.get(entry) else {
            return Err(EngineExecutionError::MissingSourceEntry {
                module: entry.clone(),
            });
        };

        let mut parsed = Vec::new();
        parsed.try_reserve_exact(modules.len()).map_err(|_| {
            EngineExecutionError::AllocationFailure {
                resource: "parsed source module table",
                requested: modules.len(),
            }
        })?;
        let mut import_presentations = 0_usize;
        for module in modules {
            let partitioned =
                fln_parse::partition_source_module(module.source).map_err(|error| {
                    EngineExecutionError::Frontend(DefinitionFrontendError::Parse(error))
                })?;
            for import in &partitioned.imports {
                bounded_source_module_name_depth(import, limits.source_modules.max_name_depth)?;
            }
            import_presentations = import_presentations
                .checked_add(partitioned.imports.len())
                .ok_or(EngineExecutionError::SourceImportLimit {
                    observed: usize::MAX,
                    limit: limits.source_modules.max_imports,
                })?;
            if import_presentations > limits.source_modules.max_imports {
                return Err(EngineExecutionError::SourceImportLimit {
                    observed: import_presentations,
                    limit: limits.source_modules.max_imports,
                });
            }
            parsed.push(partitioned);
        }
        let mut dependencies = vec![Vec::new(); modules.len()];
        let mut remaining = vec![0_usize; modules.len()];
        let mut dependents = vec![Vec::new(); modules.len()];
        for (index, module) in parsed.iter().enumerate() {
            let mut unique = BTreeSet::new();
            let mut missing = BTreeSet::new();
            for import in &module.imports {
                match owners.get(import).copied() {
                    Some(owner) => {
                        unique.insert(owner);
                    }
                    None => {
                        missing.insert(import.clone());
                    }
                }
            }
            if !missing.is_empty() {
                return Err(EngineExecutionError::MissingSourceImports {
                    module: modules[index].name.clone(),
                    imports: missing.into_iter().collect(),
                });
            }
            dependencies[index]
                .try_reserve_exact(unique.len())
                .map_err(|_| EngineExecutionError::AllocationFailure {
                    resource: "source module dependency table",
                    requested: unique.len(),
                })?;
            dependencies[index].extend(unique.iter().copied());
            remaining[index] = unique.len();
            for dependency in unique {
                dependents[dependency].push(index);
            }
        }

        let mut reachable = vec![false; modules.len()];
        let mut pending = vec![entry_index];
        while let Some(index) = pending.pop() {
            if reachable[index] {
                continue;
            }
            reachable[index] = true;
            pending.extend(dependencies[index].iter().copied());
        }
        let unreachable = modules
            .iter()
            .enumerate()
            .filter(|(index, _)| !reachable[*index])
            .map(|(_, module)| module.name.clone())
            .collect::<Vec<_>>();
        if !unreachable.is_empty() {
            return Err(EngineExecutionError::UnreachableSourceModules {
                entry: entry.clone(),
                modules: unreachable,
            });
        }

        let mut ready = modules
            .iter()
            .enumerate()
            .filter(|(index, _)| remaining[*index] == 0)
            .map(|(index, module)| (module.name.clone(), index))
            .collect::<BTreeSet<_>>();
        let mut order = Vec::new();
        order.try_reserve_exact(modules.len()).map_err(|_| {
            EngineExecutionError::AllocationFailure {
                resource: "source module order",
                requested: modules.len(),
            }
        })?;
        while let Some((_, index)) = ready.pop_first() {
            order.push(index);
            for dependent in &dependents[index] {
                remaining[*dependent] = remaining[*dependent].checked_sub(1).ok_or(
                    EngineExecutionError::UnexpectedPublication {
                        detail: "source module dependency count underflowed",
                    },
                )?;
                if remaining[*dependent] == 0 {
                    ready.insert((modules[*dependent].name.clone(), *dependent));
                }
            }
        }
        if order.len() != modules.len() {
            return Err(EngineExecutionError::SourceModuleCycle {
                modules: modules
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| remaining[*index] != 0)
                    .map(|(_, module)| module.name.clone())
                    .collect(),
            });
        }
        if policy.require_entry_command() && parsed[entry_index].commands.is_empty() {
            return Err(EngineExecutionError::EmptySourceEntry {
                module: entry.clone(),
            });
        }

        let module_order = order
            .iter()
            .map(|index| modules[*index].name.clone())
            .collect::<Vec<_>>();
        let command_count = order.iter().try_fold(0_usize, |total, index| {
            total.checked_add(parsed[*index].commands.len())
        });
        let Some(command_count) = command_count else {
            return Err(EngineExecutionError::AllocationFailure {
                resource: "definition command table",
                requested: usize::MAX,
            });
        };
        let mut commands = Vec::new();
        commands.try_reserve_exact(command_count).map_err(|_| {
            EngineExecutionError::AllocationFailure {
                resource: "definition command table",
                requested: command_count,
            }
        })?;
        let mut command_owners = Vec::new();
        command_owners
            .try_reserve_exact(command_count)
            .map_err(|_| EngineExecutionError::AllocationFailure {
                resource: "source command ownership table",
                requested: command_count,
            })?;
        for &index in &order {
            commands.extend(parsed[index].commands.iter().copied());
            command_owners.extend(std::iter::repeat_n(index, parsed[index].commands.len()));
        }
        if policy.allow_empty_batch() && commands.is_empty() {
            let root = self.logical_root(options);
            return Ok(Outcome::Complete(PlannedSourceModuleExecution {
                batch: DefinitionBatchExecution {
                    engine: self.clone(),
                    base_logical_root: root,
                    result_logical_root: root,
                    executions: Vec::new(),
                    source_module_order: module_order,
                    source_evaluation_indices: Vec::new(),
                    source_admissions: Vec::new(),
                    source_execution_command_indices: Vec::new(),
                },
                command_count,
                execution_command_indices: policy.allow_scratch_checks().then(Vec::new),
            }));
        }
        {
            let mixed = match self.execute_source_command_stream(
                commands,
                options,
                limits,
                policy.allow_scratch_checks(),
            )? {
                Outcome::Complete(completed) => completed,
                Outcome::Inconclusive(inconclusive) => {
                    return Ok(Outcome::Inconclusive(inconclusive));
                }
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            let mut execution_owners = Vec::new();
            execution_owners
                .try_reserve_exact(mixed.execution_command_indices.len())
                .map_err(|_| EngineExecutionError::AllocationFailure {
                    resource: "source execution ownership table",
                    requested: mixed.execution_command_indices.len(),
                })?;
            for &command_index in &mixed.execution_command_indices {
                let Some(&owner) = command_owners.get(command_index) else {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "source execution index escaped its command ownership table",
                    });
                };
                execution_owners.push(owner);
            }

            let mut check_owners = Vec::new();
            check_owners
                .try_reserve_exact(mixed.checks.len())
                .map_err(|_| EngineExecutionError::AllocationFailure {
                    resource: "source scratch-check ownership table",
                    requested: mixed.checks.len(),
                })?;
            check_owners.resize(mixed.checks.len(), usize::MAX);
            for output in &mixed.outputs {
                let (SourceCommandOutput::Check {
                    command_index,
                    check_index,
                }
                | SourceCommandOutput::Example {
                    command_index,
                    check_index,
                }) = output
                else {
                    continue;
                };
                let Some(&owner) = command_owners.get(*command_index) else {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "source check index escaped its command ownership table",
                    });
                };
                let Some(slot) = check_owners.get_mut(*check_index) else {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "source check output escaped its retained check table",
                    });
                };
                if *slot != usize::MAX {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "source check output repeated a retained check index",
                    });
                }
                *slot = owner;
            }
            if check_owners.contains(&usize::MAX) {
                return Err(EngineExecutionError::UnexpectedPublication {
                    detail: "source check ownership omitted a retained scratch check",
                });
            }
            verify_source_module_visibility(
                modules,
                &dependencies,
                &order,
                SourceModuleVisibilitySubjects {
                    execution_owners: &execution_owners,
                    command_owners: &command_owners,
                    completed: &mixed.batch,
                    check_owners: &check_owners,
                    checks: &mixed.checks,
                },
                limits.source_modules.max_dependency_presentations,
            )?;
            let SourceCommandBatchExecution {
                mut batch,
                command_count,
                execution_command_indices,
                ..
            } = mixed;
            batch.source_module_order = module_order;
            Ok(Outcome::Complete(PlannedSourceModuleExecution {
                batch,
                command_count,
                execution_command_indices: Some(execution_command_indices),
            }))
        }
    }

    fn execute_source_commands(
        &self,
        commands: Vec<(fln_parse::BytePos, &[u8])>,
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionBatchExecution>, EngineExecutionError> {
        Ok(
            match self.execute_source_command_stream(commands, options, limits, false)? {
                Outcome::Complete(completed) => Outcome::Complete(completed.batch),
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        )
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
                        at: None,
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
            source_module_order: Vec::new(),
            source_evaluation_indices: Vec::new(),
            source_admissions: Vec::new(),
            source_execution_command_indices: Vec::new(),
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
        let (expression, declared_type) = match &declaration {
            Declaration::Defn(definition) => {
                (definition.value.clone(), definition.base.type_.clone())
            }
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

        let mut preparation = runtime::Preparation::new(&self.environment, limits.ingress);
        let runtime_type = preparation
            .normalize_type(&declared_type)
            .map_err(EngineExecutionError::Ingress)?;
        let root_result = preparation.root_result(&runtime_type);
        let expression = preparation
            .expression_at_type(&expression, Some(declared_type.clone()))
            .map_err(EngineExecutionError::Ingress)?;
        let mut catalog = executable_dependencies(
            &self.environment,
            &expression,
            limits.ingress,
            &mut preparation,
        )
        .map_err(EngineExecutionError::Ingress)?;
        let local_lambda = executable_lambda(&admission.declaration, &expression, &mut preparation)
            .map_err(EngineExecutionError::Ingress)?;
        if let Some(lambda) = local_lambda {
            preparation.lambdas.push(lambda);
        }
        preparation
            .refine_expression_captures(&expression)
            .map_err(EngineExecutionError::Ingress)?;
        let interfaces = preparation
            .finalize_callables(&mut catalog.functions)
            .map_err(EngineExecutionError::Ingress)?;
        let ingress = fln_comp::ingress::lower_closed_expr_at_result(
            &expression,
            &catalog.scalar_constructors,
            &catalog.intrinsics,
            &preparation.constructors,
            preparation.callables(&catalog.functions),
            &interfaces,
            root_result,
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
            runtime_type,
            base_logical_root: admission.base_logical_root,
            result_logical_root: admission.result_logical_root,
            flbc_artifact,
            exit,
            checker: admission.checker,
        }))
    }
}

/// Execute a validated FLBC program on the Golem VM with the given option map
/// and execution limits. Returns the VM exit outcome — `Returned`, `Panicked`,
/// or `Refused` — wrapped in `Outcome` for the usual
/// `Complete`/`Inconclusive`/`InternalFault` tri-state.
///
/// This is the lowest-level public execution primitive: one program, one run,
/// no source parsing or elaboration. The `execute_flbc_artifact` function wraps
/// decoding, validation, *and* execution in one step; use this function when
/// you already hold a `ValidatedProgram` (e.g., from your own compilation or
/// from a cached validated artifact).
pub fn execute_golem_with_options(
    executable: &ValidatedProgram,
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

/// Write `expression` in the checker's sharing-preserving transport
/// ([`fln_checker::wire::SCHEMA_EXPR_DAG`]): one record per distinct node
/// allocation, children before parents, so a term shared in memory crosses as
/// its DAG rather than its tree. `None` once the encoding would pass `limit`
/// bytes, without ever holding more than that.
fn encode_checker_expr_dag(expression: &Expr, limit: usize) -> Option<Vec<u8>> {
    use fln_checker::wire as tag;
    use fln_core::expr::ExprNode;

    fn children(node: &ExprNode) -> [Option<&Expr>; 3] {
        match node {
            ExprNode::App { f, a } => [Some(f), Some(a), None],
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => [Some(binder_type), Some(body), None],
            ExprNode::LetE {
                type_, value, body, ..
            } => [Some(type_), Some(value), Some(body)],
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => [Some(expr), None, None],
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => [None, None, None],
        }
    }
    // A node's identity is the address of its shared allocation, stable while
    // `expression` is borrowed; structurally equal but separately allocated
    // nodes stay separate records, which costs bytes and never meaning.
    let identity = |term: &Expr| std::ptr::from_ref(term.node()).addr();

    let mut index: std::collections::HashMap<usize, u32> = std::collections::HashMap::new();
    let mut order: Vec<&Expr> = Vec::new();
    let mut pending: Vec<(&Expr, bool)> = vec![(expression, false)];
    while let Some((term, children_done)) = pending.pop() {
        let id = identity(term);
        if index.contains_key(&id) {
            continue;
        }
        if children_done {
            index.insert(id, u32::try_from(order.len()).ok()?);
            order.push(term);
            continue;
        }
        pending.push((term, true));
        for child in children(term.node()).into_iter().rev().flatten() {
            if !index.contains_key(&identity(child)) {
                pending.push((child, false));
            }
        }
    }

    let reference = |term: &Expr| index[&identity(term)];
    let mut w = CanonWriter::with_limit(limit);
    w.schema(tag::SCHEMA_EXPR_DAG);
    w.u64(order.len() as u64);
    for term in order {
        if w.overflowed() {
            return None;
        }
        match term.node() {
            ExprNode::BVar { idx } => {
                w.u8(tag::EXPR_BVAR);
                w.u32(*idx);
            }
            ExprNode::FVar { id } => {
                w.u8(tag::EXPR_FVAR);
                id.0.write_body(&mut w);
            }
            ExprNode::MVar { id } => {
                w.u8(tag::EXPR_MVAR);
                id.0.write_body(&mut w);
            }
            ExprNode::Sort { level } => {
                w.u8(tag::EXPR_SORT);
                level.write_body(&mut w);
            }
            ExprNode::Const { name, levels } => {
                w.u8(tag::EXPR_CONST);
                name.write_body(&mut w);
                w.u64(levels.len() as u64);
                for level in levels {
                    level.write_body(&mut w);
                }
            }
            ExprNode::App { f, a } => {
                w.u8(tag::EXPR_APP);
                w.u32(reference(f));
                w.u32(reference(a));
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            }
            | ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                w.u8(if matches!(term.node(), ExprNode::Lam { .. }) {
                    tag::EXPR_LAM
                } else {
                    tag::EXPR_FORALL
                });
                binder_name.write_body(&mut w);
                w.u32(reference(binder_type));
                w.u32(reference(body));
                // The upstream `BinderInfo.toUInt64` numbering, as in `SCHEMA_EXPR`.
                w.u8(binder_info.to_u64() as u8);
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                w.u8(tag::EXPR_LET);
                decl_name.write_body(&mut w);
                w.u32(reference(type_));
                w.u32(reference(value));
                w.u32(reference(body));
                w.bool(*non_dep);
            }
            ExprNode::Lit { literal } => match literal {
                Literal::Nat(n) => {
                    w.u8(tag::EXPR_LIT_NAT);
                    w.u64(n.limbs_le().len() as u64);
                    for limb in n.limbs_le() {
                        w.u64(*limb);
                    }
                }
                Literal::Str(s) => {
                    w.u8(tag::EXPR_LIT_STR);
                    w.str(s);
                }
            },
            ExprNode::MData { data, expr } => {
                w.u8(tag::EXPR_MDATA);
                data.write_body(&mut w);
                w.u32(reference(expr));
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                w.u8(tag::EXPR_PROJ);
                struct_name.write_body(&mut w);
                w.u64(*idx);
                w.u32(reference(expr));
            }
        }
    }
    (!w.overflowed()).then(|| w.into_bytes())
}

fn decode_checker_expr(
    expression: &Expr,
    budget: CheckerDecodeBudget,
) -> Result<CheckerExpr, String> {
    // Terms cross as their DAG: canonical tree bytes do not preserve sharing,
    // and one Init theorem's tree encoding is 727 MB over 7,419 distinct nodes.
    // The checker would refuse anything past its input budget, so never build
    // more encoding than it can read.
    let limit = usize::try_from(budget.max_input_bytes).unwrap_or(usize::MAX);
    let Some(bytes) = encode_checker_expr_dag(expression, limit) else {
        return Err(format!(
            "shared expression encoding exceeds the checker's {limit}-byte decode budget"
        ));
    };
    match checker_decode_expr_dag(&bytes, budget) {
        CheckerDecodeOutcome::Complete(Ok(expression)) => Ok(expression),
        CheckerDecodeOutcome::Complete(Err(malformed)) => {
            Err(format!("shared expression decode failed: {malformed:?}"))
        }
        CheckerDecodeOutcome::Inconclusive(stop) => {
            Err(format!("shared expression decode did not finish: {stop:?}"))
        }
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
        ConstantInfo::Quot(value) => {
            let kind = match value.kind {
                QuotKind::Type => CheckerQuotientKind::Type,
                QuotKind::Ctor => CheckerQuotientKind::Constructor,
                QuotKind::Lift => CheckerQuotientKind::Lift,
                QuotKind::Ind => CheckerQuotientKind::Induction,
            };
            CheckerConstantDeclaration::quotient(level_parameters, type_, kind)
        }
        ConstantInfo::Induct(value) => CheckerConstantDeclaration::inductive(
            level_parameters,
            type_,
            checker_constant_safety(value.is_unsafe),
            CheckerInductiveDeclaration::new(
                value.num_params,
                value.num_indices,
                decode_checker_names(&value.all, budget)?,
                decode_checker_names(&value.ctors, budget)?,
                value.num_nested,
                value.is_rec,
                value.is_reflexive,
            ),
        ),
        ConstantInfo::Ctor(value) => CheckerConstantDeclaration::constructor(
            level_parameters,
            type_,
            checker_constant_safety(value.is_unsafe),
            CheckerConstructorDeclaration::new(
                decode_checker_name(&value.induct, budget)?,
                value.cidx,
                value.num_params,
                value.num_fields,
            ),
        ),
        ConstantInfo::Rec(value) => {
            let mut rules = Vec::new();
            rules.try_reserve_exact(value.rules.len()).map_err(|_| {
                format!(
                    "could not reserve {} checker recursor rules",
                    value.rules.len()
                )
            })?;
            for rule in &value.rules {
                rules.push(CheckerRecursorRule::new(
                    decode_checker_name(&rule.ctor, budget)?,
                    rule.nfields,
                    decode_checker_expr(&rule.rhs, budget)?,
                ));
            }
            CheckerConstantDeclaration::recursor(
                level_parameters,
                type_,
                checker_constant_safety(value.is_unsafe),
                CheckerRecursorDeclaration::new(
                    decode_checker_names(&value.all, budget)?,
                    value.num_params,
                    value.num_indices,
                    value.num_motives,
                    value.num_minors,
                    rules,
                    value.k,
                ),
            )
        }
    };
    Ok(CheckerConstantEntry::new(name, declaration))
}

/// Constants the independent checker resolves by spelling (literal typing and
/// the Nat, String and Bool reducers) rather than by a reference in the term,
/// so a projection covering a candidate carries them whenever they exist.
const CHECKER_BUILTIN_NAMES: &[&[&str]] = &[
    &["Nat"],
    &["Nat", "zero"],
    &["Nat", "succ"],
    &["Nat", "rec"],
    &["Bool"],
    &["Bool", "true"],
    &["Bool", "false"],
    &["Eq"],
    &["Eq", "refl"],
    &["String"],
    &["String", "ofList"],
    &["Char"],
    &["Char", "ofNat"],
    &["List"],
    &["List", "nil"],
    &["List", "cons"],
];

const QUOTIENT_FAMILY: &[&[&str]] = &[
    &["Quot"],
    &["Quot", "mk"],
    &["Quot", "lift"],
    &["Quot", "ind"],
];

fn collect_constant_names(
    root: &Expr,
    seen: &mut std::collections::HashSet<*const ExprNode>,
    out: &mut Vec<Name>,
) {
    let mut stack = vec![root];
    while let Some(expr) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(expr.node())) {
            continue;
        }
        match expr.node() {
            ExprNode::Const { name, .. } => out.push(name.clone()),
            ExprNode::Proj {
                struct_name, expr, ..
            } => {
                out.push(struct_name.clone());
                stack.push(expr);
            }
            ExprNode::App { f, a } => {
                stack.push(f);
                stack.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(type_);
                stack.push(value);
                stack.push(body);
            }
            ExprNode::MData { expr, .. } => stack.push(expr),
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
}

/// Queue what the checker can reach through one projected base constant.
/// Theorem and opaque bodies are never unfolded by the checker, so they are
/// not followed (and [`checker_base_entry`] does not project them).
fn queue_base_dependencies(
    info: &ConstantInfo,
    seen: &mut std::collections::HashSet<*const ExprNode>,
    pending: &mut Vec<Name>,
) {
    collect_constant_names(&info.constant_val().type_, seen, pending);
    match info {
        ConstantInfo::Defn(value) => collect_constant_names(&value.value, seen, pending),
        ConstantInfo::Induct(value) => {
            pending.extend(value.all.iter().cloned());
            pending.extend(value.ctors.iter().cloned());
        }
        ConstantInfo::Ctor(value) => pending.push(value.induct.clone()),
        ConstantInfo::Rec(value) => {
            pending.extend(value.all.iter().cloned());
            for rule in &value.rules {
                pending.push(rule.ctor.clone());
                collect_constant_names(&rule.rhs, seen, pending);
            }
        }
        ConstantInfo::Quot(_) => pending.extend(
            QUOTIENT_FAMILY
                .iter()
                .map(|parts| Name::from_components(parts.iter().copied())),
        ),
        ConstantInfo::Axiom(_) | ConstantInfo::Thm(_) | ConstantInfo::Opaque(_) => {}
    }
}

/// A base constant as the checker sees it: theorem and opaque bodies are
/// dropped because the checker only delta-unfolds safe definitions, which keeps
/// proof terms whose tree encoding runs to hundreds of megabytes out of every
/// check that merely cites them.
fn checker_base_entry(
    info: &ConstantInfo,
    budget: CheckerDecodeBudget,
) -> Result<CheckerConstantEntry, String> {
    let (kind, safety) = match info {
        ConstantInfo::Thm(_) => (CheckerConstantKind::Theorem, CheckerConstantSafety::Safe),
        ConstantInfo::Opaque(value) => (
            CheckerConstantKind::Opaque,
            checker_constant_safety(value.is_unsafe),
        ),
        _ => return checker_entry(info, budget),
    };
    let base = info.constant_val();
    Ok(CheckerConstantEntry::new(
        decode_checker_name(&base.name, budget)?,
        CheckerConstantDeclaration::header(
            decode_checker_names(&base.level_params, budget)?,
            decode_checker_expr(&base.type_, budget)?,
            kind,
            safety,
        ),
    ))
}

/// The checker environment a candidate is reviewed against: `retained` (or an
/// empty projection) extended with every base constant the candidate's terms
/// can reach and that is not projected yet.
///
/// A constant this walk misses can only make the checker report an unknown
/// constant, which is a non-answer and never an admission. With no retained
/// projection the aggregate environment budget bounds the whole closure; with
/// one, the constants added here are counted against `max_constants` because
/// each `extend` bounds only its own entry.
fn checker_environment_covering(
    environment: &Environment,
    retained: Option<&CheckerConstantEnvironment>,
    roots: &[&Expr],
    limits: CheckerExecutionLimits,
) -> Result<CheckerConstantEnvironment, String> {
    let mut seen = std::collections::HashSet::new();
    let mut pending = Vec::new();
    for root in roots {
        collect_constant_names(root, &mut seen, &mut pending);
    }
    pending.extend(
        CHECKER_BUILTIN_NAMES
            .iter()
            .map(|parts| Name::from_components(parts.iter().copied())),
    );
    let mut visited = BTreeSet::new();
    let mut entries = Vec::new();
    while let Some(name) = pending.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        let Some(info) = environment.find(&name) else {
            continue;
        };
        if let Some(retained) = retained
            && retained
                .find(&decode_checker_name(&name, limits.decode)?)
                .is_some()
        {
            continue;
        }
        entries.push(checker_base_entry(info, limits.decode)?);
        queue_base_dependencies(info, &mut seen, &mut pending);
    }
    let outcome = match retained {
        None => CheckerConstantEnvironment::build(entries, limits.environment),
        Some(retained) => {
            let added = u64::try_from(entries.len()).unwrap_or(u64::MAX);
            if added > limits.environment.max_constants {
                return Err(format!(
                    "covering {added} base constants exceeds the checker constant budget {}",
                    limits.environment.max_constants
                ));
            }
            let mut projected = retained.clone();
            for entry in entries {
                match projected.extend(entry, limits.environment) {
                    CheckerEnvironmentOutcome::Complete { environment, .. } => {
                        projected = environment;
                    }
                    other => return checker_projection_failure(other),
                }
            }
            return Ok(projected);
        }
    };
    match outcome {
        CheckerEnvironmentOutcome::Complete { environment, .. } => Ok(environment),
        other => checker_projection_failure(other),
    }
}

fn checker_projection_failure(
    outcome: CheckerEnvironmentOutcome,
) -> Result<CheckerConstantEnvironment, String> {
    Err(match outcome {
        CheckerEnvironmentOutcome::Complete { .. } => {
            "checker environment projection completed where a failure was reported".to_owned()
        }
        CheckerEnvironmentOutcome::Refused { refusal, .. } => {
            format!("checker environment refused its projection: {refusal:?}")
        }
        CheckerEnvironmentOutcome::Inconclusive(stop) => {
            format!("checker environment projection did not finish: {stop:?}")
        }
        CheckerEnvironmentOutcome::InternalFault { fault, .. } => {
            format!("checker environment projection hit an internal fault: {fault:?}")
        }
    })
}

fn review_mutual_with_independent_checker(
    environment: &Environment,
    retained_environment: Option<&CheckerConstantEnvironment>,
    definitions: &[DefinitionVal],
    limits: CheckerExecutionLimits,
    reading: ReadingCheck<'_>,
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
    if let Some(review) = reading_review(&candidates, reading) {
        return review;
    }

    let roots: Vec<&Expr> = definitions
        .iter()
        .flat_map(|definition| [&definition.base.type_, &definition.value])
        .collect();
    let environment =
        match checker_environment_covering(environment, retained_environment, &roots, limits) {
            Ok(environment) => environment,
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "base projection into fln-checker failed: {detail}"
                ));
            }
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

fn review_quotient_with_independent_checker(
    environment: &Environment,
    retained_environment: Option<&CheckerConstantEnvironment>,
    declarations: &[QuotVal],
    limits: CheckerExecutionLimits,
    reading: ReadingCheck<'_>,
) -> CheckerReview {
    let mut candidates = Vec::new();
    if candidates.try_reserve_exact(declarations.len()).is_err() {
        return CheckerReview::no_answer(format!(
            "could not reserve {} checker quotient members",
            declarations.len()
        ));
    }
    for (index, declaration) in declarations.iter().enumerate() {
        match checker_entry(&ConstantInfo::Quot(declaration.clone()), limits.decode) {
            Ok(candidate) => candidates.push(candidate),
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "quotient member {index} projection into fln-checker failed: {detail}"
                ));
            }
        }
    }
    if let Some(review) = reading_review(&candidates, reading) {
        return review;
    }

    let roots: Vec<&Expr> = declarations
        .iter()
        .map(|declaration| &declaration.base.type_)
        .collect();
    let environment =
        match checker_environment_covering(environment, retained_environment, &roots, limits) {
            Ok(environment) => environment,
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "base projection into fln-checker failed: {detail}"
                ));
            }
        };

    match fln_checker::admit::admit_quotient(&environment, &candidates, limits.admission) {
        CheckerQuotientVerdict::Admitted(admission) => {
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
                            "fln-checker refused quotient member {member:?} retention: {refusal:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::Inconclusive(stop) => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker could not retain quotient member {member:?}: {stop:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::InternalFault { fault, .. } => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker faulted while retaining quotient member {member:?}: \
                             {fault:?}"
                        ));
                    }
                }
            }
            CheckerReview::from_seat(SeatVerdict::Agrees, Some(agreement), Some(successor))
        }
        CheckerQuotientVerdict::Rejected(rejection) => CheckerReview::from_seat(
            SeatVerdict::Disagrees {
                detail: format!("fln-checker rejected quotient initialization: {rejection:?}"),
            },
            None,
            None,
        ),
        CheckerQuotientVerdict::Inconclusive(stop) => CheckerReview::no_answer(format!(
            "fln-checker exhausted or was cancelled during quotient initialization: {stop:?}"
        )),
        CheckerQuotientVerdict::InternalFault(fault) => CheckerReview::no_answer(format!(
            "fln-checker faulted during quotient initialization: {fault:?}"
        )),
    }
}

fn review_inductive_with_independent_checker(
    environment: &Environment,
    retained_environment: Option<&CheckerConstantEnvironment>,
    block: &fln_kernel::InductiveBlock,
    limits: CheckerExecutionLimits,
    reading: ReadingCheck<'_>,
) -> CheckerReview {
    let member_count = block
        .types
        .len()
        .saturating_add(block.ctors.len())
        .saturating_add(block.recursors.len());
    let mut candidates = Vec::new();
    if candidates.try_reserve_exact(member_count).is_err() {
        return CheckerReview::no_answer(format!(
            "could not reserve {member_count} checker inductive-block members"
        ));
    }
    for declaration in &block.types {
        match checker_entry(&ConstantInfo::Induct(declaration.clone()), limits.decode) {
            Ok(candidate) => candidates.push(candidate),
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "inductive type projection into fln-checker failed: {detail}"
                ));
            }
        }
    }
    for declaration in &block.ctors {
        match checker_entry(&ConstantInfo::Ctor(declaration.clone()), limits.decode) {
            Ok(candidate) => candidates.push(candidate),
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "constructor projection into fln-checker failed: {detail}"
                ));
            }
        }
    }
    for declaration in &block.recursors {
        match checker_entry(&ConstantInfo::Rec(declaration.clone()), limits.decode) {
            Ok(candidate) => candidates.push(candidate),
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "recursor projection into fln-checker failed: {detail}"
                ));
            }
        }
    }
    if let Some(review) = reading_review(&candidates, reading) {
        return review;
    }

    let mut roots: Vec<&Expr> = block
        .types
        .iter()
        .map(|declaration| &declaration.base.type_)
        .chain(
            block
                .ctors
                .iter()
                .map(|declaration| &declaration.base.type_),
        )
        .collect();
    for recursor in &block.recursors {
        roots.push(&recursor.base.type_);
        roots.extend(recursor.rules.iter().map(|rule| &rule.rhs));
    }
    let environment =
        match checker_environment_covering(environment, retained_environment, &roots, limits) {
            Ok(environment) => environment,
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "base projection into fln-checker failed: {detail}"
                ));
            }
        };

    match fln_checker::admit::admit_inductive(
        &environment,
        &candidates,
        limits.admission,
        limits.environment,
    ) {
        CheckerInductiveVerdict::Admitted(admission) => {
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
                            "fln-checker refused inductive member {member:?} retention: {refusal:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::Inconclusive(stop) => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker could not retain inductive member {member:?}: {stop:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::InternalFault { fault, .. } => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker faulted while retaining inductive member {member:?}: \
                             {fault:?}"
                        ));
                    }
                }
            }
            CheckerReview::from_seat(SeatVerdict::Agrees, Some(agreement), Some(successor))
        }
        CheckerInductiveVerdict::Rejected(rejection) => CheckerReview::from_seat(
            SeatVerdict::Disagrees {
                detail: format!("fln-checker rejected the inductive block: {rejection:?}"),
            },
            None,
            None,
        ),
        CheckerInductiveVerdict::Deferred(limit) => {
            let names = block
                .types
                .iter()
                .map(|inductive| inductive.base.name.to_display_string())
                .collect::<Vec<_>>()
                .join(", ");
            CheckerReview::no_answer(format!(
                "fln-checker does not yet decide this inductive shape of [{names}]: {limit:?}"
            ))
        }
        CheckerInductiveVerdict::Inconclusive(stop) => CheckerReview::no_answer(format!(
            "fln-checker exhausted or was cancelled during inductive admission: {stop:?}"
        )),
        CheckerInductiveVerdict::InternalFault(fault) => CheckerReview::no_answer(format!(
            "fln-checker faulted during inductive admission: {fault:?}"
        )),
    }
}

fn review_with_independent_checker(
    environment: &Environment,
    retained_environment: Option<&CheckerConstantEnvironment>,
    declaration: &Declaration,
    limits: CheckerExecutionLimits,
    reading: ReadingCheck<'_>,
) -> CheckerReview {
    if let Declaration::Mutual(definitions) = declaration {
        return review_mutual_with_independent_checker(
            environment,
            retained_environment,
            definitions,
            limits,
            reading,
        );
    }
    if let Declaration::Quotient(declarations) = declaration {
        return review_quotient_with_independent_checker(
            environment,
            retained_environment,
            declarations,
            limits,
            reading,
        );
    }
    if let Declaration::Inductive(block) = declaration {
        return review_inductive_with_independent_checker(
            environment,
            retained_environment,
            block,
            limits,
            reading,
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
    if let Some(review) = reading_review(std::slice::from_ref(&candidate), reading) {
        return review;
    }
    let roots: Vec<&Expr> = match declaration {
        Declaration::Axiom(axiom) => vec![&axiom.base.type_],
        Declaration::Defn(definition) => vec![&definition.base.type_, &definition.value],
        Declaration::Thm(theorem) => vec![&theorem.base.type_, &theorem.value],
        Declaration::Opaque(opaque) => vec![&opaque.base.type_, &opaque.value],
        _ => Vec::new(),
    };
    let environment =
        match checker_environment_covering(environment, retained_environment, &roots, limits) {
            Ok(environment) => environment,
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "base projection into fln-checker failed: {detail}"
                ));
            }
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
    scalar_constructors: Vec<ScalarConstructorBinding>,
    intrinsics: Vec<IntrinsicBinding>,
    functions: Vec<FunctionBinding>,
}

struct ExecutableValueTypes {
    nat: Expr,
    string: Expr,
    bool_: Expr,
    float: Expr,
    float32: Expr,
    uint32: Expr,
    uint64: Expr,
    records: std::collections::HashSet<Expr>,
    closures: std::collections::HashMap<Expr, ValueType>,
}

impl ExecutableValueTypes {
    fn bounded_source() -> Self {
        Self {
            nat: Expr::const_(Name::from_components(["Nat"]), Vec::new()),
            string: Expr::const_(Name::from_components(["String"]), Vec::new()),
            bool_: Expr::const_(Name::from_components(["Bool"]), Vec::new()),
            float: Expr::const_(Name::from_components(["Float"]), Vec::new()),
            float32: Expr::const_(Name::from_components(["Float32"]), Vec::new()),
            uint32: Expr::const_(Name::from_components(["UInt32"]), Vec::new()),
            uint64: Expr::const_(Name::from_components(["UInt64"]), Vec::new()),
            records: std::collections::HashSet::new(),
            closures: std::collections::HashMap::new(),
        }
    }
}

fn executable_dependencies(
    environment: &Environment,
    source: &Expr,
    limits: IngressLimits,
    preparation: &mut runtime::Preparation<'_>,
) -> Result<ExecutableCatalog, IngressError> {
    let mut pending = BTreeSet::new();
    let mut resolved = BTreeSet::new();
    let mut visited_nodes = 0usize;
    collect_executable_constants(source, &mut pending, &mut visited_nodes, limits)?;

    let maximum_functions = limits.fir.max_functions.saturating_sub(1);
    let mut scalar_constructors = Vec::new();
    let mut intrinsics = Vec::new();
    let mut functions = Vec::new();
    let mut scanned_lambdas = 0;
    loop {
        // A mutual closure group's peers live in the callable catalog, not
        // necessarily in the selected member's expression. They may introduce
        // otherwise invisible intrinsics or checked function dependencies.
        // Scan each newly prepared body exactly once, including peers created
        // while resolving a dependency, before deciding the worklist is empty.
        while let Some(lambda) = preparation.lambdas.get(scanned_lambdas) {
            if matches!(lambda.recursion, LambdaRecursion::MutualMember { .. }) {
                collect_executable_constants(
                    &lambda.lambda,
                    &mut pending,
                    &mut visited_nodes,
                    limits,
                )?;
            }
            scanned_lambdas += 1;
        }
        let Some(name) = pending.pop_first() else {
            break;
        };
        if !resolved.insert(name.clone()) {
            continue;
        }
        if let Some(binding) = source_scalar_constructor_binding(environment, &name) {
            scalar_constructors
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: 1,
                })?;
            scalar_constructors.push(binding);
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
        let definition = match environment.find(&name) {
            Some(ConstantInfo::Defn(definition)) => Some(definition.clone()),
            _ => preparation.specialized_definition(&name),
        };
        let Some(definition) = definition else {
            continue;
        };
        let Some(mut signature) = preparation.signature(&definition, true)? else {
            continue;
        };
        signature.body = preparation.expression(&signature.body)?;
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
        scalar_constructors,
        intrinsics,
        functions,
    })
}

/// Look up whether `name` is one of the Bool constructors (`Bool.false`,
/// `Bool.true`) in the given environment, and if so return its
/// `ScalarConstructorBinding`. The match requires that the environment's
/// constructor metadata agrees with the seed declaration byte-for-byte.
///
/// This is the same predicate the bounded source compiler uses when deciding
/// whether a constructor reference can be lowered to a scalar value. Tooling
/// that wants to know "is this name a scalar constructor?" can call this
/// without running the full compiler ingress.
pub fn source_scalar_constructor_binding(
    environment: &Environment,
    name: &Name,
) -> Option<ScalarConstructorBinding> {
    let value = if name == &Name::from_components(["Bool", "false"]) {
        false
    } else if name == &Name::from_components(["Bool", "true"]) {
        true
    } else {
        return None;
    };
    let ConstantInfo::Ctor(actual) = environment.find(name)? else {
        return None;
    };
    let Declaration::Inductive(expected_block) = fln_elab::seed::bool_seed_declaration() else {
        return None;
    };
    let expected = expected_block
        .ctors
        .iter()
        .find(|constructor| &constructor.base.name == name)?;
    if actual != expected {
        return None;
    }
    Some(ScalarConstructorBinding {
        name: name.clone(),
        universe_arity: 0,
        value,
    })
}

fn source_intrinsic_binding(environment: &Environment, name: &Name) -> Option<IntrinsicBinding> {
    let info = environment.find(name)?;
    let expected = fln_elab::seed::source_intrinsic_seed_declaration(name)
        .or_else(|| fln_elab::seed::float_intrinsic_seed_declaration(name))?;
    let expected = match expected {
        Declaration::Axiom(value) => ConstantInfo::Axiom(value),
        Declaration::Defn(value) => ConstantInfo::Defn(value),
        _ => return None,
    };
    // A definition receives the intrinsic only when its entire checked body,
    // safety and telescope match the source seed. A familiar name is not enough.
    if info != &expected {
        return None;
    }
    if name == &Name::from_components(["Nat", "add"])
        && !fln_elab::seed::has_nat_add_seed_dependencies(environment)
    {
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
        "Nat.decLe" | "Nat.decLt" => (vec![ValueType::Nat, ValueType::Nat], ValueType::Bool, None),
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
        _ => {
            let (family, operation) = row_name.split_once('.')?;
            let scalar = match family {
                "Float" => ValueType::Float,
                "Float32" => ValueType::Float32,
                "UInt32" => ValueType::UInt32,
                "UInt64" => ValueType::UInt64,
                _ => return None,
            };
            let floating = matches!(scalar, ValueType::Float | ValueType::Float32);
            match operation {
                "add" | "sub" | "mul" | "div" if floating => (vec![scalar, scalar], scalar, None),
                "neg" | "abs" if floating => (vec![scalar], scalar, None),
                "beq" | "decLt" | "decLe" if floating => {
                    (vec![scalar, scalar], ValueType::Bool, None)
                }
                "isNaN" | "isFinite" | "isInf" if floating => (vec![scalar], ValueType::Bool, None),
                "toString" if floating => (vec![scalar], ValueType::String, None),
                "toBits" if floating => (
                    vec![scalar],
                    if scalar == ValueType::Float {
                        ValueType::UInt64
                    } else {
                        ValueType::UInt32
                    },
                    None,
                ),
                "ofBits" if floating => (
                    vec![if scalar == ValueType::Float {
                        ValueType::UInt64
                    } else {
                        ValueType::UInt32
                    }],
                    scalar,
                    None,
                ),
                "toUInt64" if floating => (vec![scalar], ValueType::UInt64, None),
                "toUInt32" if floating => (vec![scalar], ValueType::UInt32, None),
                "toFloat" => (vec![scalar], ValueType::Float, None),
                "toFloat32" => (vec![scalar], ValueType::Float32, None),
                "ofNat" if !floating => (vec![ValueType::Nat], scalar, None),
                "toNat" if !floating => (vec![scalar], ValueType::Nat, None),
                _ => return None,
            }
        }
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
    prepared: &Expr,
    preparation: &mut runtime::Preparation<'_>,
) -> Result<Option<LambdaBinding>, IngressError> {
    let Declaration::Defn(definition) = declaration else {
        return Ok(None);
    };
    let Some(mut signature) = preparation.signature(definition, false)? else {
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
    preparation.refine_local_result(&mut signature, prepared)?;
    let parameter_ownership = borrowed_runtime_parameters(signature.parameters.len())?;
    Ok(Some(LambdaBinding {
        lambda: prepared.clone(),
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
/// Every real lambda binder must match its Pi binder structurally. A local
/// lambda may end its spine with a represented callback result: its strict body
/// runs when that prefix is applied, not when the returned callback is called.
/// Global definitions keep their existing flat ABI and eta-expansion policy.
/// K1 has already proved the declaration well typed, but this bridge still
/// requires exact runtime representations. The returned body has its real
/// top-level lambdas removed, as required by [`FunctionBinding`].
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
                    if !eta_expand
                        && !parameters.is_empty()
                        && matches!(
                            executable_value_type(declared_type, value_types),
                            Some((ValueType::Closure(_), _))
                        )
                    {
                        // This is a real stage boundary, not missing lambdas.
                        // FIR owns and returns the suffix closure. Do not move
                        // the strict prefix body beneath invented binders.
                        break;
                    }
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
    } else if source == &value_types.float {
        Some((ValueType::Float, CallableResultOwnership::Owned))
    } else if source == &value_types.float32 {
        Some((ValueType::Float32, CallableResultOwnership::Owned))
    } else if source == &value_types.uint32 {
        Some((ValueType::UInt32, CallableResultOwnership::Scalar))
    } else if source == &value_types.uint64 {
        Some((ValueType::UInt64, CallableResultOwnership::Owned))
    } else if let Some(value) = value_types.closures.get(source) {
        Some((*value, CallableResultOwnership::Owned))
    } else if value_types.records.contains(source) {
        Some((ValueType::Constructor, CallableResultOwnership::Owned))
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
        let term = fln_checker::term::TermBudget::new(100_000_000, 200_000_000)
            .with_max_arena_nodes(100_000_000);
        let whnf = fln_checker::whnf::WhnfBudget::new(100_000_000, 100_000_000, term);
        let inference =
            fln_checker::infer::InferenceBudget::new(100_000_000, 100_000_000, term, term)
                .with_whnf(whnf);
        // Every unit the decoder produces reads at least one input byte right
        // after it is charged, so the byte bound already bounds the units. A
        // unit bound below it would refuse inputs the byte bound admits: at
        // 1_000_000 it stopped five whole-Init frontier modules on proofs well
        // under 16 MiB.
        let decode_bytes = 16 * 1024 * 1024;
        Self {
            decode: CheckerDecodeBudget::new(decode_bytes, decode_bytes),
            environment: CheckerEnvironmentBudget::new(
                20_000_000,
                100_000,
                100_000,
                100_000,
                20_000_000,
                200_000_000,
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

    /// Calibrate admission limits to the specified thread stack size in bytes.
    pub fn for_stack_bytes(bytes: usize) -> Self {
        Self::new(Budget::for_stack_bytes(bytes))
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
    pub source_modules: SourceModuleLimits,
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
            source_modules: SourceModuleLimits::default(),
        }
    }

    /// Calibrate execution limits to the specified thread stack size in bytes.
    pub fn for_stack_bytes(bytes: usize) -> Self {
        Self::new(Budget::for_stack_bytes(bytes))
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

/// Explicit planning bounds for a closed bounded-source import graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceModuleLimits {
    pub max_modules: usize,
    pub max_imports: usize,
    pub max_name_depth: usize,
    /// Maximum expression-node presentations while proving that declarations
    /// use only their own module or transitive imports.
    pub max_dependency_presentations: usize,
}

impl Default for SourceModuleLimits {
    fn default() -> Self {
        Self {
            max_modules: 4_096,
            max_imports: 65_536,
            max_name_depth: 256,
            max_dependency_presentations: 1_000_000,
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

/// One admission without its root transition: what
/// `Engine::admit_declaration_unrooted` returns, and all the `.olean` check reads.
struct UnrootedAdmission {
    engine: Engine,
    declaration: Declaration,
    checker: CheckerAgreement,
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
    /// The admitted type with safe aliases normalized by the same metered
    /// runtime preparation that produced the bytecode. Presentation uses this
    /// type, not the runtime object's tag, to distinguish Nat from Bool. The
    /// exact checked declaration above remains unchanged.
    pub runtime_type: Expr,
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

/// One bounded `#check` query or anonymous example validated by both checker seats.
///
/// The generated declaration is admitted only into a scratch successor. That
/// successor is deliberately not retained here: a check query observes the
/// current environment and cannot publish a source-visible or generated row.
/// Its body is never compiled or executed.
#[derive(Debug)]
pub struct SourceCheck {
    /// The canonical parsed check command and its source-covered term.
    pub parsed: ParsedSourceCommand,
    /// The exact generated definition candidate reviewed by both checkers.
    pub declaration: Declaration,
    /// The inferred type K1 and the independent checker accepted for the term.
    pub checked_type: Expr,
    /// The unchanged queried-environment identity under the caller's options.
    pub environment_root: LogicalRoot,
    /// The independent checker observation that allowed the council to agree.
    pub checker: CheckerAgreement,
}

/// One completed definition-only source prefix followed by a terminal check.
///
/// A standalone check has no prefix. When present, the prefix successor is the
/// exact environment recorded by [`SourceCheck`]; the query's own scratch
/// successor is never exposed.
#[derive(Debug)]
pub struct TerminalSourceCheck {
    /// The completed definition prefix, absent for a standalone query.
    pub definition_prefix: Option<DefinitionBatchExecution>,
    /// Canonical dependency-first module order, empty for an import-free query.
    pub source_module_order: Vec<Name>,
    /// The terminal query checked against the prefix successor.
    pub check: SourceCheck,
}

/// One query or anonymous-check event in an ordered import-free source stream.
///
/// Definitions have no output row. Evaluation rows point into the retained
/// execution batch; checks and silent examples point into the scratch-only table.
#[derive(Debug)]
pub enum SourceCommandOutput {
    Evaluation {
        command_index: usize,
        execution_index: usize,
    },
    Check {
        command_index: usize,
        check_index: usize,
    },
    /// A checked example has no textual output, but its dependencies remain
    /// visible to the module-visibility validator until the batch is complete.
    Example {
        command_index: usize,
        check_index: usize,
    },
}

/// The completed result of an import-free mixed source command stream.
///
/// `execution_command_indices` maps every retained definition/evaluation
/// execution back to its original source command. Query candidates never enter
/// that batch or its final engine.
#[derive(Debug)]
pub struct SourceCommandBatchExecution {
    pub batch: DefinitionBatchExecution,
    pub command_count: usize,
    pub execution_command_indices: Vec<usize>,
    pub outputs: Vec<SourceCommandOutput>,
    pub checks: Vec<SourceCheck>,
}

/// A closed dependency graph followed by its selected entry command stream.
#[derive(Debug)]
pub struct SourceModuleCommandBatchExecution {
    /// Completed silent dependency definition/evaluation execution, absent for
    /// an entry with no executable dependency commands.
    pub dependency_prefix: Option<DefinitionBatchExecution>,
    /// Number of source commands in the flattened dependency prefix, including
    /// silent scratch checks that do not enter `dependency_prefix`.
    pub dependency_command_count: usize,
    /// Original flattened dependency command index for every retained prefix
    /// execution. This table includes gaps for scratch-only checks.
    pub dependency_execution_command_indices: Vec<usize>,
    /// Canonical dependency-first module order, including the entry last.
    pub source_module_order: Vec<Name>,
    /// The selected entry's ordered definition/evaluation/check result.
    pub entry: SourceCommandBatchExecution,
}

/// One exact source module in a caller-supplied closed import set.
///
/// `name` is resolver authority supplied by the caller. The source header must
/// agree by importing only other names present in the same closed set; the
/// engine never invents a missing predecessor environment.
#[derive(Debug, Clone, Copy)]
pub struct SourceModuleInput<'source> {
    pub name: &'source Name,
    pub source: &'source [u8],
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
    /// Canonical dependency order for a closed source-module execution.
    /// Empty for declaration batches and legacy caller-ordered source batches.
    pub source_module_order: Vec<Name>,
    /// Strictly increasing execution indices for source `#eval` commands
    /// lowered through checked generated definitions. Empty for
    /// already-elaborated and definition-only batches.
    pub source_evaluation_indices: Vec<usize>,
    /// Checked source commands that publish declarations but do not execute:
    /// structures, inductives, and theorems. Includes every generated declaration.
    pub source_admissions: Vec<SourceCommandAdmission>,
    /// Original source command index for each execution, including gaps for
    /// admission-only commands and scratch checks. Empty for raw declaration batches.
    pub source_execution_command_indices: Vec<usize>,
}

/// One source command's complete, dual-checked admission without VM execution.
#[derive(Debug)]
pub struct SourceCommandAdmission {
    pub command_index: usize,
    pub admission: DeclarationBatchAdmission,
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
    /// A council seat disagreed with the kernel's acceptance.
    CouncilHalted {
        summary: String,
    },
    /// Every objecting seat was silent or ran out: nothing was learned about the
    /// declaration (FL-INV-07), and it was not published.
    CouncilNoAnswer {
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
            Self::CouncilNoAnswer { summary } => {
                write!(formatter, "council had no answer: {summary}")
            }
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

/// A refusal before Golem execution. Inference failures retain typed causes,
/// including complete kernel nonanswers from speculative assignment checks.
#[derive(Debug, Clone, PartialEq)]
pub enum EngineExecutionError {
    EmptyBatch,
    SourceModuleLimit {
        observed: usize,
        limit: usize,
    },
    SourceImportLimit {
        observed: usize,
        limit: usize,
    },
    SourceModuleNameLimit {
        module: Name,
        observed: usize,
        limit: usize,
    },
    InvalidSourceModuleName {
        module: Name,
    },
    ImportsRequireResolver {
        imports: Vec<Name>,
    },
    DuplicateSourceModule {
        module: Name,
    },
    MissingSourceEntry {
        module: Name,
    },
    EmptySourceEntry {
        module: Name,
    },
    MissingSourceImports {
        module: Name,
        imports: Vec<Name>,
    },
    UnreachableSourceModules {
        entry: Name,
        modules: Vec<Name>,
    },
    SourceModuleCycle {
        modules: Vec<Name>,
    },
    SourceDependencyPresentationLimit {
        observed: usize,
        limit: usize,
    },
    SourceModuleVisibility {
        module: Name,
        declaration: Name,
        referenced: Name,
        owner: Name,
    },
    AllocationFailure {
        resource: &'static str,
        requested: usize,
    },
    BatchCommand {
        index: usize,
        error: Box<EngineExecutionError>,
        /// Byte offset (file coordinates) of the command that failed, when the
        /// caller knew it. Locates an elaboration or kernel refusal — which carry
        /// no source position of their own — to the command's line; a parse
        /// refusal keeps its own token-precise offset in preference.
        at: Option<fln_parse::BytePos>,
    },
    StandaloneCheckRequired,
    TerminalCheckRequired,
    TerminalCheckDefinitionPrefix {
        index: usize,
    },
    TerminalCheckModuleDefinitionPrefix {
        module: Name,
        index: usize,
    },
    Frontend(NatDefinitionFrontendError),
    KernelRejected {
        class: RejectClass,
        message: String,
    },
    /// A council seat disagreed with the kernel's acceptance.
    CouncilHalted {
        summary: String,
    },
    /// Every objecting seat was silent or ran out: nothing was learned about the
    /// declaration (FL-INV-07), and it was not published.
    CouncilNoAnswer {
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

impl EngineExecutionError {
    /// The primary source byte offset this failure points at, or `None`.
    ///
    /// A per-command failure is unwrapped from [`EngineExecutionError::BatchCommand`],
    /// and a frontend refusal delegates to
    /// [`NatDefinitionFrontendError::primary_offset`], so a parse error yields the
    /// offending byte (already in the source file's coordinate system), while an
    /// elaboration refusal, a kernel rejection, an inconclusive/fault non-answer,
    /// or a structural planning fault yields `None` — no user-facing source
    /// position exists for those.
    pub fn primary_source_offset(&self) -> Option<fln_parse::BytePos> {
        match self {
            // Prefer the inner error's own token-precise offset (a parse refusal
            // has one) and fall back to the command-level offset the loop
            // attached — the only position an elaboration or kernel refusal can
            // offer.
            Self::BatchCommand { error, at, .. } => error.primary_source_offset().or(*at),
            Self::Frontend(error) => error.primary_offset(),
            _ => None,
        }
    }
}

impl fmt::Display for EngineExecutionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyBatch => write!(formatter, "definition batch must not be empty"),
            Self::SourceModuleLimit { observed, limit } => write!(
                formatter,
                "source set contains {observed} modules; planning limit is {limit}"
            ),
            Self::SourceImportLimit { observed, limit } => write!(
                formatter,
                "source set presents {observed} imports; planning limit is {limit}"
            ),
            Self::SourceModuleNameLimit {
                module,
                observed,
                limit,
            } => write!(
                formatter,
                "source module name `{}` has {observed} components; planning limit is {limit}",
                module.to_display_string()
            ),
            Self::InvalidSourceModuleName { module } => write!(
                formatter,
                "source module name `{}` is not a nonempty string-component name",
                module.to_display_string()
            ),
            Self::ImportsRequireResolver { imports } => write!(
                formatter,
                "source imports require a closed module resolver: {}",
                display_names(imports)
            ),
            Self::DuplicateSourceModule { module } => write!(
                formatter,
                "source set repeats module `{}`",
                module.to_display_string()
            ),
            Self::MissingSourceEntry { module } => write!(
                formatter,
                "source entry module `{}` is absent from the closed set",
                module.to_display_string()
            ),
            Self::EmptySourceEntry { module } => write!(
                formatter,
                "source entry module `{}` contains no supported command to execute",
                module.to_display_string()
            ),
            Self::MissingSourceImports { module, imports } => write!(
                formatter,
                "source module `{}` imports modules absent from the closed set: {}",
                module.to_display_string(),
                display_names(imports)
            ),
            Self::UnreachableSourceModules { entry, modules } => write!(
                formatter,
                "source modules are outside entry `{}`'s import closure: {}",
                entry.to_display_string(),
                display_names(modules)
            ),
            Self::SourceModuleCycle { modules } => write!(
                formatter,
                "source import graph contains a cycle: {}",
                display_names(modules)
            ),
            Self::SourceDependencyPresentationLimit { observed, limit } => write!(
                formatter,
                "source declarations presented {observed} expression nodes while checking import visibility; planning limit is {limit}"
            ),
            Self::SourceModuleVisibility {
                module,
                declaration,
                referenced,
                owner,
            } => write!(
                formatter,
                "source declaration `{}` in module `{}` references `{}` from module `{}` without a transitive import",
                declaration.to_display_string(),
                module.to_display_string(),
                referenced.to_display_string(),
                owner.to_display_string(),
            ),
            Self::AllocationFailure {
                resource,
                requested,
            } => write!(
                formatter,
                "could not reserve {requested} entries for {resource}"
            ),
            Self::BatchCommand { index, error, .. } => {
                write!(
                    formatter,
                    "definition batch command {index} failed: {error}"
                )
            }
            Self::StandaloneCheckRequired => write!(
                formatter,
                "#check requires the ordered import-free native lean command stream or one terminal entry query over a definition-only import closure, not this executable batch"
            ),
            Self::TerminalCheckRequired => write!(
                formatter,
                "bounded terminal-check execution requires #check as the final source command"
            ),
            Self::TerminalCheckDefinitionPrefix { index } => write!(
                formatter,
                "bounded terminal #check permits only definitions before it; command {index} is not a definition"
            ),
            Self::TerminalCheckModuleDefinitionPrefix { module, index } => write!(
                formatter,
                "bounded terminal #check permits only definitions in its import closure; command {index} in module `{}` is not a definition",
                module.to_display_string(),
            ),
            Self::Frontend(error) => write!(formatter, "frontend refused source: {error}"),
            Self::KernelRejected { class, message } => {
                write!(
                    formatter,
                    "kernel rejected declaration ({class:?}): {message}"
                )
            }
            Self::CouncilHalted { summary } => write!(formatter, "council halted: {summary}"),
            Self::CouncilNoAnswer { summary } => {
                write!(formatter, "council had no answer: {summary}")
            }
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
                at: None,
            },
            EngineAdmissionError::UnsupportedDeclaration { kind } => {
                Self::UnsupportedDeclaration { kind }
            }
            EngineAdmissionError::KernelRejected { class, message } => {
                Self::KernelRejected { class, message }
            }
            EngineAdmissionError::CouncilHalted { summary } => Self::CouncilHalted { summary },
            EngineAdmissionError::CouncilNoAnswer { summary } => Self::CouncilNoAnswer { summary },
            EngineAdmissionError::CheckerBridge { detail } => Self::CheckerBridge { detail },
            EngineAdmissionError::DuplicateName { name } => Self::DuplicateName { name },
            EngineAdmissionError::UnexpectedPublication { detail } => {
                Self::UnexpectedPublication { detail }
            }
        }
    }
}

/// Every field of two engines, one assertion each so a failure names the field.
/// Environments are compared by value, never printed: a closure's is too large.
#[cfg(test)]
pub(crate) fn assert_engines_identical(left: &Engine, right: &Engine, what: &str) {
    assert!(
        left.environment == right.environment,
        "{what}: environments differ ({} vs {} constants)",
        left.environment.len(),
        right.environment.len()
    );
    assert!(
        left.checker_environment == right.checker_environment,
        "{what}: retained checker projections differ ({:?} vs {:?} constants)",
        left.checker_environment
            .as_ref()
            .map(CheckerConstantEnvironment::len),
        right
            .checker_environment
            .as_ref()
            .map(CheckerConstantEnvironment::len)
    );
    assert_eq!(
        left.imported_modules, right.imported_modules,
        "{what}: imported modules"
    );
    assert!(
        left.imported_environment == right.imported_environment,
        "{what}: imported environment snapshots differ"
    );
    assert_eq!(
        left.imported_module_dependencies, right.imported_module_dependencies,
        "{what}: import edges"
    );
    assert_eq!(left.epoch, right.epoch, "{what}: epoch");
    assert_eq!(left.mode, right.mode, "{what}: mode");
    assert_eq!(
        left.reproducibility, right.reproducibility,
        "{what}: reproducibility"
    );
    assert_eq!(left.options, right.options, "{what}: options");
}

/// Two checked `.olean` sets, field by field and module by module.
#[cfg(test)]
pub(crate) fn assert_checked_sets_identical(
    left: &CheckedOleanSet,
    right: &CheckedOleanSet,
    what: &str,
) {
    assert_engines_identical(&left.engine, &right.engine, what);
    assert_eq!(
        left.base_logical_root, right.base_logical_root,
        "{what}: base root"
    );
    assert_eq!(
        left.result_logical_root, right.result_logical_root,
        "{what}: result root"
    );
    let names = |set: &CheckedOleanSet| -> Vec<Name> {
        set.modules
            .iter()
            .map(|module| module.name.clone())
            .collect()
    };
    assert_eq!(names(left), names(right), "{what}: module order");
    for (left, right) in left.modules.iter().zip(&right.modules) {
        let module = left.name.to_display_string();
        assert!(
            left.decoded == right.decoded,
            "{what}: {module}: decoded artifact"
        );
        assert_eq!(
            left.base_logical_root, right.base_logical_root,
            "{what}: {module}: base root"
        );
        assert_eq!(
            left.result_logical_root, right.result_logical_root,
            "{what}: {module}: result root"
        );
        assert_eq!(
            left.declarations, right.declarations,
            "{what}: {module}: checker rows"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{
        AxiomVal, BinderInfo, Budget, CheckerAdmissionBudget, CheckerAdmissionGround,
        ClosedVmValue, ClosedVmValueError, ConstantInfo, ConstantVal, ConstructorVal, Declaration,
        DefinitionSafety, DefinitionVal, DiagnosticChannel, DiagnosticColorPolicy, DiagnosticEpoch,
        DiagnosticFormat, DiagnosticFrontend, DiagnosticOrderPolicy, DiagnosticPathPolicy, Engine,
        EngineAdmissionError, EngineAdmissionLimits, EngineBvDecideError,
        EngineBvDecideInconclusive, EngineBvDecideLimits, EngineBvDecideOutcome,
        EngineExecutionError, EngineExecutionLimits, Environment, ExitClass, Expr, ExprNode,
        FlbcExecutionLimits, InductiveVal, IngressError, IngressResource, KVMap, Level, Literal,
        Name, NatDefinitionFrontendError, NatLit, OleanCheckError, OleanCheckLimits,
        OleanDeclarationError, OleanDecodeError, OleanDecodeLimits, OleanModuleImport,
        OleanModuleInput, OleanRebuildError, OleanRegionError, OleanWalkBudget, OpaqueVal, Outcome,
        ProjectionRefusal, ProjectionRequest, ProjectionSnapshot, ReadingCheck, RecursorRule,
        RecursorVal, ReducibilityHints, RejectClass, ScalarConstructorBinding, SourceCommandOutput,
        SourceModuleInput, TheoremVal, VmExecutionLimits, closed_vm_value, decode_olean_artifact,
        execute_flbc_artifact, execute_golem_with_options, fresh_generated_command_name,
        project_lsp_diagnostics, rebuild_olean_artifact, source_scalar_constructor_binding,
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

    /// The pin-worded message of an elaboration-time unknown name, if `error` is one (also
    /// through a batch command). `None` for every other refusal, K1's included.
    fn unknown_name_message(error: &EngineExecutionError) -> Option<String> {
        use fln_elab::source::SourceInferenceError;
        match error {
            EngineExecutionError::BatchCommand { error, .. } => unknown_name_message(error),
            EngineExecutionError::Frontend(super::DefinitionFrontendError::Elaborate(
                fln_elab::NatDefinitionElabError::Inference(
                    inference @ (SourceInferenceError::UnknownConstant(_)
                    | SourceInferenceError::UnknownMemberConstant(_)),
                ),
            )) => Some(inference.to_string()),
            _ => None,
        }
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
        framed_olean(constants, imports, super::OLEAN_ACCEPTED_VERSIONS[0])
    }

    fn framed_olean(
        constants: &[ConstantInfo],
        imports: &[OleanModuleImport],
        version: u8,
    ) -> Vec<u8> {
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
                version,
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

    fn mutual_olean_declarations() -> Vec<ConstantInfo> {
        let base = Name::from_components(["Fixture", "mutualBase"]);
        let left = Name::from_components(["Fixture", "mutualLeft"]);
        let right = Name::from_components(["Fixture", "mutualRight"]);
        let members = vec![left.clone(), right.clone()];
        vec![
            ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: right.clone(),
                    level_params: Vec::new(),
                    type_: Expr::const_(base.clone(), Vec::new()),
                },
                value: Expr::const_(left.clone(), Vec::new()),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Partial,
                all: members.clone(),
            }),
            ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: left.clone(),
                    level_params: Vec::new(),
                    type_: Expr::const_(base.clone(), Vec::new()),
                },
                value: Expr::const_(right, Vec::new()),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Partial,
                all: members,
            }),
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: base,
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::zero()),
                },
                is_unsafe: false,
            }),
        ]
    }

    fn enumeration_declarations(recursor_motive_binder: BinderInfo) -> Vec<ConstantInfo> {
        let color = Name::from_components(["Fixture", "Color"]);
        let red = Name::from_components(["Fixture", "Color", "red"]);
        let blue = Name::from_components(["Fixture", "Color", "blue"]);
        let recursor = Name::from_components(["Fixture", "Color", "rec"]);
        let u_name = Name::from_components(["u"]);
        let u = Level::param(u_name.clone());
        let color_expr = || Expr::const_(color.clone(), Vec::new());
        let red_expr = || Expr::const_(red.clone(), Vec::new());
        let blue_expr = || Expr::const_(blue.clone(), Vec::new());
        let bv = |index| Expr::bvar(index).expect("packs");
        let motive_type = pi(
            "t",
            BinderInfo::Default,
            color_expr(),
            Expr::sort(u.clone()),
        );
        let recursor_type = pi(
            "motive",
            recursor_motive_binder,
            motive_type.clone(),
            pi(
                "red",
                BinderInfo::Default,
                Expr::app(bv(0), red_expr()),
                pi(
                    "blue",
                    BinderInfo::Default,
                    Expr::app(bv(1), blue_expr()),
                    pi(
                        "t",
                        BinderInfo::Default,
                        color_expr(),
                        Expr::app(bv(3), bv(0)),
                    ),
                ),
            ),
        );
        let rule_rhs = |selected: u32| {
            Expr::lam(
                Name::from_components(["motive"]),
                motive_type.clone(),
                Expr::lam(
                    Name::from_components(["red"]),
                    Expr::app(bv(0), red_expr()),
                    Expr::lam(
                        Name::from_components(["blue"]),
                        Expr::app(bv(1), blue_expr()),
                        bv(selected),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            )
        };
        vec![
            ConstantInfo::Rec(RecursorVal {
                base: ConstantVal {
                    name: recursor,
                    level_params: vec![u_name],
                    type_: recursor_type,
                },
                all: vec![color.clone()],
                num_params: 0,
                num_indices: 0,
                num_motives: 1,
                num_minors: 2,
                rules: vec![
                    RecursorRule {
                        ctor: red.clone(),
                        nfields: 0,
                        rhs: rule_rhs(1),
                    },
                    RecursorRule {
                        ctor: blue.clone(),
                        nfields: 0,
                        rhs: rule_rhs(0),
                    },
                ],
                k: false,
                is_unsafe: false,
            }),
            ConstantInfo::Ctor(ConstructorVal {
                base: ConstantVal {
                    name: blue.clone(),
                    level_params: Vec::new(),
                    type_: color_expr(),
                },
                induct: color.clone(),
                cidx: 1,
                num_params: 0,
                num_fields: 0,
                is_unsafe: false,
            }),
            ConstantInfo::Induct(InductiveVal {
                base: ConstantVal {
                    name: color.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                num_params: 0,
                num_indices: 0,
                all: vec![color.clone()],
                ctors: vec![red.clone(), blue],
                num_nested: 0,
                is_rec: false,
                is_unsafe: false,
                is_reflexive: false,
            }),
            ConstantInfo::Ctor(ConstructorVal {
                base: ConstantVal {
                    name: red,
                    level_params: Vec::new(),
                    type_: color_expr(),
                },
                induct: color,
                cidx: 0,
                num_params: 0,
                num_fields: 0,
                is_unsafe: false,
            }),
        ]
    }

    fn dependent_field_inductive_declarations() -> Vec<ConstantInfo> {
        let witness = Name::from_components(["Fixture", "Witness"]);
        let make = Name::from_components(["Fixture", "Witness", "mk"]);
        let recursor = Name::from_components(["Fixture", "Witness", "rec"]);
        let u_name = Name::from_components(["u"]);
        let u = Level::param(u_name.clone());
        let witness_expr = || Expr::const_(witness.clone(), Vec::new());
        let make_expr = || Expr::const_(make.clone(), Vec::new());
        let bv = |index| Expr::bvar(index).expect("packs");
        let constructor_type = pi(
            "proposition",
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            pi("proof", BinderInfo::Default, bv(0), witness_expr()),
        );
        let motive_type = pi(
            "t",
            BinderInfo::Default,
            witness_expr(),
            Expr::sort(u.clone()),
        );
        let minor_type = pi(
            "proposition",
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            pi(
                "proof",
                BinderInfo::Default,
                bv(0),
                Expr::app(bv(2), Expr::app(Expr::app(make_expr(), bv(1)), bv(0))),
            ),
        );
        let recursor_type = pi(
            "motive",
            BinderInfo::Implicit,
            motive_type.clone(),
            pi(
                "mk",
                BinderInfo::Default,
                minor_type.clone(),
                pi(
                    "t",
                    BinderInfo::Default,
                    witness_expr(),
                    Expr::app(bv(2), bv(0)),
                ),
            ),
        );
        let rule_rhs = Expr::lam(
            Name::from_components(["motive"]),
            motive_type,
            Expr::lam(
                Name::from_components(["mk"]),
                minor_type,
                Expr::lam(
                    Name::from_components(["proposition"]),
                    Expr::sort(Level::zero()),
                    Expr::lam(
                        Name::from_components(["proof"]),
                        bv(0),
                        Expr::app(Expr::app(bv(2), bv(1)), bv(0)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        vec![
            ConstantInfo::Rec(RecursorVal {
                base: ConstantVal {
                    name: recursor,
                    level_params: vec![u_name],
                    type_: recursor_type,
                },
                all: vec![witness.clone()],
                num_params: 0,
                num_indices: 0,
                num_motives: 1,
                num_minors: 1,
                rules: vec![RecursorRule {
                    ctor: make.clone(),
                    nfields: 2,
                    rhs: rule_rhs,
                }],
                k: false,
                is_unsafe: false,
            }),
            ConstantInfo::Ctor(ConstructorVal {
                base: ConstantVal {
                    name: make.clone(),
                    level_params: Vec::new(),
                    type_: constructor_type,
                },
                induct: witness.clone(),
                cidx: 0,
                num_params: 0,
                num_fields: 2,
                is_unsafe: false,
            }),
            ConstantInfo::Induct(InductiveVal {
                base: ConstantVal {
                    name: witness.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                num_params: 0,
                num_indices: 0,
                all: vec![witness],
                ctors: vec![make],
                num_nested: 0,
                is_rec: false,
                is_unsafe: false,
                is_reflexive: false,
            }),
        ]
    }

    fn arrow(domain: Expr, codomain: Expr) -> Expr {
        Expr::forall_e(
            Name::from_components(["a"]),
            domain,
            codomain,
            BinderInfo::Default,
        )
    }

    fn pi(name: &str, info: BinderInfo, type_: Expr, body: Expr) -> Expr {
        Expr::forall_e(Name::from_components([name]), type_, body, info)
    }

    fn equality_environment() -> Environment {
        let eq = Name::from_components(["Eq"]);
        let refl = Name::from_components(["Eq", "refl"]);
        let u_name = Name::from_components(["uEq"]);
        let u = Level::param(u_name.clone());
        let eq_type = pi(
            "α",
            BinderInfo::Implicit,
            Expr::sort(u.clone()),
            arrow(
                Expr::bvar(0).expect("packs"),
                arrow(Expr::bvar(1).expect("packs"), Expr::sort(Level::zero())),
            ),
        );
        let refl_type = pi(
            "α",
            BinderInfo::Implicit,
            Expr::sort(u.clone()),
            pi(
                "a",
                BinderInfo::Default,
                Expr::bvar(0).expect("packs"),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(eq.clone(), vec![u]),
                            Expr::bvar(1).expect("packs"),
                        ),
                        Expr::bvar(0).expect("packs"),
                    ),
                    Expr::bvar(0).expect("packs"),
                ),
            ),
        );
        let inductive = ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: eq.clone(),
                level_params: vec![u_name.clone()],
                type_: eq_type,
            },
            num_params: 1,
            num_indices: 0,
            all: vec![eq.clone()],
            ctors: vec![refl.clone()],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: true,
        });
        let constructor = ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: refl,
                level_params: vec![u_name],
                type_: refl_type,
            },
            induct: eq,
            cidx: 0,
            num_params: 1,
            num_fields: 0,
            is_unsafe: false,
        });
        Environment::new()
            .add_decl(inductive)
            .expect("test equality type enters the imported base")
            .add_decl(constructor)
            .expect("test equality constructor enters the imported base")
    }

    fn quotient_declarations() -> Vec<ConstantInfo> {
        let quot = Name::from_components(["Quot"]);
        let u_name = Name::from_components(["u"]);
        let v_name = Name::from_components(["v"]);
        let u = Level::param(u_name.clone());
        let v = Level::param(v_name.clone());
        let prop = || Expr::sort(Level::zero());
        let bv = |index| Expr::bvar(index).expect("packs");
        let quot_type = pi(
            "α",
            BinderInfo::Implicit,
            Expr::sort(u.clone()),
            arrow(arrow(bv(0), arrow(bv(1), prop())), Expr::sort(u.clone())),
        );
        let quot_app = |alpha: Expr, relation: Expr| {
            Expr::app(
                Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), alpha),
                relation,
            )
        };
        let quot_mk_type = pi(
            "α",
            BinderInfo::Implicit,
            Expr::sort(u.clone()),
            pi(
                "r",
                BinderInfo::Default,
                arrow(bv(0), arrow(bv(1), prop())),
                pi("a", BinderInfo::Default, bv(1), quot_app(bv(2), bv(1))),
            ),
        );
        let sanity = pi(
            "a",
            BinderInfo::Default,
            bv(3),
            pi(
                "b",
                BinderInfo::Default,
                bv(4),
                arrow(
                    Expr::app(Expr::app(bv(4), bv(1)), bv(0)),
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_components(["Eq"]), vec![v.clone()]),
                                bv(4),
                            ),
                            Expr::app(bv(3), bv(2)),
                        ),
                        Expr::app(bv(3), bv(1)),
                    ),
                ),
            ),
        );
        let quot_lift_type = pi(
            "α",
            BinderInfo::Implicit,
            Expr::sort(u.clone()),
            pi(
                "r",
                BinderInfo::Implicit,
                arrow(bv(0), arrow(bv(1), prop())),
                pi(
                    "β",
                    BinderInfo::Implicit,
                    Expr::sort(v.clone()),
                    pi(
                        "f",
                        BinderInfo::Default,
                        arrow(bv(2), bv(1)),
                        arrow(sanity, arrow(quot_app(bv(4), bv(3)), bv(3))),
                    ),
                ),
            ),
        );
        let quot_mk = Name::from_components(["Quot", "mk"]);
        let quot_ind_type = pi(
            "α",
            BinderInfo::Implicit,
            Expr::sort(u.clone()),
            pi(
                "r",
                BinderInfo::Implicit,
                arrow(bv(0), arrow(bv(1), prop())),
                pi(
                    "β",
                    BinderInfo::Implicit,
                    arrow(quot_app(bv(1), bv(0)), prop()),
                    pi(
                        "mk",
                        BinderInfo::Default,
                        pi(
                            "a",
                            BinderInfo::Default,
                            bv(2),
                            Expr::app(
                                bv(1),
                                Expr::app(
                                    Expr::app(
                                        Expr::app(Expr::const_(quot_mk, vec![u.clone()]), bv(3)),
                                        bv(2),
                                    ),
                                    bv(0),
                                ),
                            ),
                        ),
                        pi(
                            "q",
                            BinderInfo::Default,
                            quot_app(bv(3), bv(2)),
                            Expr::app(bv(2), bv(0)),
                        ),
                    ),
                ),
            ),
        );
        vec![
            ConstantInfo::Quot(QuotVal {
                base: ConstantVal {
                    name: quot.clone(),
                    level_params: vec![u_name.clone()],
                    type_: quot_type,
                },
                kind: QuotKind::Type,
            }),
            ConstantInfo::Quot(QuotVal {
                base: ConstantVal {
                    name: Name::from_components(["Quot", "mk"]),
                    level_params: vec![u_name.clone()],
                    type_: quot_mk_type,
                },
                kind: QuotKind::Ctor,
            }),
            ConstantInfo::Quot(QuotVal {
                base: ConstantVal {
                    name: Name::from_components(["Quot", "lift"]),
                    level_params: vec![u_name.clone(), v_name],
                    type_: quot_lift_type,
                },
                kind: QuotKind::Lift,
            }),
            ConstantInfo::Quot(QuotVal {
                base: ConstantVal {
                    name: Name::from_components(["Quot", "ind"]),
                    level_params: vec![u_name],
                    type_: quot_ind_type,
                },
                kind: QuotKind::Ind,
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

    /// `Fixture.P : Prop` and `Fixture.self : ∀ (h : P), P := fun h => h`. The binder's
    /// style plays no part in typing, so a reading that flips it is still a declaration
    /// both seats accept: only comparing the two readings can see the flip (bead
    /// `franken_lean-z8j.1.14`).
    fn binder_declarations(style: BinderInfo) -> Vec<ConstantInfo> {
        let proposition = Name::from_components(["Fixture", "P"]);
        let theorem = Name::from_components(["Fixture", "self"]);
        let p = Expr::const_(proposition.clone(), Vec::new());
        let h = Name::from_components(["h"]);
        vec![
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: proposition,
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::zero()),
                },
                is_unsafe: false,
            }),
            ConstantInfo::Thm(TheoremVal {
                base: ConstantVal {
                    name: theorem.clone(),
                    level_params: Vec::new(),
                    type_: Expr::forall_e(h.clone(), p.clone(), p.clone(), style),
                },
                value: Expr::lam(
                    h,
                    p,
                    Expr::bvar(0).expect("index 0 is in range"),
                    BinderInfo::Default,
                ),
                all: vec![theorem],
            }),
        ]
    }

    fn council_halt(error: &OleanCheckError) -> String {
        let leaf = match error {
            OleanCheckError::Admission(EngineAdmissionError::BatchDeclaration {
                error, ..
            }) => error.as_ref(),
            OleanCheckError::Admission(error) => error,
            other => panic!("expected a council halt, got {other:?}"),
        };
        match leaf {
            EngineAdmissionError::CouncilHalted { summary } => summary.clone(),
            other => panic!("expected a council halt, got {other:?}"),
        }
    }

    #[test]
    fn the_checker_reads_every_fixture_as_the_primary_decodes_it() {
        let budget = super::CheckerExecutionLimits::default().decode;
        let mut artifacts: Vec<(String, Vec<u8>)> = [
            "Init.BinderNameHint.olean",
            "Init.SizeOfLemmas.olean",
            "Init.olean",
        ]
        .into_iter()
        .map(|name| (name.to_owned(), olean_fixture(name)))
        .collect();
        for (name, constants) in [
            ("standalone", standalone_declarations()),
            ("mutual", mutual_olean_declarations()),
            ("binder", binder_declarations(BinderInfo::InstImplicit)),
        ] {
            artifacts.push((name.to_owned(), standalone_olean(&constants)));
            for &version in super::OLEAN_ACCEPTED_VERSIONS {
                artifacts.push((
                    format!("{name} v{version}"),
                    framed_olean(&constants, &[], version),
                ));
            }
        }
        let mut compared = 0;
        for (name, bytes) in &artifacts {
            let decoded = decode_olean_artifact(bytes, OleanDecodeLimits::new(bytes.len()))
                .unwrap_or_else(|error| panic!("{name}: the primary decodes: {error}"));
            let readings = super::ArtifactReadings::new(&decoded.independent)
                .unwrap_or_else(|reason| panic!("{name}: {reason}"));
            assert_eq!(readings.0.len(), decoded.constants.len(), "{name}");
            for info in &decoded.constants {
                if let Some(
                    super::ReadingObjection::Differs(detail)
                    | super::ReadingObjection::Unprojected(detail),
                ) = readings.objection(info, budget)
                {
                    panic!("{name}: {detail}");
                }
                compared += 1;
            }
        }
        assert!(
            compared > 0,
            "a comparison over no declaration proves nothing"
        );
    }

    /// The decoder differential of bead `franken_lean-z8j.1.14`: every declaration of every
    /// module under the roots, decoded by `fln-olean` (what K1 judges) and read by the
    /// checker from the bytes, compared exactly as the council's checker seat compares them.
    /// Roots: `FLN_READING_DIFF_ROOTS` (`:`-separated `lib/lean` directories), else the
    /// pinned toolchain's. Prints a receipt; refuses on any difference or unread module.
    #[test]
    #[ignore = "walks a whole library; run in release with --ignored"]
    fn every_declaration_under_the_roots_reads_the_same_to_both_decoders() {
        use fln_hash::domain::{Domain, DomainHasher};
        use std::path::{Path, PathBuf};

        fn oleans(dir: &Path, out: &mut Vec<PathBuf>) {
            let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
                .unwrap_or_else(|error| panic!("cannot list {}: {error}", dir.display()))
                .map(|entry| entry.expect("a directory entry").path())
                .collect();
            entries.sort();
            for path in entries {
                if path.is_dir() {
                    oleans(&path, out);
                } else if path
                    .extension()
                    .is_some_and(|extension| extension == "olean")
                {
                    out.push(path);
                }
            }
        }

        let roots: Vec<PathBuf> = match std::env::var("FLN_READING_DIFF_ROOTS") {
            Ok(roots) => roots.split(':').map(PathBuf::from).collect(),
            Err(_) => vec![
                PathBuf::from(std::env::var("HOME").expect("HOME"))
                    .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean"),
            ],
        };
        let mut modules = Vec::new();
        for root in &roots {
            oleans(root, &mut modules);
        }
        assert!(!modules.is_empty(), "no .olean under {roots:?}");

        let budget = super::CheckerExecutionLimits::default().decode;
        let started = std::time::Instant::now();
        let mut reading_time = std::time::Duration::ZERO;
        let mut decode_time = std::time::Duration::ZERO;
        let mut receipt = DomainHasher::new(Domain::CacheKey);
        receipt.update(b"fln.reading-differential/1\0");
        let (mut parts, mut constants, mut agree) = (0_usize, 0_usize, 0_usize);
        let mut refused: Vec<String> = Vec::new();
        for path in &modules {
            let exported = std::fs::read(path).expect("readable part");
            let server_path = path.with_extension("olean.server");
            let private_path = path.with_extension("olean.private");
            let chain: Vec<Vec<u8>> = if server_path.is_file() && private_path.is_file() {
                vec![
                    exported,
                    std::fs::read(&server_path).expect("readable part"),
                    std::fs::read(&private_path).expect("readable part"),
                ]
            } else {
                vec![exported]
            };
            parts += chain.len();
            let total: usize = chain.iter().map(Vec::len).sum();
            let limits = OleanDecodeLimits::new(total);
            let timed = std::time::Instant::now();
            let decoded = match chain.as_slice() {
                [only] => decode_olean_artifact(only, limits),
                [exported, server, private] => {
                    super::decode_olean_module_artifacts(exported, server, private, limits)
                }
                _ => unreachable!("one part or three"),
            }
            .unwrap_or_else(|error| panic!("{}: the primary decodes: {error}", path.display()));
            decode_time += timed.elapsed();
            let slices: Vec<&[u8]> = chain.iter().map(Vec::as_slice).collect();
            let timed = std::time::Instant::now();
            let again = super::independent_reading(&slices, limits);
            reading_time += timed.elapsed();
            assert_eq!(
                again, decoded.independent,
                "the checker's reading is deterministic"
            );

            let label = path.display().to_string();
            receipt.update(&(label.len() as u64).to_le_bytes());
            receipt.update(label.as_bytes());
            let readings = match super::ArtifactReadings::new(&decoded.independent) {
                Ok(readings) => readings,
                Err(reason) => {
                    refused.push(format!("{label}: {reason}"));
                    continue;
                }
            };
            if let super::IndependentReading::Read(entries) = &decoded.independent {
                for (_, digest) in entries {
                    receipt.update(&digest.0);
                }
            }
            for info in &decoded.constants {
                constants += 1;
                match readings.objection(info, budget) {
                    None => agree += 1,
                    Some(
                        super::ReadingObjection::Differs(detail)
                        | super::ReadingObjection::Unprojected(detail),
                    ) => refused.push(format!("{label}: {detail}")),
                }
            }
        }
        println!(
            "reading-differential: roots {roots:?}; modules {}; parts {parts}; constants \
             {constants}; identical {agree}; refused {}; reading-set digest {}; elapsed {:.1}s; \
             decode with the reading {:.1}s, the checker's reading alone {:.1}s",
            modules.len(),
            refused.len(),
            receipt
                .finalize()
                .0
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>(),
            started.elapsed().as_secs_f64(),
            decode_time.as_secs_f64(),
            reading_time.as_secs_f64(),
        );
        assert!(
            refused.is_empty(),
            "{} declaration(s) or module(s) read differently:\n  {}",
            refused.len(),
            refused
                .iter()
                .take(20)
                .cloned()
                .collect::<Vec<_>>()
                .join("\n  ")
        );
        assert_eq!(agree, constants);
    }

    #[test]
    fn a_planted_primary_misreading_of_a_binder_is_a_council_disagreement() {
        let written = binder_declarations(BinderInfo::Default);
        let bytes = standalone_olean(&written);
        let limits = OleanCheckLimits::new(bytes.len(), test_budget());
        let options = KVMap::new();
        let engine = Engine::from_environment(Environment::new());

        // Control, end to end from the bytes: the two readings agree and the council
        // admits. A defect in either decoder's binder reading fails here.
        let checked = engine.check_olean_artifact(&bytes, &options, limits);
        let Ok(Outcome::Complete(admitted)) = checked else {
            panic!("the faithful artifact must be admitted: {checked:?}");
        };
        let decoded = admitted.decoded.clone();
        assert_eq!(
            decoded.constants, written,
            "the primary reads what was written"
        );

        // The planted defect: the primary decodes the binder as implicit.
        let misread = binder_declarations(BinderInfo::Implicit);
        let mut planted = decoded.clone();
        planted.constants = misread.clone();
        let refusal = engine
            .check_decoded_olean(planted, &options, limits)
            .expect_err("a misread declaration must not be admitted");
        let summary = council_halt(&refusal);
        assert!(
            summary.contains("fln-checker's own reading") && summary.contains("Fixture.self"),
            "the halt must be the checker's reading objection: {summary}"
        );

        // Where nothing caught it before: judged on the primary's reading alone, as both
        // seats were, the misread declaration is accepted by K1 and the checker alike.
        let declarations: Vec<Declaration> = misread
            .iter()
            .map(|info| super::checked_olean_declaration(info).expect("a plain declaration"))
            .collect();
        assert!(
            matches!(
                engine.admit_declarations_unrooted(
                    &declarations,
                    &options,
                    limits.admission,
                    ReadingCheck::Unread,
                ),
                Ok(Outcome::Complete(_))
            ),
            "without the comparison both seats agree on the misreading"
        );

        // The other direction: the checker's reading is the one that differs.
        let mut checker_misread = decoded.clone();
        checker_misread.independent =
            super::independent_reading(&[&standalone_olean(&misread)], limits.decode);
        let refusal = engine
            .check_decoded_olean(checker_misread, &options, limits)
            .expect_err("readings that differ in either direction are not admitted");
        assert!(council_halt(&refusal).contains("Fixture.self"));

        // An artifact the checker could not read leaves it without an answer.
        let mut unread = decoded.clone();
        unread.independent = super::IndependentReading::Unread("planted".to_owned());
        assert!(matches!(
            engine.check_decoded_olean(unread, &options, limits),
            Ok(Outcome::Inconclusive(_))
        ));

        // A declaration no council reviews. Checked again, the module's constants are all
        // already present; a primary that misread a different binder as the admitted one
        // would report the module checked, and the checker's reading refuses it.
        let true_repeat = standalone_olean(&binder_declarations(BinderInfo::StrictImplicit));
        let mut present = decode_olean_artifact(&true_repeat, limits.decode).expect("decodes");
        present.constants = written.clone();
        match admitted
            .engine
            .check_decoded_olean(present, &options, limits)
        {
            Err(OleanCheckError::IndependentReadingDiffers { name, .. }) => {
                assert_eq!(name.to_display_string(), "Fixture.self");
            }
            other => panic!("an unreviewed misreading must be refused: {other:?}"),
        }
        assert!(matches!(
            admitted
                .engine
                .check_decoded_olean(decoded.clone(), &options, limits),
            Ok(Outcome::Complete(_))
        ));

        // A subsumed theorem repeat is renamed before its council; its reading is
        // compared as the artifact states it. The true repeat (strict implicit) rechecks;
        // the same bytes misread as implicit halt the repeat's council.
        let repeat = decode_olean_artifact(&true_repeat, limits.decode).expect("decodes");
        assert!(matches!(
            admitted
                .engine
                .check_decoded_olean(repeat.clone(), &options, limits),
            Ok(Outcome::Complete(_))
        ));
        let mut misread_repeat = repeat;
        misread_repeat.constants = misread;
        let refusal = admitted
            .engine
            .check_decoded_olean(misread_repeat, &options, limits)
            .expect_err("a misread repeat must not be counted as checked");
        assert!(council_halt(&refusal).contains("Fixture.self"));
    }

    #[test]
    fn standalone_olean_check_reconstructs_non_safe_mutual_definition_units() {
        let constants = mutual_olean_declarations();
        let bytes = standalone_olean(&constants);
        let engine = Engine::from_environment(Environment::new());
        let outcome = engine
            .check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            )
            .expect("the complete non-safe mutual envelope reaches both checkers");
        let Outcome::Complete(checked) = outcome else {
            panic!("the mutual fixture must complete: {outcome:?}");
        };

        let names: Vec<String> = checked
            .declarations
            .iter()
            .map(|declaration| declaration.name.to_display_string())
            .collect();
        assert_eq!(
            names,
            [
                "Fixture.mutualBase",
                "Fixture.mutualLeft",
                "Fixture.mutualRight"
            ]
        );
        assert_eq!(checked.engine.environment().len(), 3);
        assert_eq!(checked.decoded.constants, constants);
        assert_eq!(
            checked.declarations[0].checker.ground,
            CheckerAdmissionGround::AxiomPreamble
        );
        assert_eq!(
            checked.declarations[2].checker, checked.declarations[1].checker,
            "one mutual authority transition reports its agreement on every member"
        );
        assert_eq!(
            checked.declarations[1].checker.ground,
            CheckerAdmissionGround::PartialQuarantine
        );
    }

    /// Bead fln-r0yh: Mathlib's `compile_inductive` admits its compiled
    /// recursors as one `mutualDefnDecl` whose members carry the inductive's
    /// `all` (`{ rv with .. }`), never their own names. Such definitions are
    /// grouped by that `all` and safety: a mutually recursive pair and a
    /// self-recursive singleton each check as the block they were admitted as,
    /// and definitions of different safety are never merged.
    #[test]
    fn standalone_olean_check_groups_definitions_whose_all_names_a_recursor_block() {
        let recursor_block = vec![Name::from_components(["Fixture", "Tree"])];
        let mut pair = mutual_olean_declarations();
        for info in &mut pair[..2] {
            let ConstantInfo::Defn(definition) = info else {
                panic!("the first two fixture rows are mutual definitions")
            };
            definition.all = recursor_block.clone();
        }
        let base = Name::from_components(["Fixture", "mutualBase"]);
        let lone = Name::from_components(["Fixture", "compiledRec"]);
        pair.push(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: lone.clone(),
                level_params: Vec::new(),
                type_: Expr::const_(base.clone(), Vec::new()),
            },
            value: Expr::const_(lone.clone(), Vec::new()),
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Partial,
            all: vec![Name::from_components(["Fixture", "List"])],
        }));
        let bytes = standalone_olean(&pair);
        let outcome = Engine::from_environment(Environment::new())
            .check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            )
            .expect("definitions carrying their recursor block's `all` reach both checkers");
        let Outcome::Complete(checked) = outcome else {
            panic!("the compiled-recursor fixture must complete: {outcome:?}");
        };
        assert_eq!(checked.engine.environment().len(), 4);
        assert_eq!(checked.decoded.constants, pair);
        let checker_of = |name: &str| {
            checked
                .declarations
                .iter()
                .find(|declaration| declaration.name.to_display_string() == name)
                .map(|declaration| declaration.checker)
                .expect("every row is reported")
        };
        assert_eq!(
            checker_of("Fixture.mutualLeft"),
            checker_of("Fixture.mutualRight"),
            "the mutually recursive pair is one authority transition"
        );
        assert_eq!(
            checker_of("Fixture.compiledRec").ground,
            CheckerAdmissionGround::PartialQuarantine
        );

        // A different `all` is a different admission: a pair referring to each
        // other across two `all` lists is a dependency cycle between two units,
        // refused as unplannable rather than admitted as a block nobody built.
        let mut crossed = pair.clone();
        let ConstantInfo::Defn(left) = &mut crossed[1] else {
            panic!("the second fixture row is the left mutual definition")
        };
        left.all = vec![Name::from_components(["Fixture", "Other"])];
        let bytes = standalone_olean(&crossed);
        assert!(
            matches!(
                Engine::from_environment(Environment::new()).check_olean_artifact(
                    &bytes,
                    &KVMap::new(),
                    OleanCheckLimits::new(bytes.len(), test_budget()),
                ),
                Err(OleanCheckError::DependencyCycle { .. })
            ),
            "definitions with different `all` lists are never merged into one block"
        );

        // A definition whose `all` names itself keeps the ordinary envelope, even
        // when another definition's foreign `all` names it too: the two are not
        // one block unless their own records say so.
        let mut self_named = pair.clone();
        let left_name = Name::from_components(["Fixture", "mutualLeft"]);
        for info in &mut self_named[..2] {
            let ConstantInfo::Defn(definition) = info else {
                panic!("the first two fixture rows are mutual definitions")
            };
            definition.all = vec![left_name.clone()];
        }
        let bytes = standalone_olean(&self_named);
        assert!(
            matches!(
                Engine::from_environment(Environment::new()).check_olean_artifact(
                    &bytes,
                    &KVMap::new(),
                    OleanCheckLimits::new(bytes.len(), test_budget()),
                ),
                Err(OleanCheckError::DependencyCycle { .. })
            ),
            "a self-named definition is not absorbed into a foreign group"
        );

        // Different safety under one `all` is not one admission (the pin's
        // `add_mutual` refuses a block that mixes safeties): given closed
        // bodies, the partial and the unsafe definition each check alone.
        let witness = Name::from_components(["Fixture", "baseWitness"]);
        let mut mixed = pair.clone();
        for (position, info) in mixed[..2].iter_mut().enumerate() {
            let ConstantInfo::Defn(definition) = info else {
                panic!("the first two fixture rows are mutual definitions")
            };
            definition.value = Expr::const_(witness.clone(), Vec::new());
            if position == 1 {
                definition.safety = DefinitionSafety::Unsafe;
            }
        }
        mixed.push(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: witness,
                level_params: Vec::new(),
                type_: Expr::const_(base, Vec::new()),
            },
            is_unsafe: false,
        }));
        let bytes = standalone_olean(&mixed);
        let outcome = Engine::from_environment(Environment::new())
            .check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            )
            .expect("a partial and an unsafe definition sharing one `all` are two units");
        assert!(
            matches!(outcome, Outcome::Complete(_)),
            "mixed safety must not be merged into one refused block: {outcome:?}"
        );
    }

    #[test]
    fn standalone_olean_check_retains_acyclic_multi_name_body_metadata() {
        let proposition = Name::from_components(["Fixture", "Metadata", "P"]);
        let witness = Name::from_components(["Fixture", "Metadata", "p"]);
        let definition_left = Name::from_components(["Fixture", "Metadata", "defLeft"]);
        let definition_right = Name::from_components(["Fixture", "Metadata", "defRight"]);
        let theorem_left = Name::from_components(["Fixture", "Metadata", "thmLeft"]);
        let theorem_right = Name::from_components(["Fixture", "Metadata", "thmRight"]);
        let opaque_left = Name::from_components(["Fixture", "Metadata", "opaqueLeft"]);
        let opaque_right = Name::from_components(["Fixture", "Metadata", "opaqueRight"]);
        let definition_members = vec![definition_left.clone(), definition_right.clone()];
        let theorem_members = vec![theorem_left.clone(), theorem_right.clone()];
        let opaque_members = vec![opaque_left.clone(), opaque_right.clone()];
        let proposition_expr = Expr::const_(proposition.clone(), Vec::new());
        let witness_expr = Expr::const_(witness.clone(), Vec::new());
        let constants = vec![
            ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: definition_right.clone(),
                    level_params: Vec::new(),
                    type_: proposition_expr.clone(),
                },
                value: Expr::const_(definition_left.clone(), Vec::new()),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: definition_members.clone(),
            }),
            ConstantInfo::Thm(TheoremVal {
                base: ConstantVal {
                    name: theorem_right.clone(),
                    level_params: Vec::new(),
                    type_: proposition_expr.clone(),
                },
                value: witness_expr.clone(),
                all: theorem_members.clone(),
            }),
            ConstantInfo::Opaque(OpaqueVal {
                base: ConstantVal {
                    name: opaque_right.clone(),
                    level_params: Vec::new(),
                    type_: proposition_expr.clone(),
                },
                value: witness_expr.clone(),
                is_unsafe: false,
                all: opaque_members.clone(),
            }),
            ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: definition_left.clone(),
                    level_params: Vec::new(),
                    type_: proposition_expr.clone(),
                },
                value: witness_expr.clone(),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: definition_members.clone(),
            }),
            ConstantInfo::Thm(TheoremVal {
                base: ConstantVal {
                    name: theorem_left.clone(),
                    level_params: Vec::new(),
                    type_: proposition_expr.clone(),
                },
                value: witness_expr.clone(),
                all: theorem_members.clone(),
            }),
            ConstantInfo::Opaque(OpaqueVal {
                base: ConstantVal {
                    name: opaque_left.clone(),
                    level_params: Vec::new(),
                    type_: proposition_expr.clone(),
                },
                value: witness_expr,
                is_unsafe: false,
                all: opaque_members.clone(),
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
        ];
        let bytes = standalone_olean(&constants);
        let outcome = Engine::from_environment(Environment::new())
            .check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            )
            .expect("acyclic multi-name body rows reach both checkers");
        let Outcome::Complete(checked) = outcome else {
            panic!("the metadata fixture must complete: {outcome:?}");
        };
        assert_eq!(checked.declarations.len(), constants.len());
        assert_eq!(checked.engine.environment().len(), constants.len());
        assert!(checked.declarations.iter().all(|declaration| {
            declaration.checker.schema == fln_checker::admit::ADMISSION_SCHEMA
        }));

        let environment = checked.engine.environment();
        assert!(matches!(
            environment.find(&definition_left),
            Some(ConstantInfo::Defn(value)) if value.all == definition_members
        ));
        assert!(matches!(
            environment.find(&definition_right),
            Some(ConstantInfo::Defn(value)) if value.all == definition_members
        ));
        assert!(matches!(
            environment.find(&theorem_left),
            Some(ConstantInfo::Thm(value)) if value.all == theorem_members
        ));
        assert!(matches!(
            environment.find(&theorem_right),
            Some(ConstantInfo::Thm(value)) if value.all == theorem_members
        ));
        assert!(matches!(
            environment.find(&opaque_left),
            Some(ConstantInfo::Opaque(value)) if value.all == opaque_members
        ));
        assert!(matches!(
            environment.find(&opaque_right),
            Some(ConstantInfo::Opaque(value)) if value.all == opaque_members
        ));
    }

    #[test]
    fn standalone_olean_check_refuses_malformed_or_rejected_mutual_units_atomically() {
        let engine = Engine::from_environment(Environment::new());
        let limits_for = |bytes: &[u8]| OleanCheckLimits::new(bytes.len(), test_budget());

        let mut mismatched = mutual_olean_declarations();
        let ConstantInfo::Defn(right) = &mut mismatched[0] else {
            panic!("the fixture's first row is the right mutual definition")
        };
        right.all.reverse();
        let bytes = standalone_olean(&mismatched);
        assert!(matches!(
            engine.check_olean_artifact(&bytes, &KVMap::new(), limits_for(&bytes)),
            Err(OleanCheckError::MutualEnvelopeUnsupported { ref name, .. })
                if name == &Name::from_components(["Fixture", "mutualRight"])
        ));

        let mut missing = mutual_olean_declarations();
        missing.remove(1);
        let bytes = standalone_olean(&missing);
        assert!(matches!(
            engine.check_olean_artifact(&bytes, &KVMap::new(), limits_for(&bytes)),
            Err(OleanCheckError::MutualEnvelopeUnsupported { .. })
        ));

        let mut mixed = mutual_olean_declarations();
        let left = Name::from_components(["Fixture", "mutualLeft"]);
        mixed[1] = ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: left,
                level_params: Vec::new(),
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        });
        let bytes = standalone_olean(&mixed);
        assert!(matches!(
            engine.check_olean_artifact(&bytes, &KVMap::new(), limits_for(&bytes)),
            Err(OleanCheckError::MutualEnvelopeUnsupported { .. })
        ));

        let mut duplicate = mutual_olean_declarations();
        let ConstantInfo::Defn(right) = &mut duplicate[0] else {
            panic!("the fixture's first row is the right mutual definition")
        };
        right.all[1] = right.all[0].clone();
        let bytes = standalone_olean(&duplicate);
        assert!(matches!(
            engine.check_olean_artifact(&bytes, &KVMap::new(), limits_for(&bytes)),
            Err(OleanCheckError::MutualEnvelopeUnsupported { .. })
        ));

        let mut safe = mutual_olean_declarations();
        for info in &mut safe[..2] {
            let ConstantInfo::Defn(definition) = info else {
                panic!("the first two fixture rows are mutual definitions")
            };
            definition.safety = DefinitionSafety::Safe;
        }
        let bytes = standalone_olean(&safe);
        assert!(matches!(
            engine.check_olean_artifact(&bytes, &KVMap::new(), limits_for(&bytes)),
            Err(OleanCheckError::DependencyCycle { declarations })
                if declarations.len() == 2
                    && declarations.contains(&Name::from_components(["Fixture", "mutualLeft"]))
                    && declarations.contains(&Name::from_components(["Fixture", "mutualRight"]))
        ));

        let bounded = mutual_olean_declarations();
        let bytes = standalone_olean(&bounded);
        let mut limits = limits_for(&bytes);
        limits.max_dependency_presentations = 0;
        assert!(matches!(
            engine.check_olean_artifact(&bytes, &KVMap::new(), limits),
            Err(OleanCheckError::DependencyPresentationLimit {
                observed: 1,
                limit: 0
            })
        ));

        let cycle_left = Name::from_components(["Fixture", "cycleLeft"]);
        let cycle_right = Name::from_components(["Fixture", "cycleRight"]);
        let unbound_cycle = [
            ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: cycle_left.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::zero()),
                },
                value: Expr::const_(cycle_right.clone(), Vec::new()),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Partial,
                all: vec![cycle_left.clone()],
            }),
            ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: cycle_right.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::zero()),
                },
                value: Expr::const_(cycle_left.clone(), Vec::new()),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Partial,
                all: vec![cycle_right.clone()],
            }),
        ];
        let bytes = standalone_olean(&unbound_cycle);
        assert!(matches!(
            engine.check_olean_artifact(&bytes, &KVMap::new(), limits_for(&bytes)),
            Err(OleanCheckError::DependencyCycle { declarations })
                if declarations == vec![cycle_left, cycle_right]
        ));

        let mut rejected = mutual_olean_declarations();
        let ConstantInfo::Defn(right) = &mut rejected[0] else {
            panic!("the fixture's first row is the right mutual definition")
        };
        right.value = Expr::sort(Level::zero());
        let bytes = standalone_olean(&rejected);
        assert!(matches!(
            engine.check_olean_artifact(&bytes, &KVMap::new(), limits_for(&bytes)),
            Err(OleanCheckError::Admission(
                EngineAdmissionError::BatchDeclaration { index: 1, .. }
            ))
        ));
        assert!(engine.environment().is_empty());
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
    fn standalone_olean_check_refuses_unresolved_imports_and_incomplete_units() {
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
            Err(OleanCheckError::QuotientEnvelopeUnsupported { ref names })
                if names == &vec![quotient_name]
        ));
    }

    #[test]
    fn standalone_olean_check_reconstructs_the_quotient_authority_unit() {
        let mut constants = quotient_declarations();
        constants.rotate_left(2);
        let bytes = standalone_olean(&constants);
        let engine = Engine::from_environment(equality_environment());
        let checked = engine
            .check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            )
            .expect("the fixed quotient envelope is reconstructible")
            .into_complete()
            .expect("both checkers complete the fixed quotient judgment");

        assert_eq!(checked.declarations.len(), 4);
        assert!(
            checked
                .declarations
                .iter()
                .all(|declaration| declaration.checker.ground
                    == CheckerAdmissionGround::QuotientPrimitiveChecked)
        );
        for name in [
            Name::from_components(["Quot"]),
            Name::from_components(["Quot", "mk"]),
            Name::from_components(["Quot", "lift"]),
            Name::from_components(["Quot", "ind"]),
        ] {
            assert!(checked.engine.environment().contains(&name));
            assert!(!engine.environment().contains(&name));
        }

        let mut candidate_only = EngineAdmissionLimits::new(test_budget());
        candidate_only.checker.environment = fln_checker::environment::EnvironmentBudget::new(
            u64::MAX,
            1,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            u64::MAX,
        );
        let retained = checked
            .engine
            .admit_declaration(
                typed_axiom("AfterColor", Expr::sort(Level::zero())),
                &KVMap::new(),
                candidate_only,
            )
            .expect("the retained four-row checker block leaves one row for its consumer")
            .into_complete()
            .expect("the follower admission answers completely");
        assert!(
            retained
                .engine
                .environment()
                .contains(&Name::from_components(["AfterColor"]))
        );

        let uncached = Engine::from_environment(checked.engine.environment().clone());
        assert!(matches!(
            uncached.admit_declaration(
                typed_axiom("UncachedAfterColor", Expr::sort(Level::zero())),
                &KVMap::new(),
                candidate_only,
            ),
            Err(EngineAdmissionError::CouncilNoAnswer { .. })
        ));
        assert!(
            !uncached
                .environment()
                .contains(&Name::from_components(["UncachedAfterColor"]))
        );
    }

    #[test]
    fn standalone_olean_check_reconstructs_a_nullary_inductive_authority_unit() {
        let constants = enumeration_declarations(BinderInfo::Implicit);
        let bytes = standalone_olean(&constants);
        let engine = Engine::from_environment(Environment::new());
        let checked = engine
            .check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            )
            .expect("the complete inductive envelope is reconstructible")
            .into_complete()
            .expect("K1 and the independent inductive judgment complete");

        assert_eq!(checked.declarations.len(), 4);
        assert!(checked.declarations.iter().all(|declaration| {
            declaration.checker.ground == CheckerAdmissionGround::InductiveNonrecursiveChecked
        }));
        for name in [
            Name::from_components(["Fixture", "Color"]),
            Name::from_components(["Fixture", "Color", "red"]),
            Name::from_components(["Fixture", "Color", "blue"]),
            Name::from_components(["Fixture", "Color", "rec"]),
        ] {
            assert!(checked.engine.environment().contains(&name));
            assert!(!engine.environment().contains(&name));
        }
    }

    #[test]
    fn standalone_olean_check_reconstructs_dependent_nonrecursive_fields() {
        let constants = dependent_field_inductive_declarations();
        let bytes = standalone_olean(&constants);
        let engine = Engine::from_environment(Environment::new());
        let checked = engine
            .check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            )
            .expect("the complete dependent-field inductive is reconstructible")
            .into_complete()
            .expect("K1 and the independent field-bearing judgment complete");

        assert_eq!(checked.declarations.len(), 3);
        assert!(checked.declarations.iter().all(|declaration| {
            declaration.checker.ground == CheckerAdmissionGround::InductiveNonrecursiveChecked
        }));
        for name in [
            Name::from_components(["Fixture", "Witness"]),
            Name::from_components(["Fixture", "Witness", "mk"]),
            Name::from_components(["Fixture", "Witness", "rec"]),
        ] {
            assert!(checked.engine.environment().contains(&name));
            assert!(!engine.environment().contains(&name));
        }

        let mut exhausted_limits = OleanCheckLimits::new(bytes.len(), test_budget());
        exhausted_limits.admission.checker.environment =
            fln_checker::environment::EnvironmentBudget::new(0, 0, 0, 0, 0, 0);
        let exhausted_engine = Engine::from_environment(Environment::new());
        assert!(matches!(
            exhausted_engine.check_olean_artifact(&bytes, &KVMap::new(), exhausted_limits,),
            Err(OleanCheckError::Admission(
                EngineAdmissionError::BatchDeclaration { .. }
            ))
        ));
        assert!(
            exhausted_engine.environment().is_empty(),
            "checker staging exhaustion cannot publish any K1 prefix"
        );
    }

    #[test]
    fn enumeration_envelope_and_checker_nonanswers_are_failure_atomic() {
        let mut incomplete = enumeration_declarations(BinderInfo::Implicit);
        incomplete.pop();
        let bytes = standalone_olean(&incomplete);
        let engine = Engine::from_environment(Environment::new());
        assert!(matches!(
            engine.check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            ),
            Err(OleanCheckError::InductiveEnvelopeUnsupported { .. })
        ));
        assert!(engine.environment().is_empty());

        let constants = enumeration_declarations(BinderInfo::Implicit);
        let constant_count = constants.len();
        let mut types = Vec::new();
        let mut constructors = Vec::new();
        let mut recursors = Vec::new();
        for constant in constants {
            match constant {
                ConstantInfo::Induct(value) => types.push(value),
                ConstantInfo::Ctor(value) => constructors.push(value),
                ConstantInfo::Rec(value) => recursors.push(value),
                _ => {}
            }
        }
        assert_eq!(
            types.len() + constructors.len() + recursors.len(),
            constant_count,
            "the enumeration fixture must contain only inductive authority rows"
        );
        constructors.sort_by_key(|constructor| constructor.cidx);
        let declaration = Declaration::Inductive(fln_kernel::InductiveBlock {
            types,
            ctors: constructors,
            recursors,
        });
        let mut limits = EngineAdmissionLimits::new(test_budget());
        limits.checker.admission.conversion.quick.max_comparisons = 0;
        let result = engine.admit_declaration(declaration, &KVMap::new(), limits);
        assert!(
            matches!(result, Err(EngineAdmissionError::CouncilNoAnswer { .. })),
            "checker exhaustion is a council non-answer, not a halt, got {result:?}"
        );
        assert!(engine.environment().is_empty());
    }

    #[test]
    fn malformed_quotient_unit_is_atomic_and_checker_exhaustion_is_not_rejection() {
        let mut malformed = quotient_declarations();
        let lift = malformed
            .get_mut(2)
            .and_then(|constant| match constant {
                ConstantInfo::Quot(value) => Some(value),
                _ => None,
            })
            .expect("fixture row 2 must be Quot.lift");
        lift.base.type_ = Expr::sort(Level::zero());
        let bytes = standalone_olean(&malformed);
        let engine = Engine::from_environment(equality_environment());
        assert!(matches!(
            engine.check_olean_artifact(
                &bytes,
                &KVMap::new(),
                OleanCheckLimits::new(bytes.len(), test_budget()),
            ),
            Err(OleanCheckError::Admission(
                EngineAdmissionError::BatchDeclaration { index: 0, .. }
            ))
        ));
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["Quot"]))
        );

        let quotient_rows: Option<Vec<_>> = quotient_declarations()
            .into_iter()
            .map(|constant| match constant {
                ConstantInfo::Quot(value) => Some(value),
                _ => None,
            })
            .collect();
        let declaration = Declaration::Quotient(
            quotient_rows.expect("the quotient fixture must contain only quotient rows"),
        );
        let mut limits = EngineAdmissionLimits::new(test_budget());
        limits.checker.admission.conversion.quick.max_comparisons = 0;
        assert!(matches!(
            engine.admit_declaration(declaration, &KVMap::new(), limits),
            Err(EngineAdmissionError::CouncilNoAnswer { .. })
        ));
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["Quot"]))
        );
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

    fn fixture_name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn fixture_constant(text: &str) -> Expr {
        Expr::const_(fixture_name(text), Vec::new())
    }

    fn fixture_imports(names: &[&str]) -> Vec<OleanModuleImport> {
        names
            .iter()
            .map(|text| OleanModuleImport {
                module: fixture_name(text),
                import_all: false,
                is_exported: false,
                is_meta: false,
            })
            .collect()
    }

    fn fixture_axiom(text: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: fixture_name(text),
                level_params: Vec::new(),
                type_,
            },
            is_unsafe: false,
        })
    }

    /// A theorem of `Fixture.P`.
    fn fixture_theorem(text: &str, value: Expr) -> ConstantInfo {
        ConstantInfo::Thm(TheoremVal {
            base: ConstantVal {
                name: fixture_name(text),
                level_params: Vec::new(),
                type_: fixture_constant("Fixture.P"),
            },
            value,
            all: Vec::new(),
        })
    }

    /// A closed set shaped so the scheduled door must reassemble serial rows:
    /// siblings `B`, `C` and `E` import only `A`, so each checks its own copy of a
    /// name the serial door meets after an earlier sibling's (`t` identical, `s` the
    /// same statement with another proof, the axiom `q` identical), and `D` imports
    /// `B` and `C` and repeats `t` inside its own closure.
    fn sibling_repeat_module_set() -> Vec<(Name, Vec<u8>)> {
        let witness = || fixture_constant("Fixture.p");
        let detour = Expr::app(
            Expr::lam(
                fixture_name("h"),
                fixture_constant("Fixture.P"),
                Expr::bvar(0).expect("test bound variable is in range"),
                BinderInfo::Default,
            ),
            witness(),
        );
        let module = |name: &str, constants: &[ConstantInfo], imports: &[&str]| {
            (
                fixture_name(name),
                olean_with_imports(constants, &fixture_imports(imports)),
            )
        };
        vec![
            module(
                "Fixture.A",
                &[
                    fixture_axiom("Fixture.P", Expr::sort(Level::zero())),
                    fixture_axiom("Fixture.p", fixture_constant("Fixture.P")),
                ],
                &[],
            ),
            module(
                "Fixture.B",
                &[
                    fixture_theorem("Fixture.t", witness()),
                    fixture_theorem("Fixture.s", witness()),
                ],
                &["Fixture.A"],
            ),
            module(
                "Fixture.C",
                &[
                    fixture_theorem("Fixture.t", witness()),
                    fixture_theorem("Fixture.s", detour),
                    fixture_axiom("Fixture.q", fixture_constant("Fixture.P")),
                ],
                &["Fixture.A"],
            ),
            module(
                "Fixture.D",
                &[
                    fixture_theorem("Fixture.t", witness()),
                    fixture_theorem("Fixture.u", fixture_constant("Fixture.s")),
                ],
                &["Fixture.B", "Fixture.C"],
            ),
            module(
                "Fixture.E",
                &[fixture_axiom("Fixture.q", fixture_constant("Fixture.P"))],
                &["Fixture.A"],
            ),
        ]
    }

    fn fixture_inputs(set: &[(Name, Vec<u8>)]) -> Vec<OleanModuleInput<'_>> {
        // Reversed, so input order and the serial order disagree.
        set.iter()
            .rev()
            .map(|(name, artifact)| OleanModuleInput {
                name,
                artifact,
                server_artifact: None,
                private_artifact: None,
            })
            .collect()
    }

    fn fixture_jobs(threads: usize) -> super::OleanFrontierJobs {
        super::OleanFrontierJobs {
            threads: std::num::NonZeroUsize::new(threads).expect("a positive thread count"),
            worker_stack_bytes: 2 * 1024 * 1024,
        }
    }

    /// The scheduled door's answer is the serial door's, value for value.
    fn assert_same_set_answer(
        serial: &Result<Outcome<super::CheckedOleanSet>, OleanCheckError>,
        scheduled: &Result<Outcome<super::CheckedOleanSet>, OleanCheckError>,
        what: &str,
    ) {
        match (serial, scheduled) {
            (Ok(Outcome::Complete(serial)), Ok(Outcome::Complete(scheduled))) => {
                super::assert_checked_sets_identical(serial, scheduled, what);
            }
            (Ok(Outcome::Inconclusive(serial)), Ok(Outcome::Inconclusive(scheduled))) => {
                assert_eq!(serial, scheduled, "{what}");
            }
            (Ok(Outcome::InternalFault(serial)), Ok(Outcome::InternalFault(scheduled))) => {
                assert_eq!(serial, scheduled, "{what}");
            }
            (Err(serial), Err(scheduled)) => assert_eq!(serial, scheduled, "{what}"),
            (serial, scheduled) => {
                let kind = |answer: &Result<Outcome<super::CheckedOleanSet>, OleanCheckError>| {
                    match answer {
                        Ok(Outcome::Complete(_)) => "complete".to_owned(),
                        Ok(Outcome::Inconclusive(reason)) => format!("inconclusive {reason:?}"),
                        Ok(Outcome::InternalFault(fault)) => format!("internal fault {fault:?}"),
                        Err(error) => format!("error {error:?}"),
                    }
                };
                panic!(
                    "{what}: serial and scheduled answers differ in kind: {} vs {}",
                    kind(serial),
                    kind(scheduled)
                );
            }
        }
    }

    #[test]
    fn scheduled_module_set_reassembles_the_serial_result_across_sibling_repeats() {
        let set = sibling_repeat_module_set();
        let inputs = fixture_inputs(&set);
        let limits = OleanCheckLimits::new(
            set.iter().map(|(_, artifact)| artifact.len()).sum(),
            test_budget(),
        );
        let engine = Engine::from_environment(Environment::new());
        let serial = engine.check_olean_modules(&inputs, &KVMap::new(), limits);
        let Ok(Outcome::Complete(checked)) = &serial else {
            panic!("the fixture set must complete serially: {serial:?}");
        };
        // The serial planner must meet `C`'s and `E`'s copies after earlier ones,
        // or this fixture exercises nothing a closure-only check would miss.
        let rows = |module: &str| -> Vec<String> {
            checked
                .modules
                .iter()
                .find(|checked| checked.name == fixture_name(module))
                .expect("fixture module")
                .declarations
                .iter()
                .map(|row| row.name.to_display_string())
                .collect()
        };
        assert_eq!(rows("Fixture.C"), ["Fixture.q", "Fixture.t", "Fixture.s"]);
        assert_eq!(rows("Fixture.E"), ["Fixture.q"]);
        let last = checked.modules.last().expect("five modules");
        assert_eq!(last.name, fixture_name("Fixture.E"));
        assert_eq!(last.base_logical_root, last.result_logical_root);
        for threads in [1, 2, 3, 5] {
            let scheduled = engine.check_olean_modules_scheduled(
                &inputs,
                &KVMap::new(),
                limits,
                fixture_jobs(threads),
                None,
            );
            assert_same_set_answer(&serial, &scheduled, &format!("{threads} threads"));
        }
    }

    /// Cancelled once some modules are decided, the scheduled door dispatches no
    /// more, lets the running councils finish, and answers inconclusive; never
    /// cancelled, it completes.
    #[test]
    fn scheduled_module_set_stops_dispatching_once_cancelled() {
        /// Cancelled from the `after`-th sample on.
        struct CancelAfter {
            samples: std::sync::atomic::AtomicUsize,
            after: usize,
        }
        impl super::CancellationProbe for CancelAfter {
            fn is_cancelled(&self) -> bool {
                self.samples
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                    >= self.after
            }
        }
        let set = sibling_repeat_module_set();
        let inputs = fixture_inputs(&set);
        let limits = OleanCheckLimits::new(
            set.iter().map(|(_, artifact)| artifact.len()).sum(),
            test_budget(),
        );
        let engine = Engine::from_environment(Environment::new());
        let run = |after: usize| {
            let probe = CancelAfter {
                samples: std::sync::atomic::AtomicUsize::new(0),
                after,
            };
            let answer = engine.check_olean_modules_scheduled(
                &inputs,
                &KVMap::new(),
                limits,
                fixture_jobs(2),
                Some(&probe),
            );
            (answer, probe.samples.into_inner())
        };
        for after in [0, 1] {
            let (answer, _) = run(after);
            assert!(
                matches!(
                    &answer,
                    Ok(Outcome::Inconclusive(reason))
                        if *reason == super::Inconclusive::cancelled("olean-modules/scheduled")
                ),
                "cancelled after {after} samples: {answer:?}"
            );
        }
        let (answer, samples) = run(usize::MAX);
        assert!(matches!(answer, Ok(Outcome::Complete(_))), "{answer:?}");
        // One sample before the first dispatch and one per decided module.
        assert_eq!(samples, set.len() + 1);
    }

    /// Whatever stops the serial door (a rejection, a council with no answer, an
    /// exhausted kernel, a missing or malformed member) stops the scheduled door
    /// with the same value, decided by the first module of the serial order, not by
    /// whichever finished first.
    #[test]
    fn scheduled_module_set_stops_where_the_serial_door_stops() {
        let mut set = sibling_repeat_module_set();
        // `F` first admits 400 axioms and then offers `Fixture.P` itself as a proof
        // of `Fixture.P`, which the kernel rejects; `G` cites a constant nobody
        // declares, which planning refuses before any kernel work. The serial order
        // reaches `F` first, while `G`, just as ready, stops long before `F` does.
        let mut slow: Vec<ConstantInfo> = (0..400)
            .map(|index| fixture_axiom(&format!("Fixture.a{index}"), fixture_constant("Fixture.P")))
            .collect();
        slow.push(fixture_theorem(
            "Fixture.bad1",
            fixture_constant("Fixture.P"),
        ));
        let refused = [fixture_theorem(
            "Fixture.bad2",
            fixture_constant("Fixture.nowhere"),
        )];
        for (module, constants) in [("Fixture.F", slow.as_slice()), ("Fixture.G", &refused)] {
            set.push((
                fixture_name(module),
                olean_with_imports(constants, &fixture_imports(&["Fixture.A"])),
            ));
        }
        let engine = Engine::from_environment(Environment::new());
        let limits = OleanCheckLimits::new(
            set.iter().map(|(_, artifact)| artifact.len()).sum(),
            test_budget(),
        );
        let same = |inputs: &[OleanModuleInput<'_>], limits: OleanCheckLimits, what: &str| {
            let serial = engine.check_olean_modules(inputs, &KVMap::new(), limits);
            for threads in [2, 3, 7] {
                let scheduled = engine.check_olean_modules_scheduled(
                    inputs,
                    &KVMap::new(),
                    limits,
                    fixture_jobs(threads),
                    None,
                );
                assert_same_set_answer(&serial, &scheduled, &format!("{what}, {threads} threads"));
            }
            serial
        };

        let inputs = fixture_inputs(&set);
        match same(&inputs, limits, "rejection") {
            Err(OleanCheckError::Admission(EngineAdmissionError::BatchDeclaration {
                error,
                ..
            })) => assert!(
                matches!(*error, EngineAdmissionError::KernelRejected { .. }),
                "the serial door stops at the kernel's rejection of `F`: {error:?}"
            ),
            other => panic!("the rejecting set must be refused at `F`: {other:?}"),
        }
        // On its own, `G` is refused differently, so the value above names `F`.
        let only_g: Vec<_> = inputs
            .iter()
            .copied()
            .filter(|input| *input.name != fixture_name("Fixture.F"))
            .collect();
        assert!(matches!(
            same(&only_g, limits, "planning refusal"),
            Err(OleanCheckError::MissingConstants { .. })
        ));

        // A council whose checker cannot retain anything has no answer. The serial
        // door returns that error; the frontier would call it inconclusive.
        let mut silent = limits;
        silent.admission.checker.environment.max_steps = 0;
        match same(&inputs, silent, "silent checker") {
            Err(OleanCheckError::Admission(EngineAdmissionError::BatchDeclaration {
                error,
                ..
            })) => assert!(
                matches!(*error, EngineAdmissionError::CouncilNoAnswer { .. }),
                "{error:?}"
            ),
            other => panic!("a silent checker must leave the council without an answer: {other:?}"),
        }

        let mut starved = limits;
        starved.admission.kernel.steps = 0;
        assert!(matches!(
            same(&inputs, starved, "starved kernel"),
            Ok(Outcome::Inconclusive(_))
        ));

        let without_a: Vec<_> = inputs
            .iter()
            .copied()
            .filter(|input| *input.name != fixture_name("Fixture.A"))
            .collect();
        assert!(matches!(
            same(&without_a, limits, "missing member"),
            Err(OleanCheckError::MissingModuleImports { .. })
        ));

        let mut malformed = set.clone();
        malformed[2].1[0] ^= u8::MAX;
        assert!(matches!(
            same(&fixture_inputs(&malformed), limits, "malformed member"),
            Err(OleanCheckError::ModuleDecode { .. })
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
        let stop =
            decode_olean_artifact(&bytes, limits).expect_err("five objects cannot decode it");
        assert_eq!(
            stop,
            OleanDecodeError::Declaration(OleanDeclarationError::Budget {
                visited: 6,
                budget: 5
            }),
            "the stop reports the allowance it exceeded (fln-s97y)"
        );
        let usage = stop
            .resource_usage()
            .expect("an explicit budget stop has a usage");
        assert_eq!((usage.allowed, usage.observed), (5, 6));
        assert!(usage.is_genuine_exhaustion());
    }

    /// The real frontier over a real pinned module (the checked-in C3 fixture), with a
    /// planted decode budget: the row is a typed resource exhaustion carrying the
    /// allowance, never `failed` (fln-s97y). With the decode budget restored, the same
    /// module is `failed` for a genuine reason (the fixture is a module-system part whose
    /// `.olean.server` and `.olean.private` are not supplied), so the planted row's verdict
    /// comes from the budget and nothing else.
    #[test]
    fn a_planted_decode_budget_stop_is_an_inconclusive_frontier_row_with_its_allowance() {
        use fln_core::diag::{ResourceReason, StructuralUnit};
        use fln_core::outcome::{Inconclusive, InconclusiveCause};

        let bytes = olean_fixture("Init.SizeOfLemmas.olean");
        let name = Name::from_components(["Init", "SizeOfLemmas"]);
        let inputs = [OleanModuleInput {
            name: &name,
            artifact: &bytes,
            server_artifact: None,
            private_artifact: None,
        }];
        let engine = Engine::from_environment(Environment::new());
        let run = |limits: OleanCheckLimits| {
            let frontier = engine
                .check_olean_frontier(&inputs, &KVMap::new(), limits)
                .expect("a one-module set is a frontier, not a whole-set refusal");
            assert_eq!(frontier.rows.len(), 1);
            frontier.rows.into_iter().next().expect("one row").verdict
        };

        let mut planted = OleanCheckLimits::new(bytes.len(), test_budget());
        planted.decode.declarations = OleanWalkBudget { max_objects: 5 };
        let verdict = run(planted);
        match &verdict {
            super::OleanModuleVerdict::Inconclusive(Inconclusive {
                cause: InconclusiveCause::ResourceExhausted { usage },
                ..
            }) => {
                assert_eq!(
                    usage.reason,
                    ResourceReason::StructuralBudget {
                        unit: StructuralUnit::ProducedNodes
                    }
                );
                assert_eq!((usage.allowed, usage.observed), (5, 6), "{usage:?}");
            }
            other => panic!("a decode budget stop must be inconclusive, got {other:?}"),
        }

        let control = run(OleanCheckLimits::new(bytes.len(), test_budget()));
        assert!(
            matches!(
                control,
                super::OleanModuleVerdict::Failed(OleanCheckError::MissingCompanionParts { .. })
            ),
            "with the budget restored the module fails for its missing companion parts, got {control:?}"
        );
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

    /// The committed `prelude.olean` chain, byte-identical to the pinned
    /// v4.32.0 stdlib's `Init/Prelude` exported, server and private parts
    /// (fln-cli's `olean_verify_rebuild_chain_fixture_is_the_pinned_init_prelude`
    /// holds that against the installed pin), read from the invoking tree.
    fn pinned_prelude_chain() -> [Vec<u8>; 3] {
        let manifest_dir = std::env::var_os("CARGO_MANIFEST_DIR")
            .map(std::path::PathBuf::from)
            .expect("cargo identifies the invoking crate directory");
        let dir = manifest_dir.join("../fln-conformance/fixtures/tag_attributes");
        ["", ".server", ".private"].map(|suffix| {
            let path = dir.join(format!("prelude.olean{suffix}"));
            std::fs::read(&path)
                .unwrap_or_else(|error| panic!("cannot read fixture {}: {error}", path.display()))
        })
    }

    #[test]
    fn public_olean_decoder_reuses_the_pinned_server_declaration_arrays() {
        let [exported, server, private] = pinned_prelude_chain();
        let public_view = super::OleanView::parse(&exported).expect("exported view");
        let server_view =
            super::OleanView::parse_with_dependencies(&server, &[&exported]).expect("server view");
        assert!(
            server_view
                .reuses_module_constant_arrays(&public_view)
                .unwrap(),
            "the real pinned Prelude must take the guarded reuse path"
        );
        let limits = OleanDecodeLimits::new(exported.len() + server.len() + private.len());
        let exported_constants = super::DeclDecoder::new(&public_view, limits.declarations)
            .decode_module_constants()
            .expect("exported declarations");
        let server_constants = super::DeclDecoder::new(&server_view, limits.declarations)
            .decode_module_constants()
            .expect("the omitted server pass");
        assert_eq!(exported_constants, server_constants);
        let decoded = super::decode_olean_module_artifacts(&exported, &server, &private, limits)
            .expect("the pinned chain still decodes");
        assert!(decoded.companion_parts_loaded);
        assert_eq!(decoded.constants.len(), 2314);
        assert!(matches!(
            decoded.independent,
            super::IndependentReading::Read(_)
        ));
    }

    #[test]
    fn public_olean_decoder_checks_unshared_server_arrays_and_their_budget() {
        let base = super::OLEAN_REGION_ALIGN as u64;
        let axiom = |name: &str, type_| {
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: Name::from_components([name]),
                    level_params: Vec::new(),
                    type_,
                },
                is_unsafe: false,
            })
        };
        let encode = |constants: &[ConstantInfo], part| {
            super::encode_olean_module(
                super::OleanModuleWriteInput {
                    is_module: true,
                    imports: &[],
                    constants,
                    extra_const_names: &[],
                },
                super::OleanWriteHeader {
                    version: 2,
                    flags: 1,
                    lean_version: super::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
                    githash: super::OLEAN_PIN_COMMIT,
                    base_addr: part * base,
                },
                super::OleanWriteBudget::default(),
            )
            .expect("module fixture encodes")
            .bytes
        };
        let public_constants = [axiom("Public", Expr::sort(Level::zero()))];
        let exported = encode(&public_constants, 1);
        let private = encode(&public_constants, 3);
        let server = encode(&[axiom("Server", Expr::sort(Level::zero()))], 2);
        let limits = OleanDecodeLimits::new(exported.len() + server.len() + private.len());
        let decode = |server: &[u8], limits| {
            super::decode_olean_module_artifacts(&exported, server, &private, limits)
        };
        assert_eq!(
            decode(&server, limits)
                .expect("valid unshared server")
                .constants,
            public_constants
        );

        // Bind either one of the server's arrays to the exported array. Both
        // arrays still have one member, but their names disagree. A names-only
        // or constants-only shortcut would silently accept one of these cells.
        let root = |bytes: &[u8], part| {
            let start = fln_olean::format::OLEAN_HEADER_SIZE;
            (u64::from_le_bytes(bytes[start..start + 8].try_into().unwrap()) - part * base) as usize
        };
        let slot = |field| {
            let index = fln_olean::format::MODULE_DATA_FIELDS
                .iter()
                .filter(|field| field.lean_type != "Bool")
                .position(|candidate| candidate.name == field)
                .expect("generated field");
            8 * (index + 1)
        };
        for field in ["constNames", "constants"] {
            let source = root(&exported, 1) + slot(field);
            let target = root(&server, 2) + slot(field);
            let mut altered = server.clone();
            altered[target..target + 8].copy_from_slice(&exported[source..source + 8]);
            assert!(matches!(
                decode(&altered, limits),
                Err(OleanDecodeError::CompanionDeclaration {
                    part: super::OleanCompanionPart::Server,
                    error: OleanDeclarationError::Shape {
                        what: "constNames[i] != constants[i].name",
                        ..
                    },
                })
            ));
        }

        let mut type_ = Expr::sort(Level::zero());
        for index in 0..32 {
            type_ = Expr::forall_e(
                Name::num(Name::anonymous(), index),
                Expr::sort(Level::zero()),
                type_,
                BinderInfo::Default,
            );
        }
        let larger_server = encode(&[axiom("Server", type_)], 2);
        let mut limits =
            OleanDecodeLimits::new(exported.len() + larger_server.len() + private.len());
        assert!(decode(&larger_server, limits).is_ok());
        limits.declarations.max_objects = 16;
        let error = decode(&larger_server, limits).expect_err("unshared server exceeds its budget");
        assert!(matches!(
            error,
            OleanDecodeError::CompanionDeclaration {
                part: super::OleanCompanionPart::Server,
                error: OleanDeclarationError::Budget { .. },
            }
        ));
        assert!(error.is_resource_exhaustion());
        limits.declarations.max_objects = 0;
        assert!(matches!(
            decode(&server, limits),
            Err(OleanDecodeError::Declaration(
                OleanDeclarationError::Budget { .. }
            ))
        ));
    }

    #[test]
    fn public_olean_module_rebuild_door_rederives_a_real_chain_per_part() {
        use super::{
            OleanModulePart, OleanModuleParts, OleanPartRebuild, rebuild_olean_module_artifacts,
        };
        let [exported, server, private] = pinned_prelude_chain();
        let total = exported.len() + server.len() + private.len();

        // The standalone door cannot rebuild a companion: its pointers into
        // the earlier parts resolve nowhere in its own region.
        for companion in [&server, &private] {
            assert!(matches!(
                rebuild_olean_artifact(companion, companion.len()),
                Err(OleanRebuildError::Region(
                    OleanRegionError::PtrOutOfBounds { .. }
                ))
            ));
        }

        let chain = OleanModuleParts {
            exported: &exported,
            server: Some(&server),
            private: Some(&private),
        };
        let rebuilt = rebuild_olean_module_artifacts(chain, total)
            .expect("the real pinned chain rebuilds at exactly its own size");
        assert_eq!(
            rebuilt.iter().map(|part| part.part).collect::<Vec<_>>(),
            OleanModulePart::LOAD_ORDER,
            "one answer per part, in load order"
        );
        for (
            OleanPartRebuild {
                part,
                bytes,
                report,
            },
            original,
        ) in rebuilt.iter().zip([&exported, &server, &private])
        {
            assert!(bytes == original, "{part} rebuilds byte-identically");
            assert!(report.findings.is_empty(), "{part}: {:?}", report.findings);
            assert_eq!(report.nonzero_padding_bytes, 0, "{part}");
            if *part == OleanModulePart::Exported {
                assert_eq!(
                    report.dependency_pointers, 0,
                    "the exported part is standalone"
                );
            } else {
                assert!(
                    report.dependency_pointers > 0,
                    "{part} never crossed into a predecessor"
                );
            }
        }

        // A load-order prefix is what the Reference's reader accepts too.
        let prefix = OleanModuleParts {
            private: None,
            ..chain
        };
        let rebuilt = rebuild_olean_module_artifacts(prefix, total).expect("a prefix rebuilds");
        assert_eq!(rebuilt.len(), 2);
        assert!(rebuilt[1].part == OleanModulePart::Server && rebuilt[1].bytes == server);

        // Typed refusals: a gap in load order, the byte bound over the parts
        // together, and a corrupted companion named as itself.
        let gap = OleanModuleParts {
            server: None,
            ..chain
        };
        let refusal = rebuild_olean_module_artifacts(gap, total)
            .expect_err("a private part without its server part is refused");
        assert_eq!(
            refusal,
            OleanRebuildError::MissingPredecessor {
                part: OleanModulePart::Private,
                missing: OleanModulePart::Server,
            }
        );
        assert!(!refusal.is_resource_exhaustion());

        let refusal = rebuild_olean_module_artifacts(chain, total - 1)
            .expect_err("one byte under the chain's size is refused");
        assert_eq!(
            refusal,
            OleanRebuildError::ArtifactTooLarge {
                bytes: total,
                limit: total - 1,
            }
        );
        assert!(refusal.is_resource_exhaustion());

        let mut corrupted = private.clone();
        corrupted[0] ^= u8::MAX;
        let refusal = rebuild_olean_module_artifacts(
            OleanModuleParts {
                private: Some(&corrupted),
                ..chain
            },
            total,
        )
        .expect_err("a corrupted private part is refused");
        assert_eq!(
            refusal,
            OleanRebuildError::PartRegion {
                part: OleanModulePart::Private,
                error: OleanRegionError::BadMagic,
            }
        );
        assert!(!refusal.is_resource_exhaustion());
    }

    /// Both rebuild doors hold every part's header to the pin (bead
    /// `fln-fur.1`). The rebuild re-derives the header from its parsed fields,
    /// so the codec alone reproduces a forged one byte for byte: the door's
    /// check is the only thing standing between the forgery and a verified
    /// rebuild, and each cell shows that first.
    #[test]
    fn public_olean_rebuild_doors_refuse_a_header_the_pin_did_not_write() {
        use super::{OleanModulePart, OleanModuleParts, rebuild_olean_module_artifacts};
        let offset = |name: &str| {
            fln_olean::format::OLEAN_HEADER_FIELDS
                .iter()
                .find(|field| field.name == name)
                .map(|field| field.offset)
                .expect("a generated header field")
        };
        // `(field, offset, byte)`: flags cleared, Lean `5.32.0`, another commit.
        let forgeries = [
            ("flags", offset("flags"), 0x00),
            ("lean_version", offset("lean_version"), b'5'),
            ("githash", offset("githash"), b'9'),
        ];
        let forge = |bytes: &[u8], at: usize, byte: u8| {
            let mut forged = bytes.to_vec();
            assert_ne!(forged[at], byte, "the edit must change a byte");
            forged[at] = byte;
            forged
        };
        let refused_as = |refusal: &OleanRebuildError, part: OleanModulePart, field: &str| {
            matches!(
                refusal,
                OleanRebuildError::HeaderNotPinned { part: refused, mismatch }
                    if *refused == part && mismatch.field == field
            ) && refusal.to_string().starts_with(&format!(
                "incompatible {part} header: header field `{field}`"
            )) && !refusal.is_resource_exhaustion()
        };

        let standalone = olean_fixture("Init.BinderNameHint.olean");
        for (field, at, byte) in forgeries {
            let forged = forge(&standalone, at, byte);
            let (codec, _) = fln_olean::rebuild::rebuild(&forged).expect("the codec rebuilds it");
            assert!(codec == forged, "{field}: the codec reproduces the forgery");
            let refusal = rebuild_olean_artifact(&forged, forged.len()).expect_err(field);
            assert!(
                refused_as(&refusal, OleanModulePart::Exported, field),
                "{field}: {refusal:?}"
            );
        }
        // The envelope still answers first: a forged header behind a bad magic
        // is refused as the bad magic.
        let mut both = forge(&standalone, offset("githash"), b'9');
        both[0] ^= u8::MAX;
        assert!(matches!(
            rebuild_olean_artifact(&both, both.len()),
            Err(OleanRebuildError::Region(OleanRegionError::BadMagic))
        ));

        let chain = pinned_prelude_chain();
        let total = chain.iter().map(Vec::len).sum();
        let rebuild = |parts: &[Vec<u8>; 3]| {
            rebuild_olean_module_artifacts(
                OleanModuleParts {
                    exported: &parts[0],
                    server: Some(&parts[1]),
                    private: Some(&parts[2]),
                },
                total,
            )
        };
        assert!(
            rebuild(&chain).is_ok(),
            "the unforged pinned chain rebuilds"
        );
        for (index, part) in OleanModulePart::LOAD_ORDER.into_iter().enumerate() {
            for (field, at, byte) in forgeries {
                let mut parts = chain.clone();
                parts[index] = forge(&chain[index], at, byte);
                let loaded: Vec<&[u8]> = parts[..index].iter().map(Vec::as_slice).collect();
                let (codec, _) =
                    fln_olean::rebuild::rebuild_with_dependencies(&parts[index], &loaded)
                        .expect("the codec rebuilds the forged part");
                assert!(
                    codec == parts[index],
                    "{part} {field}: the codec reproduces it"
                );
                let refusal = rebuild(&parts).expect_err("a forged part is refused");
                assert!(
                    refused_as(&refusal, part, field),
                    "{part} {field}: {refusal:?}"
                );
            }
        }
        // Load order decides: an earlier part's forgery is the one reported.
        let mut parts = chain;
        parts[2] = forge(&parts[2], offset("flags"), 0x00);
        parts[1] = forge(&parts[1], offset("githash"), b'9');
        let refusal = rebuild(&parts).expect_err("two forged parts");
        assert!(
            refused_as(&refusal, OleanModulePart::Server, "githash"),
            "{refusal:?}"
        );
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
            EngineBvDecideError::Admission(EngineAdmissionError::CouncilNoAnswer {
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
            EngineExecutionError::CouncilNoAnswer { ref summary }
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
            EngineExecutionError::CouncilNoAnswer { ref summary }
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
            EngineAdmissionError::CouncilNoAnswer { ref summary }
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
        // The candidate cites `first_postulate`, whose own type cites `Nat`: a
        // two-row base that only a retained projection can supply under a
        // one-row budget.
        let cites_first = || {
            definition(
                "second_postulate",
                Expr::const_(Name::from_components(["first_postulate"]), Vec::new()),
            )
        };
        let second = first
            .engine
            .admit_declaration(cites_first(), &options, candidate_only)
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
            .admit_declaration(cites_first(), &options, candidate_only)
            .expect_err("the same budget cannot reconstruct the multi-row base");
        assert!(matches!(
            error,
            EngineAdmissionError::CouncilNoAnswer { ref summary }
                if summary.contains("fln-checker") && summary.contains("no answer")
        ));
        assert_eq!(uncached.logical_root(&options), uncached_root);
        assert!(
            !uncached
                .environment()
                .contains(&Name::from_components(["second_postulate"]))
        );
    }

    #[test]
    fn a_subsuming_olean_repeat_is_planned_then_its_own_body_is_rechecked() {
        let options = KVMap::new();
        let limits = EngineAdmissionLimits::new(test_budget());
        let admit = |engine: &Engine, declaration: Declaration| -> Engine {
            match engine.admit_declaration(declaration, &options, limits) {
                Ok(Outcome::Complete(admitted)) => Some(admitted.engine),
                _ => None,
            }
            .expect("setup admission must complete")
        };
        let nat = nat_type();
        let proposition = Expr::const_(Name::from_components(["P"]), Vec::new());
        let proof = Expr::const_(Name::from_components(["h"]), Vec::new());
        let statement = |binder: &str, info: BinderInfo| {
            Expr::forall_e(
                Name::from_components([binder]),
                nat.clone(),
                proposition.clone(),
                info,
            )
        };
        let engine = admit(
            &seeded_engine(),
            typed_axiom("P", Expr::sort(Level::zero())),
        );
        let engine = admit(&engine, typed_axiom("h", proposition.clone()));
        let first_body = Expr::lam(
            Name::from_components(["x"]),
            nat.clone(),
            proof.clone(),
            BinderInfo::Default,
        );
        let engine = admit(
            &engine,
            theorem("t", statement("x", BinderInfo::Default), first_body),
        );
        let root = engine.logical_root(&options);

        // A repeat the Reference's rule admits: renamed binders and a different
        // binder style in the statement, and its own proof term.
        let repeat = |value: Expr| match theorem("t", statement("y", BinderInfo::Implicit), value) {
            Declaration::Thm(theorem) => ConstantInfo::Thm(theorem),
            _ => unreachable!("theorem() builds a theorem"),
        };
        let own_body = Expr::lam(
            Name::from_components(["y"]),
            nat.clone(),
            proof.clone(),
            BinderInfo::Implicit,
        );
        let olean_limits = OleanCheckLimits::new(1 << 20, test_budget());
        let plan =
            super::plan_olean_declarations(engine.environment(), &[repeat(own_body)], olean_limits)
                .expect("the Reference's import accepts a subsuming repeat");
        assert!(plan.order.is_empty() && plan.already_present.is_empty());
        assert_eq!(plan.subsumed.len(), 1);

        let rechecked = match engine
            .recheck_subsumed_repeats(plan.subsumed, &options, limits, ReadingCheck::Unread)
            .expect("a well-typed repeat body rechecks")
        {
            Outcome::Complete(rechecked) => Some(rechecked),
            _ => None,
        }
        .expect("the recheck answers completely");
        assert_eq!(rechecked.len(), 1);
        assert_eq!(rechecked[0].name, Name::from_components(["t"]));
        assert_eq!(
            rechecked[0].checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        assert_eq!(
            engine.logical_root(&options),
            root,
            "the recheck publishes nothing"
        );

        // The repeat's own body is what gets checked: a proof of `P` where a
        // proof of `∀ y, P` is due is refused.
        let bad =
            super::plan_olean_declarations(engine.environment(), &[repeat(proof)], olean_limits)
                .expect("the statement still subsumes");
        assert!(
            engine
                .recheck_subsumed_repeats(bad.subsumed, &options, limits, ReadingCheck::Unread)
                .is_err(),
            "an ill-typed repeat body must not be counted as checked"
        );

        // A repeat whose statement differs is not subsumed.
        let other = match theorem(
            "t",
            proposition.clone(),
            Expr::const_(Name::from_components(["h"]), Vec::new()),
        ) {
            Declaration::Thm(theorem) => ConstantInfo::Thm(theorem),
            _ => unreachable!("theorem() builds a theorem"),
        };
        assert!(matches!(
            super::plan_olean_declarations(engine.environment(), &[other], olean_limits),
            Err(OleanCheckError::DuplicateDeclaration { .. })
        ));
    }

    #[test]
    fn the_default_checker_decode_budget_binds_on_bytes_not_units() {
        let default = super::CheckerExecutionLimits::default().decode;
        assert!(
            default.max_produced_units >= default.max_input_bytes,
            "each produced unit reads at least one byte, so a unit bound below \
             the byte bound refuses inputs the byte bound admits"
        );
        // A left-nested application spine with a fresh leaf per argument: every
        // node is its own allocation, so the shared transport carries all
        // 1,200,001 of them as records (an application is 9 bytes, a bound
        // variable 5), past the old 1_000_000-unit bound and under the byte
        // bound.
        let mut spine = Expr::bvar(0).expect("small index");
        for index in 0..600_000u32 {
            spine = Expr::app(spine, Expr::bvar(index % 1000).expect("small index"));
        }
        let bytes = super::encode_checker_expr_dag(&spine, usize::MAX)
            .expect("unbounded")
            .len() as u64;
        assert!(
            bytes > 1_200_001 && bytes < default.max_input_bytes,
            "{bytes}"
        );
        super::decode_checker_expr(&spine, default)
            .expect("an expression within the byte bound decodes under the default budget");
        // The control: the old unit bound refuses this same input on units.
        let refusal = super::decode_checker_expr(
            &spine,
            super::CheckerDecodeBudget::new(default.max_input_bytes, 1_000_000),
        )
        .expect_err("the old unit bound stops before the spine is decoded");
        assert!(refusal.contains("ProducedUnits"), "{refusal}");
    }

    #[test]
    fn frontier_engines_keep_a_base_only_while_a_later_module_starts_from_it() {
        use super::{FrontierEngines, frontier_base_of};
        use std::collections::BTreeSet;
        use std::sync::Arc;
        // 1 and 2 import 0; 3 imports 1 and 2, whose closures tie in size, so 3
        // starts from the earlier, 1. Neither 2 nor 3 is anyone's base.
        let dependencies: Vec<BTreeSet<usize>> = vec![
            BTreeSet::new(),
            BTreeSet::from([0]),
            BTreeSet::from([0]),
            BTreeSet::from([1, 2]),
        ];
        let closures: Vec<Arc<BTreeSet<usize>>> = vec![
            Arc::new(BTreeSet::from([0])),
            Arc::new(BTreeSet::from([0, 1])),
            Arc::new(BTreeSet::from([0, 2])),
            Arc::new(BTreeSet::from([0, 1, 2, 3])),
        ];
        let base_of: Vec<_> = (0..4)
            .map(|index| frontier_base_of(&dependencies, &closures, |p| p, index))
            .collect();
        assert_eq!(base_of, vec![None, Some(0), Some(0), Some(1)]);
        let mut engines = FrontierEngines::new(base_of);
        for index in 0..4 {
            engines.keep(index, Some(Engine::builder().build_empty()));
        }
        let kept = |engines: &FrontierEngines| -> Vec<bool> {
            engines.engines.iter().map(Option::is_some).collect()
        };
        assert_eq!(kept(&engines), [true, true, false, false]);
        // 1 is dispatched from 0, which 2 still needs.
        assert!(engines.release(1, &closures, true).unwrap().is_some());
        assert_eq!(kept(&engines), [true, true, false, false]);
        // 2 is decided without a check (blocked): 0 has no user left.
        assert!(engines.release(2, &closures, false).unwrap().is_none());
        assert_eq!(kept(&engines), [false, true, false, false]);
        let base = engines
            .release(3, &closures, true)
            .unwrap()
            .expect("3 starts from 1");
        assert_eq!(*base.closure, BTreeSet::from([0, 1]));
        assert_eq!(kept(&engines), [false, false, false, false]);
        // A module released twice is an invariant failure, never a silent reuse.
        assert!(engines.release(3, &closures, true).is_err());
    }

    #[test]
    fn frontier_closures_merge_a_repeated_name_by_the_import_rule() {
        use super::{ConstantInfo, merge_frontier_entry};
        let name = || Name::from_components(["t"]);
        let constant = |label: &str| Expr::const_(Name::from_components([label]), Vec::new());
        let theorem = |type_: Expr, value: Expr| {
            ConstantInfo::Thm(TheoremVal {
                base: ConstantVal {
                    name: name(),
                    level_params: Vec::new(),
                    type_,
                },
                value,
                all: vec![name()],
            })
        };
        let axiom = |label: &str, type_: Expr| {
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: Name::from_components([label]),
                    level_params: Vec::new(),
                    type_,
                },
                is_unsafe: false,
            })
        };
        let mut base = Environment::new();
        for (label, type_) in [
            ("P", Expr::sort(Level::zero())),
            ("Q", Expr::sort(Level::zero())),
            ("h1", constant("P")),
            ("h2", constant("P")),
        ] {
            base = base.add_decl(axiom(label, type_)).expect("unique");
        }
        let entry = |info: ConstantInfo| {
            base.add_decl(info)
                .expect("unique")
                .entry(&name())
                .expect("present")
        };
        let first = base
            .add_decl(theorem(constant("P"), constant("h1")))
            .expect("unique");

        // An absent name is added, digest and all.
        let added =
            merge_frontier_entry(base.clone(), &entry(theorem(constant("P"), constant("h1"))))
                .expect("absent");
        assert_eq!(added, first);
        // An identical copy is already there.
        let identical = merge_frontier_entry(
            first.clone(),
            &entry(theorem(constant("P"), constant("h1"))),
        )
        .expect("identical");
        assert_eq!(identical, first);
        // The same statement with another proof subsumes: the present copy stays.
        let subsumed = merge_frontier_entry(
            first.clone(),
            &entry(theorem(constant("P"), constant("h2"))),
        )
        .expect("subsumed");
        assert_eq!(subsumed, first);
        // Another statement cannot be imported beside it.
        assert!(matches!(
            merge_frontier_entry(first, &entry(theorem(constant("Q"), constant("h1")))),
            Err(OleanCheckError::DuplicateDeclaration { name: refused }) if refused == name()
        ));
    }

    /// The frontier's union engine exists only when the accepted modules merge:
    /// two modules that never import each other may each declare a different
    /// `main`, and then the union is that duplicate, never a lost run.
    #[test]
    fn the_union_of_accepted_modules_is_refused_only_for_a_real_duplicate() {
        use super::{ConstantInfo, FrontierAccepted};
        let main = || Name::from_components(["main"]);
        let axiom = |name: Name, type_: Expr| {
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name,
                    level_params: Vec::new(),
                    type_,
                },
                is_unsafe: false,
            })
        };
        let module = |index: usize, label: &str, type_: Expr| FrontierAccepted {
            index,
            position: index,
            name: Name::from_components([label]),
            admitted: vec![
                Environment::new()
                    .add_decl(axiom(main(), type_))
                    .expect("unique")
                    .entry(&main())
                    .expect("present"),
            ],
        };
        let engine = Engine::from_environment(Environment::new());
        let prop = Expr::sort(Level::zero());
        let ty = Expr::sort(Level::one());

        let same = engine
            .frontier_union_engine([&module(0, "A", prop.clone()), &module(1, "B", prop.clone())])
            .expect("an identical declaration merges");
        assert!(same.environment.entry(&main()).is_some());
        assert_eq!(
            same.imported_modules().iter().cloned().collect::<Vec<_>>(),
            [Name::from_components(["A"]), Name::from_components(["B"])]
        );
        assert!(matches!(
            engine.frontier_union_engine([&module(0, "A", prop), &module(1, "B", ty)]),
            Err(OleanCheckError::DuplicateDeclaration { name }) if name == main()
        ));
    }

    #[test]
    fn terms_cross_to_the_checker_as_their_dag() {
        use fln_hash::canon::Canonical;
        // A balanced application tree of depth 40 over `Sort 0`, shared in
        // memory: 2^41 - 1 tree nodes over 41 distinct ones. Its tree encoding
        // could never be built; its shared encoding is 41 records.
        let mut tree = Expr::sort(Level::zero());
        for _ in 0..40 {
            tree = Expr::app(tree.clone(), tree);
        }
        assert!(tree.to_canonical_bytes_within(1 << 20).is_none());
        let decoded =
            super::decode_checker_expr(&tree, super::CheckerExecutionLimits::default().decode)
                .expect("the shared encoding fits");
        assert_eq!(decoded.nodes().len(), 41);
    }

    #[test]
    fn checker_projection_covers_reachable_constants_and_drops_base_proofs() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let limits = EngineAdmissionLimits::new(test_budget());
        let admit = |engine: &Engine, declaration: Declaration| -> Engine {
            match engine.admit_declaration(declaration, &options, limits) {
                Ok(Outcome::Complete(admitted)) => Some(admitted.engine),
                _ => None,
            }
            .expect("setup admission must complete")
        };
        let proposition = Name::from_components(["P"]);
        let engine = admit(&engine, typed_axiom("P", Expr::sort(Level::zero())));
        let engine = admit(
            &engine,
            typed_axiom("h", Expr::const_(proposition.clone(), Vec::new())),
        );
        let engine = admit(
            &engine,
            theorem(
                "proved",
                Expr::const_(proposition.clone(), Vec::new()),
                Expr::const_(Name::from_components(["h"]), Vec::new()),
            ),
        );

        let uncached = Engine::from_environment(engine.environment().clone());
        let cited = admit(
            &uncached,
            theorem(
                "again",
                Expr::const_(proposition, Vec::new()),
                Expr::const_(Name::from_components(["proved"]), Vec::new()),
            ),
        );
        let projection = cited
            .checker_environment
            .as_ref()
            .expect("admission retains the projection it checked against");
        let wire = |name: &str| {
            super::decode_checker_name(
                &Name::from_components([name]),
                super::CheckerExecutionLimits::default().decode,
            )
            .expect("test names project")
        };
        let proved = projection
            .find(&wire("proved"))
            .expect("the cited theorem is projected");
        assert_eq!(proved.kind(), super::CheckerConstantKind::Theorem);
        assert!(
            proved.body_value().is_none(),
            "a base theorem is projected without its proof"
        );
        assert!(
            projection.find(&wire("h")).is_none(),
            "a constant reached only through a base proof is not projected"
        );
        assert!(projection.find(&wire("P")).is_some());
        assert!(
            projection
                .find(&wire("again"))
                .and_then(|again| again.body_value())
                .is_some(),
            "the admitted candidate itself keeps its checked body"
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

        // The follower cites nothing, so an uncached engine projects none of
        // the block: the checker base covers what a candidate reaches, not the
        // whole environment. (The checker quarantines partial definitions, so
        // no admissible candidate can cite this block to force it back in.)
        let uncached = Engine::from_environment(admitted.engine.environment().clone());
        let uncached_name = Name::from_components(["uncachedMutualFollower"]);
        let unrelated = uncached
            .admit_declaration(
                typed_axiom("uncachedMutualFollower", Expr::sort(Level::zero())),
                &options,
                candidate_only,
            )
            .expect("an unrelated candidate does not pay to project the block");
        let unrelated = match unrelated {
            Outcome::Complete(unrelated) => Some(unrelated),
            _ => None,
        }
        .expect("the uncached admission must answer completely");
        assert!(unrelated.engine.environment().contains(&uncached_name));
        let projection = unrelated
            .engine
            .checker_environment
            .as_ref()
            .expect("admission retains the projection it checked against");
        assert_eq!(
            projection.len(),
            1,
            "only the candidate itself is projected"
        );

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
        // An elaboration error. The pin's `prelude` analog (only `Nat` declared) reports
        // `Unknown constant `String`` at the literal, having auto-bound the unknown annotation
        // `String` as an implicit; this door has no auto-bound implicits and stops at the
        // annotation.
        assert_eq!(
            unknown_name_message(&missing_type).as_deref(),
            Some("Unknown identifier `String`"),
            "{missing_type:?}"
        );

        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let expected_constants: usize = fln_elab::seed::source_seed_declarations()
            .into_iter()
            .chain(
                fln_elab::seed::float_numeric_seed()
                    .expect("the numeric candidate inventory is valid")
                    .declarations,
            )
            .map(|declaration| match declaration {
                Declaration::Inductive(block) => {
                    block.types.len() + block.ctors.len() + block.recursors.len()
                }
                Declaration::Mutual(definitions) => definitions.len(),
                Declaration::Quotient(rows) => rows.len(),
                Declaration::Axiom(_)
                | Declaration::Defn(_)
                | Declaration::Thm(_)
                | Declaration::Opaque(_) => 1,
            })
            .sum();
        assert_eq!(engine.environment().len(), expected_constants);
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
        for name in [
            Name::from_components(["Bool", "false"]),
            Name::from_components(["Bool", "true"]),
            Name::from_components(["Bool", "rec"]),
        ] {
            assert!(engine.environment().contains(&name));
        }
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
        assert_eq!(
            completed.engine.environment().len(),
            engine.environment().len() + 2
        );
    }

    #[test]
    fn terminal_source_evaluation_reuses_the_checked_definition_pipeline() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let completed = engine
            .execute_source_definitions(
                &[b"def first (x y : Nat) : Nat := x\n#eval let chosen : Nat := first 42 9; Nat.add chosen 0"],
                &options,
                test_limits(),
            )
            .expect("a terminal bounded evaluation reaches the native pipeline");
        let Outcome::Complete(completed) = completed else {
            panic!("evaluation batch was not complete"); // ubs:ignore — test-only diagnostic.
        };

        assert_eq!(completed.executions.len(), 2);
        assert_eq!(completed.source_evaluation_indices, vec![1]);
        let Declaration::Defn(evaluation) = &completed.executions[1].declaration else {
            panic!("evaluation was not a definition"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(evaluation.base.name, Name::num(Name::anonymous(), 1));
        assert_eq!(
            evaluation.all.as_slice(),
            std::slice::from_ref(&evaluation.base.name)
        );
        let VmExit::Returned(returned) = &completed.executions[1].exit else {
            panic!("evaluation did not return"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(returned.value.unbox(), 42);
    }

    #[test]
    fn interleaved_evaluations_are_ordered_and_later_failure_remains_atomic() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let base_root = engine.logical_root(&options);
        let refusal = engine
            .execute_source_definitions(
                &[b"#eval Nat.add 40 2\ndef answer := missing"],
                &options,
                test_limits(),
            )
            .expect_err("a later definition refusal exposes no partial evaluation batch");
        // The pin on this file: `2:14: error(lean.unknownIdentifier): Unknown identifier
        // `missing`` (v4.32.0, 2026-10-05), an elaboration error.
        assert!(
            matches!(
                &refusal,
                EngineExecutionError::BatchCommand {
                    index: 1,
                    error,
                    ..
                } if unknown_name_message(error).as_deref()
                    == Some("Unknown identifier `missing`")
            ),
            "{refusal:?}"
        );
        assert_eq!(engine.logical_root(&options), base_root);

        let recovered = engine
            .execute_source_definitions(
                &[b"#eval Nat.add 40 2\ndef answer := 7\n#eval Nat.add answer 1\ndef final := answer"],
                &options,
                test_limits(),
            )
            .expect("evaluations and definitions execute in one checked source order");
        let Outcome::Complete(recovered) = recovered else {
            panic!("interleaved recovery was not complete"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(recovered.executions.len(), 4);
        assert_eq!(recovered.source_evaluation_indices, vec![0, 2]);
        for pair in recovered.executions.windows(2) {
            assert_eq!(pair[0].result_logical_root, pair[1].base_logical_root);
        }
        let Declaration::Defn(first_evaluation) = &recovered.executions[0].declaration else {
            panic!("first evaluation was not a definition candidate"); // ubs:ignore — test-only diagnostic.
        };
        let Declaration::Defn(second_evaluation) = &recovered.executions[2].declaration else {
            panic!("second evaluation was not a definition candidate"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(first_evaluation.base.name, Name::num(Name::anonymous(), 0));
        assert_eq!(second_evaluation.base.name, Name::num(Name::anonymous(), 2));
        let VmExit::Returned(first_returned) = &recovered.executions[0].exit else {
            panic!("first recovered evaluation did not return"); // ubs:ignore — test-only diagnostic.
        };
        let VmExit::Returned(second_returned) = &recovered.executions[2].exit else {
            panic!("second recovered evaluation did not return"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(first_returned.value.unbox(), 42);
        assert_eq!(second_returned.value.unbox(), 8);
    }

    #[test]
    fn generated_evaluation_names_skip_existing_unspellable_constants() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let occupied = Name::num(Name::anonymous(), 0);
        let declaration = Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: occupied.clone(),
                level_params: Vec::new(),
                type_: nat_type(),
            },
            value: Expr::lit(Literal::Nat(NatLit::from_u64(7))),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![occupied],
        });
        let Outcome::Complete(seed) = engine
            .execute_definition(declaration, &options, test_limits())
            .expect("the planted numeric-name definition is checked and executable")
        else {
            panic!("planted definition was not complete"); // ubs:ignore — test-only diagnostic.
        };

        let Outcome::Complete(completed) = seed
            .engine
            .execute_source_definitions(&[b"#eval Nat.add 40 2"], &options, test_limits())
            .expect("evaluation deterministically skips the occupied generated name")
        else {
            panic!("collision recovery was not complete"); // ubs:ignore — test-only diagnostic.
        };
        let Declaration::Defn(evaluation) = &completed.executions[0].declaration else {
            panic!("evaluation was not a definition"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(evaluation.base.name, Name::num(Name::anonymous(), 1));

        #[cfg(target_pointer_width = "64")]
        {
            let last = Name::num(Name::anonymous(), u64::MAX);
            let declaration = Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: last.clone(),
                    level_params: Vec::new(),
                    type_: nat_type(),
                },
                value: Expr::lit(Literal::Nat(NatLit::from_u64(9))),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![last],
            });
            let Outcome::Complete(last_seed) = seed
                .engine
                .execute_definition(declaration, &options, test_limits())
                .expect("the numeric name boundary is a checked environment row")
            else {
                panic!("numeric name boundary admission was not complete"); // ubs:ignore — test-only diagnostic.
            };
            assert!(matches!(
                fresh_generated_command_name(last_seed.engine.environment(), usize::MAX),
                Err(EngineExecutionError::UnexpectedPublication {
                    detail: "bounded source command could not derive a fresh generated name"
                })
            ));
        }
    }

    #[test]
    fn standalone_source_check_is_dual_checked_without_execution_or_publication() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let before = engine.logical_root(&options);

        let Outcome::Complete(checked_type) = engine
            .check_source_command(b"#check Nat", &options, test_limits().admission())
            .expect("a bounded type query reaches both checker seats")
        else {
            panic!("the bounded type query was not complete"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(checked_type.environment_root, before);
        assert_eq!(
            checked_type.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        assert!(matches!(
            checked_type.checked_type.node(),
            ExprNode::Sort { level } if level.to_nat() == Some(1)
        ));
        let Declaration::Defn(candidate) = &checked_type.declaration else {
            panic!("the checked query candidate must be a definition"); // ubs:ignore — test-only diagnostic.
        };
        assert!(
            matches!(candidate.value.node(), ExprNode::Const { name, .. } if name == &Name::from_components(["Nat"]))
        );
        assert_eq!(engine.logical_root(&options), before);
        assert!(
            !engine
                .environment()
                .contains(&Name::num(Name::anonymous(), 0)),
            "the scratch generated declaration must not escape the query"
        );

        let Outcome::Complete(function) = engine
            .check_source_command(b"#check Nat.add", &options, test_limits().admission())
            .expect("the seeded Nat.add signature is queryable")
        else {
            panic!("the bounded function query was not complete"); // ubs:ignore — test-only diagnostic.
        };
        assert!(matches!(
            function.checked_type.node(),
            ExprNode::ForallE { .. }
        ));

        let unknown = engine
            .check_source_command(b"#check Missing", &options, test_limits().admission())
            .expect_err("an unknown check term has no guessed type");
        assert!(matches!(unknown, EngineExecutionError::Frontend(_)));
        assert!(unknown.to_string().contains("no inferable type"));
        assert_eq!(engine.logical_root(&options), before);

        let interleaved = engine
            .execute_source_definitions(
                &[b"def answer := 42\n#check answer"],
                &options,
                test_limits(),
            )
            .expect_err("checks cannot be smuggled into executable batches");
        assert!(matches!(
            interleaved,
            EngineExecutionError::BatchCommand {
                index: 1,
                error,
                ..
            } if matches!(*error, EngineExecutionError::StandaloneCheckRequired)
        ));
        assert_eq!(engine.logical_root(&options), before);

        let term = fln_checker::term::TermBudget::new(0, 0).with_max_arena_nodes(0);
        let whnf = fln_checker::whnf::WhnfBudget::new(0, 0, term);
        let inference = fln_checker::infer::InferenceBudget::new(0, 0, term, term).with_whnf(whnf);
        let mut constrained = test_limits().admission();
        constrained.checker.admission =
            CheckerAdmissionBudget::new(inference, whnf, inference.defeq);
        let stopped = engine
            .check_source_command(b"#check Nat", &options, constrained)
            .expect_err("an independent-checker non-answer vetoes a source check");
        assert!(matches!(
            stopped,
            EngineExecutionError::CouncilNoAnswer { ref summary }
                if summary.contains("fln-checker") && summary.contains("no answer")
        ));
        assert_eq!(engine.logical_root(&options), before);

        assert!(matches!(
            engine
                .check_source_command(b"#check 40 + 2", &options, test_limits().admission(),)
                .expect("the unchanged engine recovers after both refusals"),
            Outcome::Complete(_)
        ));
    }

    #[test]
    fn terminal_source_check_observes_only_a_completed_definition_prefix() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let before = engine.logical_root(&options);

        let Outcome::Complete(terminal) = engine
            .check_terminal_source_command(
                b"def first (x : Nat) : Nat := x + 2\ndef answer : Nat := first 40\n#check answer",
                &options,
                test_limits(),
            )
            .expect("a terminal query observes its completed definition prefix")
        else {
            panic!("the terminal source check was not complete"); // ubs:ignore — test-only diagnostic.
        };
        let prefix = terminal
            .definition_prefix
            .as_ref()
            .expect("the completed definition prefix is retained");
        assert_eq!(prefix.executions.len(), 2);
        assert!(
            prefix
                .engine
                .environment()
                .contains(&Name::from_components(["first"]))
        );
        assert!(
            prefix
                .engine
                .environment()
                .contains(&Name::from_components(["answer"]))
        );
        assert_eq!(terminal.check.environment_root, prefix.result_logical_root);
        assert_eq!(terminal.check.checked_type, nat_type());
        let Declaration::Defn(query) = &terminal.check.declaration else {
            panic!("the terminal query candidate must be a definition"); // ubs:ignore — test-only diagnostic.
        };
        assert!(
            matches!(query.value.node(), ExprNode::Const { name, .. } if name == &Name::from_components(["answer"]))
        );
        assert!(
            !prefix.engine.environment().contains(&query.base.name),
            "the checked query row must not escape into the retained prefix successor"
        );
        assert_eq!(engine.logical_root(&options), before);

        let Outcome::Complete(function) = engine
            .check_terminal_source_command(
                b"def add (x : Nat) : Nat := x + 1\n#check add",
                &options,
                test_limits(),
            )
            .expect("a terminal query can inspect a checked source function")
        else {
            panic!("the terminal function check was not complete"); // ubs:ignore — test-only diagnostic.
        };
        assert!(matches!(
            function.check.checked_type.node(),
            ExprNode::ForallE { .. }
        ));

        let unknown = engine
            .check_terminal_source_command(
                b"def retained : Nat := 7\n#check Missing",
                &options,
                test_limits(),
            )
            .expect_err("a failed terminal query exposes no prefix successor");
        assert!(matches!(
            unknown,
            EngineExecutionError::BatchCommand {
                index: 1,
                error,
                ..
            } if matches!(*error, EngineExecutionError::Frontend(_))
        ));
        assert_eq!(engine.logical_root(&options), before);

        assert!(matches!(
            engine
                .check_terminal_source_command(b"#eval 1\n#check Nat", &options, test_limits(),)
                .expect_err("evaluation output is not admitted before a terminal check"),
            EngineExecutionError::TerminalCheckDefinitionPrefix { index: 0 }
        ));
        assert!(matches!(
            engine
                .check_terminal_source_command(
                    b"#check Nat\ndef later : Nat := 1",
                    &options,
                    test_limits(),
                )
                .expect_err("a nonterminal query stays outside this bounded command shape"),
            EngineExecutionError::TerminalCheckRequired
        ));
        assert_eq!(engine.logical_root(&options), before);
    }

    #[test]
    fn mixed_source_commands_preserve_output_order_and_never_publish_check_rows() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let before = engine.logical_root(&options);

        let Outcome::Complete(empty) = engine
            .execute_source_commands_with_checks(b"\n-- no commands\n", &options, test_limits())
            .expect("a parsed empty mixed stream is an identity transition")
        else {
            panic!("the empty mixed stream must answer completely"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(empty.command_count, 0);
        assert!(empty.batch.executions.is_empty());
        assert!(empty.execution_command_indices.is_empty());
        assert!(empty.outputs.is_empty());
        assert!(empty.checks.is_empty());
        assert_eq!(empty.batch.base_logical_root, before);
        assert_eq!(empty.batch.result_logical_root, before);
        assert_eq!(
            empty.batch.engine.environment().len(),
            engine.environment().len()
        );

        let Outcome::Complete(completed) = engine
            .execute_source_commands_with_checks(
                b"#check Nat\n#eval 40 + 2\ndef answer : Nat := 42\n#check answer\n#eval answer + 1\n#check Nat.add",
                &options,
                test_limits(),
            )
            .expect("definitions, evaluations, and checks share one ordered source stream")
        else {
            panic!("the mixed source command stream must answer completely"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(completed.command_count, 6);
        assert_eq!(completed.execution_command_indices, [1, 2, 4]);
        assert_eq!(completed.batch.executions.len(), 3);
        assert_eq!(completed.batch.source_evaluation_indices, [0, 2]);
        assert_eq!(completed.outputs.len(), 5);
        assert_eq!(completed.checks.len(), 3);
        assert_eq!(completed.batch.base_logical_root, before);
        assert_eq!(
            completed.batch.result_logical_root,
            completed.batch.executions[2].result_logical_root
        );
        assert!(
            completed
                .batch
                .engine
                .environment()
                .contains(&Name::from_components(["answer"]))
        );
        assert_eq!(
            closed_vm_value(&completed.batch.executions[0].exit),
            Ok(Some(ClosedVmValue::Scalar(42)))
        );
        assert_eq!(
            closed_vm_value(&completed.batch.executions[2].exit),
            Ok(Some(ClosedVmValue::Scalar(43)))
        );

        let expected_commands = [0, 1, 3, 4, 5];
        for (output, expected) in completed.outputs.iter().zip(expected_commands) {
            let actual = match output {
                SourceCommandOutput::Evaluation { command_index, .. }
                | SourceCommandOutput::Check { command_index, .. }
                | SourceCommandOutput::Example { command_index, .. } => *command_index,
            };
            assert_eq!(actual, expected);
        }
        let SourceCommandOutput::Check {
            check_index: first_check_index,
            ..
        } = &completed.outputs[0]
        else {
            panic!("command zero must retain its checked query"); // ubs:ignore — test-only diagnostic.
        };
        let first_check = &completed.checks[*first_check_index];
        assert_eq!(first_check.environment_root, before);
        let SourceCommandOutput::Check {
            check_index: answer_check_index,
            ..
        } = &completed.outputs[2]
        else {
            panic!("command three must retain its checked query"); // ubs:ignore — test-only diagnostic.
        };
        let answer_check = &completed.checks[*answer_check_index];
        assert_eq!(
            answer_check.environment_root,
            completed.batch.executions[1].result_logical_root
        );
        for output in &completed.outputs {
            let SourceCommandOutput::Check { check_index, .. } = output else {
                continue;
            };
            let check = &completed.checks[*check_index];
            let Declaration::Defn(query) = &check.declaration else {
                panic!("every source check candidate must be a definition"); // ubs:ignore — test-only diagnostic.
            };
            assert!(
                !completed
                    .batch
                    .engine
                    .environment()
                    .contains(&query.base.name),
                "scratch query rows must not escape into the final engine"
            );
        }
        assert_eq!(engine.logical_root(&options), before);

        let future = engine
            .execute_source_commands_with_checks(
                b"#check later\ndef later : Nat := 1",
                &options,
                test_limits(),
            )
            .expect_err("a query cannot observe a definition from a later command");
        assert!(matches!(
            future,
            EngineExecutionError::BatchCommand {
                index: 0,
                error,
                ..
            } if matches!(*error, EngineExecutionError::Frontend(_))
        ));
        assert_eq!(engine.logical_root(&options), before);

        let failed = engine
            .execute_source_commands_with_checks(
                b"#check Nat\n#eval 42\ndef retained : Nat := 7\n#check Missing",
                &options,
                test_limits(),
            )
            .expect_err("a late failed check exposes neither earlier output nor a successor");
        assert!(matches!(
            failed,
            EngineExecutionError::BatchCommand {
                index: 3,
                error,
                ..
            } if matches!(*error, EngineExecutionError::Frontend(_))
        ));
        assert_eq!(engine.logical_root(&options), before);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["retained"]))
        );

        assert!(matches!(
            engine
                .execute_source_commands_with_checks(
                    b"#check Nat\ndef recovered : Nat := 9\n#eval recovered",
                    &options,
                    test_limits(),
                )
                .expect("the unchanged engine recovers after the late query refusal"),
            Outcome::Complete(_)
        ));
    }

    #[test]
    fn terminal_source_check_observes_a_closed_definition_only_import_graph() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let before = engine.logical_root(&options);
        let base = Name::from_components(["Base"]);
        let middle = Name::from_components(["Middle"]);
        let main = Name::from_components(["Main"]);
        let modules = [
            SourceModuleInput {
                name: &main,
                source: b"import Middle\n#check middle",
            },
            SourceModuleInput {
                name: &base,
                source: b"def base : Nat := 40",
            },
            SourceModuleInput {
                name: &middle,
                source: b"import Base\ndef middle : Nat := base + 2",
            },
        ];

        let Outcome::Complete(checked) = engine
            .check_terminal_source_modules(&modules, &main, &options, test_limits())
            .expect("a terminal query observes its transitive checked import closure")
        else {
            panic!("the imported terminal source check was not complete"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(
            checked.source_module_order,
            [base.clone(), middle, main.clone()]
        );
        let prefix = checked
            .definition_prefix
            .as_ref()
            .expect("the dependency definitions are retained as the query prefix");
        assert_eq!(prefix.executions.len(), 2);
        assert_eq!(checked.check.environment_root, prefix.result_logical_root);
        assert_eq!(checked.check.checked_type, nat_type());
        assert!(
            prefix
                .engine
                .environment()
                .contains(&Name::from_components(["base"]))
        );
        assert!(
            prefix
                .engine
                .environment()
                .contains(&Name::from_components(["middle"]))
        );
        let Declaration::Defn(query) = &checked.check.declaration else {
            panic!("the imported query candidate must be a definition"); // ubs:ignore — test-only diagnostic.
        };
        assert!(
            !prefix.engine.environment().contains(&query.base.name),
            "the imported query row must remain in its discarded successor"
        );
        assert_eq!(engine.logical_root(&options), before);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["base"]))
        );

        let empty = Name::from_components(["Empty"]);
        let empty_graph = [
            SourceModuleInput {
                name: &empty,
                source: b"",
            },
            SourceModuleInput {
                name: &main,
                source: b"import Empty\n#check Nat",
            },
        ];
        let Outcome::Complete(empty_check) = engine
            .check_terminal_source_modules(&empty_graph, &main, &options, test_limits())
            .expect("an import graph with no definitions can still query the checked seed")
        else {
            panic!("the definition-free imported query was not complete"); // ubs:ignore — test-only diagnostic.
        };
        assert!(empty_check.definition_prefix.is_none());
        assert_eq!(
            empty_check.source_module_order,
            [empty.clone(), main.clone()]
        );
        assert_eq!(empty_check.check.environment_root, before);

        let evaluation_dependency = [
            SourceModuleInput {
                name: &base,
                source: b"#eval 1",
            },
            SourceModuleInput {
                name: &main,
                source: b"import Base\n#check Nat",
            },
        ];
        assert!(matches!(
            engine
                .check_terminal_source_modules(
                    &evaluation_dependency,
                    &main,
                    &options,
                    test_limits(),
                )
                .expect_err("an imported query cannot execute dependency evaluations"),
            EngineExecutionError::TerminalCheckModuleDefinitionPrefix {
                module,
                index: 0,
            } if module == base
        ));

        let unknown_modules = [
            SourceModuleInput {
                name: &base,
                source: b"def base : Nat := 40",
            },
            SourceModuleInput {
                name: &main,
                source: b"import Base\n#check Missing",
            },
        ];
        assert!(matches!(
            engine
                .check_terminal_source_modules(
                    &unknown_modules,
                    &main,
                    &options,
                    test_limits(),
                )
                .expect_err("a refused query exposes no completed dependency engine"),
            EngineExecutionError::BatchCommand { index: 1, error, .. }
                if matches!(*error, EngineExecutionError::Frontend(_))
        ));
        assert_eq!(engine.logical_root(&options), before);

        let term = fln_checker::term::TermBudget::new(0, 0).with_max_arena_nodes(0);
        let whnf = fln_checker::whnf::WhnfBudget::new(0, 0, term);
        let inference = fln_checker::infer::InferenceBudget::new(0, 0, term, term).with_whnf(whnf);
        let mut constrained = test_limits();
        constrained.checker.admission =
            CheckerAdmissionBudget::new(inference, whnf, inference.defeq);
        assert!(matches!(
            engine
                .check_terminal_source_modules(&empty_graph, &main, &options, constrained)
                .expect_err("an independent-checker non-answer vetoes an imported query"),
            EngineExecutionError::BatchCommand { index: 0, error, .. }
                if matches!(*error, EngineExecutionError::CouncilNoAnswer { .. })
        ));
        assert_eq!(engine.logical_root(&options), before);
        assert!(matches!(
            engine
                .check_terminal_source_modules(&empty_graph, &main, &options, test_limits())
                .expect("the unchanged engine recovers after imported-query refusals"),
            Outcome::Complete(_)
        ));
    }

    #[test]
    fn mixed_entry_commands_observe_silent_dependency_evaluations() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let before = engine.logical_root(&options);
        let base = Name::from_components(["Base"]);
        let middle = Name::from_components(["Middle"]);
        let main = Name::from_components(["Main"]);
        let provider = Name::from_components(["A"]);
        let consumer = Name::from_components(["B"]);
        let modules = [
            SourceModuleInput {
                name: &main,
                source: b"import Middle\n#check middle\n#eval middle\ndef answer : Nat := middle + 1\n#check answer\n#eval answer",
            },
            SourceModuleInput {
                name: &base,
                source: b"#eval 99\ndef base : Nat := 40",
            },
            SourceModuleInput {
                name: &middle,
                source: b"import Base\ndef middle : Nat := base + 2",
            },
        ];

        let Outcome::Complete(completed) = engine
            .execute_source_modules_with_entry_checks(&modules, &main, &options, test_limits())
            .expect("the mixed entry observes its deterministic dependency environment")
        else {
            panic!("the mixed imported source stream must answer completely"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(
            completed.source_module_order,
            [base.clone(), middle, main.clone()]
        );
        let dependency_prefix = completed
            .dependency_prefix
            .as_ref()
            .expect("the imported commands execute before the entry");
        assert_eq!(completed.dependency_command_count, 3);
        assert_eq!(completed.dependency_execution_command_indices, [0, 1, 2]);
        assert_eq!(dependency_prefix.executions.len(), 3);
        assert_eq!(dependency_prefix.source_evaluation_indices, [0]);
        assert_eq!(
            closed_vm_value(&dependency_prefix.executions[0].exit),
            Ok(Some(ClosedVmValue::Scalar(99)))
        );
        assert_eq!(completed.entry.command_count, 5);
        assert_eq!(completed.entry.execution_command_indices, [1, 2, 4]);
        assert_eq!(completed.entry.batch.source_evaluation_indices, [0, 2]);
        assert_eq!(completed.entry.outputs.len(), 4);
        assert_eq!(completed.entry.checks.len(), 2);
        assert_eq!(
            completed.entry.batch.base_logical_root,
            dependency_prefix.result_logical_root
        );
        assert_eq!(
            closed_vm_value(&completed.entry.batch.executions[0].exit),
            Ok(Some(ClosedVmValue::Scalar(42)))
        );
        assert_eq!(
            closed_vm_value(&completed.entry.batch.executions[2].exit),
            Ok(Some(ClosedVmValue::Scalar(43)))
        );
        assert_eq!(
            completed.entry.checks[0].environment_root,
            dependency_prefix.result_logical_root
        );
        assert_eq!(
            completed.entry.checks[1].environment_root,
            completed.entry.batch.executions[1].result_logical_root
        );
        assert_eq!(
            completed.entry.batch.engine.environment().len(),
            dependency_prefix.engine.environment().len() + completed.entry.batch.executions.len(),
            "scratch checks cannot add rows to the retained entry successor"
        );
        for check in &completed.entry.checks {
            let Declaration::Defn(_) = &check.declaration else {
                panic!("each imported-entry query candidate must be a definition"); // ubs:ignore — test-only diagnostic.
            };
        }
        assert_eq!(engine.logical_root(&options), before);

        let future_modules = [
            SourceModuleInput {
                name: &main,
                source: b"import Base\n#check later\ndef later : Nat := base",
            },
            SourceModuleInput {
                name: &base,
                source: b"def base : Nat := 40",
            },
        ];
        assert!(matches!(
            engine
                .execute_source_modules_with_entry_checks(
                    &future_modules,
                    &main,
                    &options,
                    test_limits(),
                )
                .expect_err("an entry check cannot observe a later entry definition"),
            EngineExecutionError::BatchCommand {
                index: 0,
                error,
                ..
            } if matches!(*error, EngineExecutionError::Frontend(_))
        ));
        assert_eq!(engine.logical_root(&options), before);

        let leaking_evaluation = [
            SourceModuleInput {
                name: &main,
                source: b"import A\nimport B\n#check visible",
            },
            SourceModuleInput {
                name: &provider,
                source: b"def leaked : Nat := 40",
            },
            SourceModuleInput {
                name: &consumer,
                source: b"#eval leaked\ndef visible : Nat := 42",
            },
        ];
        assert!(matches!(
            engine
                .execute_source_modules_with_entry_checks(
                    &leaking_evaluation,
                    &main,
                    &options,
                    test_limits(),
                )
                .expect_err("a dependency evaluation cannot borrow an unimported sibling"),
            EngineExecutionError::SourceModuleVisibility {
                ref module,
                ref referenced,
                ref owner,
                ..
            } if module == &consumer
                && referenced == &Name::from_components(["leaked"])
                && owner == &provider
        ));
        assert_eq!(engine.logical_root(&options), before);

        let checked_dependency = [
            SourceModuleInput {
                name: &main,
                source: b"import Base\n#check base",
            },
            SourceModuleInput {
                name: &base,
                source: b"#check Nat\ndef base : Nat := 40",
            },
        ];
        let Outcome::Complete(checked_dependency) = engine
            .execute_source_modules_with_entry_checks(
                &checked_dependency,
                &main,
                &options,
                test_limits(),
            )
            .expect("the imported scratch check uses the module visibility path")
        else {
            panic!("the imported scratch check must answer completely"); // ubs:ignore — test-only diagnostic.
        };
        let checked_prefix = checked_dependency
            .dependency_prefix
            .as_ref()
            .expect("the definition after the dependency check is published");
        assert_eq!(checked_dependency.dependency_command_count, 2);
        assert_eq!(checked_dependency.dependency_execution_command_indices, [1]);
        assert_eq!(checked_prefix.executions.len(), 1);
        assert_eq!(
            checked_prefix.engine.environment().len(),
            engine.environment().len() + 1,
            "the imported scratch check cannot add a retained environment row"
        );
        assert_eq!(checked_dependency.entry.checks.len(), 1);
        assert_eq!(
            checked_dependency.entry.checks[0].environment_root,
            checked_prefix.result_logical_root
        );
        assert_eq!(engine.logical_root(&options), before);

        let future_dependency = [
            SourceModuleInput {
                name: &main,
                source: b"import Base\n#check later",
            },
            SourceModuleInput {
                name: &base,
                source: b"#check later\ndef later : Nat := 40",
            },
        ];
        assert!(matches!(
            engine
                .execute_source_modules_with_entry_checks(
                    &future_dependency,
                    &main,
                    &options,
                    test_limits(),
                )
                .expect_err("a dependency check cannot observe its later definition"),
            EngineExecutionError::BatchCommand { index: 0, error, .. }
                if matches!(*error, EngineExecutionError::Frontend(_))
        ));
        assert_eq!(engine.logical_root(&options), before);

        let leaking_check = [
            SourceModuleInput {
                name: &main,
                source: b"import A\nimport B\n#check leaked",
            },
            SourceModuleInput {
                name: &provider,
                source: b"def leaked : Nat := 40",
            },
            SourceModuleInput {
                name: &consumer,
                source: b"#check leaked\ndef visible : Nat := 42",
            },
        ];
        assert!(matches!(
            engine
                .execute_source_modules_with_entry_checks(
                    &leaking_check,
                    &main,
                    &options,
                    test_limits(),
                )
                .expect_err("a dependency check cannot borrow an unimported sibling"),
            EngineExecutionError::SourceModuleVisibility {
                ref module,
                ref referenced,
                ref owner,
                ..
            } if module == &consumer
                && referenced == &Name::from_components(["leaked"])
                && owner == &provider
        ));
        assert_eq!(engine.logical_root(&options), before);
    }

    #[test]
    fn mixed_source_modules_allow_a_silent_import_only_entry() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let before = engine.logical_root(&options);
        let base = Name::from_components(["Base"]);
        let main = Name::from_components(["Main"]);
        let modules = [
            SourceModuleInput {
                name: &main,
                source: b"import Base\n",
            },
            SourceModuleInput {
                name: &base,
                source: b"#check Nat\n#eval 7\ndef imported : Nat := 7",
            },
        ];

        let Outcome::Complete(completed) = engine
            .execute_source_modules_with_entry_checks(&modules, &main, &options, test_limits())
            .expect("an import-only entry completes after its checked dependency closure")
        else {
            panic!("the import-only entry must answer completely"); // ubs:ignore — test-only diagnostic.
        };
        assert_eq!(completed.source_module_order, [base, main]);
        assert_eq!(completed.dependency_command_count, 3);
        assert_eq!(completed.dependency_execution_command_indices, [1, 2]);
        let prefix = completed
            .dependency_prefix
            .as_ref()
            .expect("the dependency executes without becoming entry output");
        assert_eq!(prefix.executions.len(), 2);
        assert_eq!(prefix.source_evaluation_indices, [0]);
        assert_eq!(completed.entry.command_count, 0);
        assert!(completed.entry.batch.executions.is_empty());
        assert!(completed.entry.execution_command_indices.is_empty());
        assert!(completed.entry.outputs.is_empty());
        assert!(completed.entry.checks.is_empty());
        assert_eq!(
            completed.entry.batch.base_logical_root,
            prefix.result_logical_root
        );
        assert_eq!(
            completed.entry.batch.result_logical_root,
            prefix.result_logical_root
        );
        assert_eq!(
            completed.entry.batch.engine.environment().len(),
            prefix.engine.environment().len()
        );
        assert_eq!(engine.logical_root(&options), before);
    }

    #[test]
    fn nat_add_logical_model_passes_both_checkers_for_symbolic_equations() {
        let limits = EngineAdmissionLimits::new(test_budget());
        let engine = Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap();
        let options = KVMap::new();
        let before = engine.logical_root(&options);
        let n = Expr::bvar(0).unwrap();
        let literal = |value| Expr::lit(Literal::Nat(NatLit::from_u64(value)));
        let add = |left, right| {
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_components(["Nat", "add"]), vec![]),
                    left,
                ),
                right,
            )
        };
        let proof = |label, left, right: Expr| {
            let equality = [nat_type(), left, right.clone()].into_iter().fold(
                Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]),
                Expr::app,
            );
            let reflexivity = [nat_type(), right].into_iter().fold(
                Expr::const_(Name::from_components(["Eq", "refl"]), vec![Level::one()]),
                Expr::app,
            );
            theorem(
                label,
                Expr::forall_e(
                    Name::from_components(["n"]),
                    nat_type(),
                    equality,
                    BinderInfo::Default,
                ),
                Expr::lam(
                    Name::from_components(["n"]),
                    nat_type(),
                    reflexivity,
                    BinderInfo::Default,
                ),
            )
        };
        // These proofs bypass elaboration entirely. The logical model must
        // reach K1 and the independent checker, not just a unifier shortcut.
        for (label, left, right) in [
            ("zeroRight", add(n.clone(), literal(0)), n.clone()),
            (
                "nestedOffsets",
                add(add(n.clone(), literal(2)), literal(3)),
                add(n.clone(), literal(5)),
            ),
            (
                "successorOffset",
                add(n.clone(), literal(1)),
                Expr::app(
                    Expr::const_(Name::from_components(["Nat", "succ"]), vec![]),
                    n.clone(),
                ),
            ),
        ] {
            engine
                .admit_declaration(proof(label, left, right), &options, limits)
                .unwrap_or_else(|error| panic!("{label}: {error:?}"))
                .into_complete()
                .expect("both checkers certify symbolic Nat.add computation");
        }
        engine
            .admit_declaration(
                proof("wrongOffset", add(n.clone(), literal(1)), n),
                &options,
                limits,
            )
            .expect_err("unequal symbolic offsets must remain rejected");
        assert_eq!(engine.logical_root(&options), before);
        assert!(matches!(
            engine
                .environment()
                .find(&Name::from_components(["Nat", "add"])),
            Some(ConstantInfo::Defn(_))
        ));
        assert_eq!(
            fln_elab::reducibility::table(engine.environment())
                .unwrap()
                .status(&Name::from_components(["Nat", "add"])),
            fln_elab::reducibility::Reducibility::ImplicitReducible,
        );
    }

    #[test]
    fn checked_nat_add_source_reaches_the_existing_intrinsic_runtime() {
        let options = KVMap::new();
        let nat_only = seeded_engine();
        let base_root = nat_only.logical_root(&options);
        let missing = nat_only
            .execute_source_definition(b"def answer := Nat.add 40 2", &options, test_limits())
            .expect_err("the Nat-only seed must not invent the Nat.add constant");
        // An elaboration error, as at the pin: a `prelude` file declaring only `Nat` gets
        // `error(lean.unknownIdentifier): Unknown constant `Nat.add`` (v4.32.0, 2026-10-05).
        assert_eq!(
            unknown_name_message(&missing).as_deref(),
            Some("Unknown constant `Nat.add`"),
            "{missing:?}"
        );
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
    fn ordinary_infix_source_reaches_checked_flbc_and_golem_with_pin_grouping() {
        let options = KVMap::new();
        let nat_only = seeded_engine();
        let base_root = nat_only.logical_root(&options);
        let missing = nat_only
            .execute_source_definition(b"def answer := 40 + 2", &options, test_limits())
            .expect_err("notation must not invent Nat.add authority");
        // An elaboration error. The pin's `prelude` analog (only `Nat` declared) stops one step
        // earlier, at `Unknown constant `OfNat``, because its numerals elaborate through
        // `OfNat`; this seed's numerals are native, so the first missing constant is `Nat.add`.
        assert_eq!(
            unknown_name_message(&missing).as_deref(),
            Some("Unknown constant `Nat.add`"),
            "{missing:?}"
        );
        assert_eq!(nat_only.logical_root(&options), base_root);
        let missing_equality = nat_only
            .execute_source_definition(b"def equal : Bool := 40 == 42", &options, test_limits())
            .expect_err("notation must not invent Nat.beq authority");
        // An elaboration error at the first missing name, the annotation's `Bool`. The pin has
        // no faithful analog: without `Init`, `==` is not even a token (a `prelude` file
        // declaring only `Nat` gets `Unknown constant `OfNat`` and `expected token`).
        assert_eq!(
            unknown_name_message(&missing_equality).as_deref(),
            Some("Unknown identifier `Bool`"),
            "{missing_equality:?}"
        );
        assert_eq!(nat_only.logical_root(&options), base_root);

        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let completed = engine
            .execute_source_definitions(
                &[
                    b"def precedence := 2 + 3 * 4",
                    b"def subtraction := 20 - 3 - 2",
                    b"def exponent := 2 ^ 3 ^ 2",
                    b"def grouped := (2 + 3) * 4",
                    b"def bits := 12 &&& 10 ||| 1",
                    b"def text := \"franken\" ++ \"lean\"",
                    b"def natEqual := 40 + 2 == 42",
                    b"def natUnequal := 40 + 1 == 42",
                    b"def stringEqual := text == \"frankenlean\"",
                    b"def stringUnequal := text == \"franken_lean\"",
                ],
                &options,
                test_limits(),
            )
            .expect("ordinary bounded infix source reaches checked execution");
        let Outcome::Complete(completed) = completed else {
            panic!("bounded infix execution must answer completely");
        };
        let expected = [
            ClosedVmValue::Scalar(14),
            ClosedVmValue::Scalar(15),
            ClosedVmValue::Scalar(512),
            ClosedVmValue::Scalar(20),
            ClosedVmValue::Scalar(9),
            ClosedVmValue::String("frankenlean".to_owned()),
            ClosedVmValue::Scalar(1),
            ClosedVmValue::Scalar(0),
            ClosedVmValue::Scalar(1),
            ClosedVmValue::Scalar(0),
        ];
        assert_eq!(completed.executions.len(), expected.len());
        for (execution, expected) in completed.executions.iter().zip(expected) {
            assert_eq!(closed_vm_value(&execution.exit), Ok(Some(expected)));
            assert!(!execution.flbc_artifact.is_empty());
            fln_comp::flbc::decode_canonical(&execution.flbc_artifact, CodecLimits::default())
                .expect("every exact executed infix artifact decodes canonically");
        }
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
        // As at the pin: a `prelude` file declaring only `Nat` gets
        // `Unknown constant `Nat.pred`` (v4.32.0, 2026-10-05).
        assert_eq!(
            unknown_name_message(&missing).as_deref(),
            Some("Unknown constant `Nat.pred`"),
            "{missing:?}"
        );
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
        // As at the pin: a `prelude` file declaring only `Nat` gets
        // `Unknown constant `Nat.log2`` (v4.32.0, 2026-10-05).
        assert_eq!(
            unknown_name_message(&missing).as_deref(),
            Some("Unknown constant `Nat.log2`"),
            "{missing:?}"
        );
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
        // As at the pin: a `prelude` file declaring `Nat` and `String` gets
        // `Unknown constant `String.append`` (v4.32.0, 2026-10-05).
        assert_eq!(
            unknown_name_message(&missing).as_deref(),
            Some("Unknown constant `String.append`"),
            "{missing:?}"
        );
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
        // As at the pin: a `prelude` file declaring `Nat` and `String` gets
        // `Unknown constant `String.length`` (v4.32.0, 2026-10-05).
        assert_eq!(
            unknown_name_message(&missing).as_deref(),
            Some("Unknown constant `String.length`"),
            "{missing:?}"
        );
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
        // As at the pin: a `prelude` file declaring `Nat` and `String` gets
        // `Unknown constant `Nat.beq`` (v4.32.0, 2026-10-05).
        assert_eq!(
            unknown_name_message(&missing).as_deref(),
            Some("Unknown constant `Nat.beq`"),
            "{missing:?}"
        );
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
    fn checked_bool_literals_reach_golem_through_exact_constructor_rows() {
        let options = KVMap::new();
        let nat_only = seeded_engine();
        let missing = nat_only
            .execute_source_definition(b"def answer := true", &options, test_limits())
            .expect_err("the Nat-only door must not invent Bool constructor authority");
        // An elaboration error. The pin's `prelude` analog (only `Nat` declared) says
        // `Unknown identifier `true``; this door names the constructor it resolved `true` to.
        assert_eq!(
            unknown_name_message(&missing).as_deref(),
            Some("Unknown identifier `Bool.true`"),
            "{missing:?}"
        );

        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the exact Bool block passes the dual-checker council")
            .into_complete()
            .expect("the bounded Bool source seed answers completely");
        assert!(matches!(
            engine
                .environment()
                .find(&Name::from_components(["Bool", "false"])),
            Some(ConstantInfo::Ctor(constructor)) if constructor.cidx == 0
        ));
        assert!(matches!(
            engine
                .environment()
                .find(&Name::from_components(["Bool", "true"])),
            Some(ConstantInfo::Ctor(constructor)) if constructor.cidx == 1
        ));

        let completed = engine
            .execute_source_definitions(
                &[
                    b"def yes := true",
                    b"def no := Bool.false",
                    b"def keep (flag : Bool) : Bool := flag",
                    b"def answer := keep yes",
                ],
                &options,
                test_limits(),
            )
            .expect("checked Bool constructors and a Bool parameter reach Golem");
        let Outcome::Complete(completed) = completed else {
            panic!("the checked Bool literal batch must answer completely");
        };
        assert_eq!(completed.executions.len(), 4);
        assert_eq!(
            closed_vm_value(&completed.executions[0].exit),
            Ok(Some(ClosedVmValue::Scalar(1)))
        );
        assert_eq!(
            closed_vm_value(&completed.executions[1].exit),
            Ok(Some(ClosedVmValue::Scalar(0)))
        );
        assert_eq!(
            closed_vm_value(&completed.executions[3].exit),
            Ok(Some(ClosedVmValue::Scalar(1)))
        );

        for (execution, expected) in [
            (&completed.executions[0], 1_u64),
            (&completed.executions[1], 0_u64),
        ] {
            let executable =
                fln_comp::flbc::decode_canonical(&execution.flbc_artifact, CodecLimits::default())
                    .expect("the Bool constructor artifact decodes canonically");
            assert!(matches!(
                &executable.functions()[0].code[0],
                fln_comp::flbc::Instruction::Nat { value, .. } if *value == expected
            ));
        }
    }

    #[test]
    fn scalar_bool_compiler_binding_requires_the_exact_seed_constructor_row() {
        let Declaration::Inductive(block) = fln_elab::seed::bool_seed_declaration() else {
            panic!("the source seed must expose the exact Bool block");
        };
        let exact = block.ctors[1].clone();
        let name = exact.base.name.clone();
        let exact_environment = Environment::new()
            .add_decl(ConstantInfo::Ctor(exact.clone()))
            .expect("the exact constructor row enters the isolated fixture");
        assert_eq!(
            source_scalar_constructor_binding(&exact_environment, &name),
            Some(ScalarConstructorBinding {
                name: name.clone(),
                universe_arity: 0,
                value: true,
            })
        );

        let mut forged = exact;
        forged.cidx = 0;
        let forged_environment = Environment::new()
            .add_decl(ConstantInfo::Ctor(forged))
            .expect("the untrusted imported fixture can carry a forged row");
        assert_eq!(
            source_scalar_constructor_binding(&forged_environment, &name),
            None,
            "a Bool.true spelling cannot grant scalar true authority to a nonmatching row"
        );
    }

    #[test]
    fn checked_global_named_true_remains_an_ordinary_nat_definition() {
        let options = KVMap::new();
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the exact Bool block passes the dual-checker council")
            .into_complete()
            .expect("the bounded Bool source seed answers completely");
        let completed = engine
            .execute_source_definitions(
                &[b"def true : Nat := 7", b"def answer := Nat.add true 1"],
                &options,
                test_limits(),
            )
            .expect("a checked exact global named true wins ordinary name resolution");
        let Outcome::Complete(completed) = completed else {
            panic!("the ordinary true-name batch must answer completely");
        };
        assert_eq!(
            closed_vm_value(&completed.executions[1].exit),
            Ok(Some(ClosedVmValue::Scalar(8)))
        );
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
                    b"def answer := 40 + 2",
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
                    b"def message := \"ordinary\" ++ \"ignored\" ++ \"intrinsic\"",
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
            .expect_err("an explicit let type is checked against its value");
        // `String` against `Nat` is a rigid mismatch: refused at elaboration, as the pinned
        // lean does ("Type mismatch \"wrong\" has type String but is expected to have type
        // Nat", fln-azxg), never handed to K1 as a typed body.
        assert!(
            matches!(
                &mismatch,
                EngineExecutionError::Frontend(super::DefinitionFrontendError::Elaborate(
                    fln_elab::NatDefinitionElabError::Inference(
                        fln_elab::source::SourceInferenceError::TypeMismatch { .. }
                    )
                ))
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
                ..
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
    fn closed_source_modules_derive_import_order_and_execute_the_entry_last() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let main = Name::from_components(["Main"]);
        let middle = Name::from_components(["Project", "Middle"]);
        let base = Name::from_components(["Project", "Base"]);
        let modules = [
            SourceModuleInput {
                name: &main,
                source: b"import Project.Middle\ndef answer : Nat := Nat.add middle 1",
            },
            SourceModuleInput {
                name: &base,
                source: b"def base : Nat := 20",
            },
            SourceModuleInput {
                name: &middle,
                source: b"import Project.Base\ndef middle : Nat := Nat.mul base 2",
            },
        ];

        let completed = engine
            .execute_source_modules(&modules, &main, &options, test_limits())
            .expect("the exact closed source graph reaches the native pipeline");
        let Outcome::Complete(completed) = completed else {
            panic!("the bounded source graph must answer completely");
        };

        let names = completed
            .executions
            .iter()
            .map(|execution| match &execution.declaration {
                Declaration::Defn(definition) => definition.base.name.to_display_string(),
                other => panic!("source execution produced non-definition {other:?}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["base", "middle", "answer"]);
        assert_eq!(completed.source_module_order, [base, middle, main]);
        let VmExit::Returned(returned) = &completed.executions[2].exit else {
            panic!("the entry definition must return normally");
        };
        assert_eq!(returned.value.unbox(), 41);
        assert!(
            completed
                .engine
                .environment()
                .contains(&Name::from_components(["answer"]))
        );
    }

    #[test]
    fn closed_source_modules_require_a_supported_command_in_the_entry_only() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let main = Name::from_components(["Main"]);
        let dependency = Name::from_components(["Dependency"]);
        let empty_entry = [
            SourceModuleInput {
                name: &main,
                source: b"import Dependency\n",
            },
            SourceModuleInput {
                name: &dependency,
                source: b"def dependency : Nat := 42",
            },
        ];
        let base_root = engine.logical_root(&options);

        let error = engine
            .execute_source_modules(&empty_entry, &main, &options, test_limits())
            .expect_err("a dependency result must not masquerade as the entry product");
        assert_eq!(
            error,
            EngineExecutionError::EmptySourceEntry {
                module: main.clone(),
            }
        );
        assert_eq!(
            error.to_string(),
            "source entry module `Main` contains no supported command to execute"
        );
        assert_eq!(engine.logical_root(&options), base_root);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["dependency"]))
        );

        let empty_dependency = [
            SourceModuleInput {
                name: &main,
                source: b"import Dependency\ndef answer : Nat := 42",
            },
            SourceModuleInput {
                name: &dependency,
                source: b"",
            },
        ];
        let completed = engine
            .execute_source_modules(&empty_dependency, &main, &options, test_limits())
            .expect("only the entry needs an executable product")
            .into_complete()
            .expect("the repaired entry answers completely");
        assert_eq!(completed.executions.len(), 1);
        assert_eq!(completed.source_module_order, [dependency, main]);
        assert!(matches!(completed.executions[0].exit, VmExit::Returned(_)));
        if let VmExit::Returned(returned) = &completed.executions[0].exit {
            assert_eq!(returned.value.unbox(), 42);
        }
    }

    #[test]
    fn source_modules_cannot_borrow_declarations_from_unimported_siblings() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let main = Name::from_components(["Main"]);
        let provider = Name::from_components(["A"]);
        let consumer = Name::from_components(["B"]);
        let leaking = [
            SourceModuleInput {
                name: &main,
                source: b"import A\nimport B\ndef answer : Nat := Nat.add borrowed 1",
            },
            SourceModuleInput {
                name: &provider,
                source: b"def leaked : Nat := 40",
            },
            SourceModuleInput {
                name: &consumer,
                source: b"def borrowed : Nat := Nat.add leaked 1",
            },
        ];
        let base_root = engine.logical_root(&options);

        let error = engine
            .execute_source_modules(&leaking, &main, &options, test_limits())
            .expect_err("topological order must not grant one sibling visibility into another");
        assert_eq!(
            error,
            EngineExecutionError::SourceModuleVisibility {
                module: consumer.clone(),
                declaration: Name::from_components(["borrowed"]),
                referenced: Name::from_components(["leaked"]),
                owner: provider.clone(),
            }
        );
        assert_eq!(engine.logical_root(&options), base_root);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["borrowed"]))
        );

        let closed = [
            SourceModuleInput {
                name: &main,
                source: b"import B\ndef answer : Nat := Nat.add leaked 2",
            },
            SourceModuleInput {
                name: &provider,
                source: b"def leaked : Nat := 40",
            },
            SourceModuleInput {
                name: &consumer,
                source: b"import A\ndef borrowed : Nat := Nat.add leaked 1",
            },
        ];
        let completed = engine
            .execute_source_modules(&closed, &main, &options, test_limits())
            .expect("adding the missing transitive import repairs the same source closure")
            .into_complete()
            .expect("the repaired source closure answers completely");
        assert_eq!(completed.source_module_order, [provider, consumer, main]);
        let VmExit::Returned(returned) = &completed.executions[2].exit else {
            panic!("the repaired entry definition must return normally");
        };
        assert_eq!(returned.value.unbox(), 42);
    }

    #[test]
    fn source_module_visibility_scan_is_bounded_and_recoverable() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the bounded source seed reaches both council seats")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let main = Name::from_components(["Main"]);
        let dependency = Name::from_components(["Dependency"]);
        let modules = [
            SourceModuleInput {
                name: &main,
                source: b"import Dependency\ndef answer : Nat := dependency",
            },
            SourceModuleInput {
                name: &dependency,
                source: b"def dependency : Nat := 7",
            },
        ];
        let mut exhausted = test_limits();
        exhausted.source_modules.max_dependency_presentations = 0;

        assert_eq!(
            engine
                .execute_source_modules(&modules, &main, &options, exhausted)
                .expect_err("zero visibility presentations is a typed resource stop"),
            EngineExecutionError::SourceDependencyPresentationLimit {
                observed: 1,
                limit: 0,
            }
        );
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["answer"]))
        );

        assert!(matches!(
            engine.execute_source_modules(&modules, &main, &options, test_limits()),
            Ok(Outcome::Complete(_))
        ));
    }

    #[test]
    fn unresolved_source_imports_never_enter_the_legacy_ordered_batch() {
        let engine = seeded_engine();
        let imports: [&[u8]; 1] = [b"import Missing\ndef answer := 1"];
        let error = engine
            .execute_source_definitions(&imports, &KVMap::new(), test_limits())
            .expect_err("an ordered byte batch is not import resolver authority");
        assert!(matches!(
            error,
            EngineExecutionError::ImportsRequireResolver { imports }
                if imports == vec![Name::from_components(["Missing"])]
        ));
        assert_eq!(engine.environment().len(), 1);
    }

    #[test]
    fn closed_source_modules_refuse_missing_duplicate_cyclic_and_unused_rows() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let main = Name::from_components(["Main"]);
        let other = Name::from_components(["Other"]);
        let missing = [SourceModuleInput {
            name: &main,
            source: b"import Absent\ndef answer := 1",
        }];
        assert!(matches!(
            engine.execute_source_modules(&missing, &main, &options, test_limits()),
            Err(EngineExecutionError::MissingSourceImports { module, imports })
                if module == main && imports == vec![Name::from_components(["Absent"])]
        ));
        let empty_missing = [SourceModuleInput {
            name: &main,
            source: b"import Absent\n",
        }];
        assert!(matches!(
            engine.execute_source_modules(&empty_missing, &main, &options, test_limits()),
            Err(EngineExecutionError::MissingSourceImports { module, imports })
                if module == main && imports == vec![Name::from_components(["Absent"])]
        ));

        let duplicate = [
            SourceModuleInput {
                name: &main,
                source: b"def first := 1",
            },
            SourceModuleInput {
                name: &main,
                source: b"def second := 2",
            },
        ];
        assert!(matches!(
            engine.execute_source_modules(&duplicate, &main, &options, test_limits()),
            Err(EngineExecutionError::DuplicateSourceModule { module }) if module == main
        ));

        let cycle = [
            SourceModuleInput {
                name: &main,
                source: b"import Other\ndef answer := other",
            },
            SourceModuleInput {
                name: &other,
                source: b"import Main\ndef other := answer",
            },
        ];
        assert!(matches!(
            engine.execute_source_modules(&cycle, &main, &options, test_limits()),
            Err(EngineExecutionError::SourceModuleCycle { modules }) if modules.len() == 2
        ));

        let unused = [
            SourceModuleInput {
                name: &main,
                source: b"def answer := 1",
            },
            SourceModuleInput {
                name: &other,
                source: b"def other := 2",
            },
        ];
        assert!(matches!(
            engine.execute_source_modules(&unused, &main, &options, test_limits()),
            Err(EngineExecutionError::UnreachableSourceModules { entry, modules })
                if entry == main && modules == vec![other]
        ));
        assert_eq!(engine.environment().len(), 1);
    }

    #[test]
    fn closed_source_module_planning_limits_are_typed_and_recoverable() {
        let engine = seeded_engine();
        let options = KVMap::new();
        let main = Name::from_components(["Main"]);
        let dependency = Name::from_components(["Dependency"]);
        let modules = [
            SourceModuleInput {
                name: &main,
                source: b"import Dependency\ndef answer := dependency",
            },
            SourceModuleInput {
                name: &dependency,
                source: b"def dependency := 7",
            },
        ];
        let mut limited = test_limits();
        limited.source_modules.max_imports = 0;
        assert_eq!(
            engine
                .execute_source_modules(&modules, &main, &options, limited)
                .expect_err("zero import presentations is an explicit planning stop"),
            EngineExecutionError::SourceImportLimit {
                observed: 1,
                limit: 0,
            }
        );
        assert_eq!(engine.environment().len(), 1);

        let completed = engine
            .execute_source_modules(&modules, &main, &options, test_limits())
            .expect("the same graph recovers under the ordinary bound");
        assert!(matches!(completed, Outcome::Complete(_)));

        let hierarchical = Name::from_components(["Project", "Dependency"]);
        let hierarchical_modules = [
            SourceModuleInput {
                name: &main,
                source: b"import Project.Dependency\ndef answer := dependency",
            },
            SourceModuleInput {
                name: &hierarchical,
                source: b"def dependency := 7",
            },
        ];
        let mut shallow = test_limits();
        shallow.source_modules.max_name_depth = 1;
        assert!(matches!(
            engine.execute_source_modules(&hierarchical_modules, &main, &options, shallow),
            Err(EngineExecutionError::SourceModuleNameLimit {
                module,
                observed: 2,
                limit: 1,
            }) if module == hierarchical
        ));
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
                ..
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
                ..
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

    /// End-to-end test that the bounded source's new `<=` and `<` infix
    /// spellings reach the VM and produce the right Bool. Exercises the full
    /// source → K1 → independent checker → FIR → FLBC → Golem path with the
    /// decision-procedure extern rows that were previously unbridged in the
    /// bounded source bridge.
    #[test]
    fn bounded_source_supports_nat_le_and_lt_infix_end_to_end() {
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(test_budget()))
            .expect("the source seed passes the dual-checker council")
            .into_complete()
            .expect("the bounded source seed answers completely");
        let options = KVMap::new();
        let sources: [&[u8]; 5] = [
            b"def lt_pos : Bool := 1 < 2",
            b"def lt_eq : Bool := 2 < 2",
            b"def le_pos : Bool := 1 <= 2",
            b"def le_eq : Bool := 2 <= 2",
            b"def le_neg : Bool := 3 <= 2",
        ];
        let completed = engine
            .execute_source_definitions(&sources, &options, test_limits())
            .expect("the bounded source reaches Golem for every comparison shape")
            .into_complete()
            .expect("the bounded batch answers completely");
        let vm_exits: Vec<_> = completed
            .executions
            .iter()
            .map(|execution| {
                let VmExit::Returned(returned) = &execution.exit else {
                    panic!("the bounded comparison must return normally");
                };
                assert_eq!(value_kind(&returned.value), ValueKind::Scalar);
                let scalar = returned.value.unbox();
                assert!(
                    scalar == 0 || scalar == 1,
                    "Bool must be 0 or 1, got {scalar}"
                );
                scalar
            })
            .collect();
        assert_eq!(vm_exits, vec![1, 0, 1, 1, 0], "1<2, 2<2, 1<=2, 2<=2, 3<=2");
        // The published engine now holds every comparison; the seed
        // additionally exposes Nat.decLe and Nat.decLt by name.
        assert!(
            engine.environment().len() <= completed.engine.environment().len(),
            "the published snapshot must extend the seed"
        );
        assert!(
            completed
                .engine
                .environment()
                .contains(&Name::from_components(["lt_pos"]))
        );
    }

    /// fln-32rr: shared subterms are presented once. The term doubles one node
    /// 64 times, so as a tree it has 2^65 - 1 nodes; as a DAG, 65.
    #[test]
    fn constant_references_present_each_shared_node_once() {
        let mut term = Expr::const_(Name::from_components(["shared"]), Vec::new());
        for _ in 0..64 {
            term = Expr::app(term.clone(), term);
        }
        let mut names = std::collections::BTreeSet::new();
        let mut presentations = 0;
        assert_eq!(
            super::collect_constant_references(&term, &mut names, &mut presentations, 65),
            Ok(())
        );
        assert_eq!(presentations, 65);
        assert_eq!(
            names.into_iter().collect::<Vec<_>>(),
            [Name::from_components(["shared"])]
        );
        let mut presentations = 0;
        assert_eq!(
            super::collect_constant_references(
                &term,
                &mut std::collections::BTreeSet::new(),
                &mut presentations,
                64
            ),
            Err(super::ConstantReferenceCollectionError::PresentationLimit {
                observed: 65,
                limit: 64
            }),
            "the limit still bounds distinct nodes"
        );
    }

    /// A refused host allocation inside one module's check is that module's typed
    /// non-answer, and the process goes on (fln-frontier-oom-abort-w9dx). The
    /// allocation really fails: the test re-runs itself under a 4 GiB address-space
    /// limit (`prlimit --as`), installs the hook, and asks for 8 GiB inside the
    /// frontier's guard.
    #[test]
    fn a_refused_host_allocation_in_a_module_check_is_that_module_s_non_answer() {
        const CHILD: &str = "FLN_W9DX_HOST_ALLOCATION_CHILD";
        const MARKER: &str = "w9dx: the run continued past a refused allocation";
        const REQUESTED: usize = 8 << 30;
        if std::env::var_os(CHILD).is_some() {
            super::install_host_allocation_failure_hook();
            let done = super::frontier_guarded(7, true, std::time::Instant::now(), || {
                let block = std::hint::black_box(vec![0_u8; std::hint::black_box(REQUESTED)]);
                // Reached only if the limit did not hold: an accepted row fails the
                // assertions below.
                super::FrontierDone {
                    index: 7,
                    verdict: super::OleanModuleVerdict::Accepted {
                        declarations: block.len(),
                    },
                    accepted: None,
                    engine: None,
                    elapsed: std::time::Duration::ZERO,
                    retained: None,
                }
            });
            assert_eq!(done.index, 7);
            assert!(done.accepted.is_none() && done.engine.is_none());
            assert!(
                matches!(
                    &done.verdict,
                    super::OleanModuleVerdict::Inconclusive(fln_core::outcome::Inconclusive {
                        cause: fln_core::outcome::InconclusiveCause::DependencyUnavailable { what },
                        ..
                    }) if what.text() == format!(
                        "host memory: the host refused an allocation of {REQUESTED} bytes"
                    )
                ),
                "the module's row must be a typed non-answer, got {:?}",
                done.verdict
            );
            assert!(
                matches!(
                    done.retained,
                    Some(super::FrontierRetained::Failed(
                        OleanCheckError::HostMemory {
                            requested: REQUESTED
                        }
                    ))
                ),
                "a retained job keeps the typed error"
            );
            let after = std::hint::black_box(vec![1_u8; 1 << 20]);
            assert_eq!(after.len(), 1 << 20);
            println!("{MARKER}");
            return;
        }
        let test = "tests::a_refused_host_allocation_in_a_module_check_is_that_module_s_non_answer";
        let binary = std::env::current_exe().expect("the test binary's path");
        // util-linux `prlimit` sets the child's address-space limit and execs it;
        // no shell is involved.
        let output = std::process::Command::new("prlimit")
            .arg(format!("--as={}", 4_u64 << 30))
            .arg("--")
            .arg(&binary)
            .args(["--exact", test, "--nocapture", "--test-threads", "1"])
            .env(CHILD, "1")
            .output()
            .expect("run the test binary under prlimit's address-space limit");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && stdout.contains(MARKER),
            "the limited child did not survive its refused allocation: {:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            output.status
        );
        assert!(
            stderr.contains(&format!("memory allocation of {REQUESTED} bytes failed")),
            "the hook names the refused request on stderr:\n{stderr}"
        );
    }

    /// FL-INV-07: a frontier row whose council had no answer, or which ran past a
    /// structural limit, is a non-answer. Only a disagreement or a kernel
    /// rejection is a failure.
    #[test]
    fn frontier_rows_type_non_answers_as_inconclusive_and_refusals_as_failed() {
        use fln_core::outcome::{Inconclusive, InconclusiveCause};

        let no_answer = super::frontier_error_verdict(OleanCheckError::Admission(
            EngineAdmissionError::BatchDeclaration {
                index: 3,
                error: Box::new(EngineAdmissionError::CouncilNoAnswer {
                    summary: "checker: budget exhausted".to_owned(),
                }),
            },
        ));
        assert!(
            matches!(
                &no_answer,
                super::OleanModuleVerdict::Inconclusive(Inconclusive {
                    cause: InconclusiveCause::DependencyUnavailable { what },
                    ..
                }) if what.text().contains("checker: budget exhausted")
            ),
            "a nested council non-answer must be inconclusive, got {no_answer:?}"
        );

        for error in [
            OleanCheckError::DependencyPresentationLimit {
                observed: 101,
                limit: 100,
            },
            OleanCheckError::DeclarationLimit {
                observed: 7,
                limit: 6,
            },
        ] {
            let verdict = super::frontier_error_verdict(error);
            assert!(
                matches!(
                    &verdict,
                    super::OleanModuleVerdict::Inconclusive(Inconclusive {
                        cause: InconclusiveCause::ResourceExhausted { usage },
                        ..
                    }) if usage.is_genuine_exhaustion()
                ),
                "a structural limit must be a genuine exhaustion, got {verdict:?}"
            );
        }

        for error in [
            OleanCheckError::HostMemory { requested: 8 << 30 },
            OleanCheckError::AllocationFailure {
                resource: "olean frontier rows",
                requested: 3,
            },
            OleanCheckError::Admission(EngineAdmissionError::BatchDeclaration {
                index: 2,
                error: Box::new(EngineAdmissionError::AllocationFailure {
                    resource: "admission batch",
                    requested: 5,
                }),
            }),
        ] {
            let verdict = super::frontier_error_verdict(error);
            assert!(
                matches!(
                    &verdict,
                    super::OleanModuleVerdict::Inconclusive(Inconclusive {
                        cause: InconclusiveCause::DependencyUnavailable { what },
                        ..
                    }) if what.text().starts_with("host memory: ")
                ),
                "a refused allocation is a non-answer, never a refusal, got {verdict:?}"
            );
        }

        for error in [
            OleanCheckError::Admission(EngineAdmissionError::CouncilHalted {
                summary: "checker disagreed".to_owned(),
            }),
            OleanCheckError::Admission(EngineAdmissionError::BatchDeclaration {
                index: 0,
                error: Box::new(EngineAdmissionError::KernelRejected {
                    class: RejectClass::LooseBVar,
                    message: "loose bound variable".to_owned(),
                }),
            }),
        ] {
            let verdict = super::frontier_error_verdict(error);
            assert!(
                matches!(verdict, super::OleanModuleVerdict::Failed(_)),
                "a disagreement or rejection must stay a failure, got {verdict:?}"
            );
        }

        for error in [
            OleanCheckError::InternalInvariant {
                detail: "frontier module was visited twice",
            },
            OleanCheckError::Admission(EngineAdmissionError::BatchDeclaration {
                index: 1,
                error: Box::new(EngineAdmissionError::CheckerBridge {
                    detail: "the checker council agreed without an admission record".to_owned(),
                }),
            }),
        ] {
            let verdict = super::frontier_error_verdict(error);
            assert!(
                matches!(verdict, super::OleanModuleVerdict::InternalFault(_)),
                "our own accounting failing is an internal fault, got {verdict:?}"
            );
        }
    }

    /// fln-s97y's residue: a decode stop against an explicit allowance is a typed
    /// resource exhaustion carrying that allowance, a host refusal is a host-memory
    /// non-answer, and malformed input still fails. A stop whose numbers do not show an
    /// overrun is not promoted to an exhaustion it cannot demonstrate.
    #[test]
    fn frontier_rows_type_decode_budget_stops_with_their_allowance() {
        use fln_core::diag::{ResourceReason, StructuralUnit};
        use fln_core::outcome::{Inconclusive, InconclusiveCause};

        let module = Name::from_components(["Planted"]);
        let in_module = |error: OleanDecodeError| OleanCheckError::ModuleDecode {
            module: module.clone(),
            error,
        };
        let budget_cases = [
            (
                OleanCheckError::Decode(OleanDecodeError::Declaration(
                    OleanDeclarationError::Budget {
                        visited: 6,
                        budget: 5,
                    },
                )),
                StructuralUnit::ProducedNodes,
                5,
                6,
            ),
            (
                in_module(OleanDecodeError::Region(
                    OleanRegionError::BudgetExhausted {
                        visited: 11,
                        budget: 10,
                    },
                )),
                StructuralUnit::ProducedNodes,
                10,
                11,
            ),
            (
                in_module(OleanDecodeError::CompanionRegion {
                    part: super::OleanCompanionPart::Server,
                    error: OleanRegionError::PayloadBudgetExhausted {
                        required: 300,
                        budget: 256,
                    },
                }),
                StructuralUnit::InputBytes,
                256,
                300,
            ),
            (
                in_module(OleanDecodeError::CompanionDeclaration {
                    part: super::OleanCompanionPart::Private,
                    error: OleanDeclarationError::Budget {
                        visited: 9,
                        budget: 8,
                    },
                }),
                StructuralUnit::ProducedNodes,
                8,
                9,
            ),
            (
                in_module(OleanDecodeError::ArtifactTooLarge {
                    bytes: 2048,
                    limit: 1024,
                }),
                StructuralUnit::InputBytes,
                1024,
                2048,
            ),
            (
                in_module(OleanDecodeError::Declaration(
                    OleanDeclarationError::ChainTooLarge {
                        bytes: 4096,
                        limit: 4000,
                    },
                )),
                StructuralUnit::InputBytes,
                4000,
                4096,
            ),
        ];
        for (error, unit, allowed, observed) in budget_cases {
            let verdict = super::frontier_error_verdict(error);
            match &verdict {
                super::OleanModuleVerdict::Inconclusive(Inconclusive {
                    cause: InconclusiveCause::ResourceExhausted { usage },
                    ..
                }) => {
                    assert_eq!(usage.reason, ResourceReason::StructuralBudget { unit });
                    assert_eq!((usage.allowed, usage.observed), (allowed, observed));
                    assert!(usage.is_genuine_exhaustion());
                }
                other => panic!("a decode budget stop must carry its allowance, got {other:?}"),
            }
        }

        let refused = super::frontier_error_verdict(in_module(OleanDecodeError::Declaration(
            OleanDeclarationError::AllocationRefused { requested: 7 },
        )));
        assert!(
            matches!(
                &refused,
                super::OleanModuleVerdict::Inconclusive(Inconclusive {
                    cause: InconclusiveCause::DependencyUnavailable { what },
                    ..
                }) if what.text().starts_with("host memory: ")
            ),
            "a refused decode reservation is a host non-answer, got {refused:?}"
        );

        for error in [
            in_module(OleanDecodeError::Region(OleanRegionError::BadMagic)),
            in_module(OleanDecodeError::Declaration(
                OleanDeclarationError::Shape {
                    offset: 64,
                    what: "planted shape",
                },
            )),
            OleanCheckError::Decode(OleanDecodeError::UnexpectedCompanionParts),
            // Numbers that do not show an overrun: never promoted to an exhaustion.
            in_module(OleanDecodeError::ArtifactTooLarge {
                bytes: 1024,
                limit: 1024,
            }),
            in_module(OleanDecodeError::Declaration(
                OleanDeclarationError::Budget {
                    visited: 5,
                    budget: 5,
                },
            )),
        ] {
            let verdict = super::frontier_error_verdict(error);
            assert!(
                matches!(verdict, super::OleanModuleVerdict::Failed(_)),
                "malformed input, or a stop that cannot show its overrun, stays failed, got {verdict:?}"
            );
        }
    }

    /// A construct this implementation cannot judge yet is a typed `Unsupported`
    /// non-answer naming the construct, never `failed` (FL-INV-07): the decoder's
    /// `Name.num` that needs an `mpz`, and the planner's four `*Unsupported` refusals.
    /// None occurs in the stdlib receipt or S20's 5,712 rows, so each is planted. A
    /// genuinely malformed declaration payload stays `failed`.
    #[test]
    fn frontier_rows_type_unsupported_constructs_as_inconclusive_naming_them() {
        use fln_core::outcome::{Inconclusive, InconclusiveCause};

        let module = Name::from_components(["Planted"]);
        let name = |text: &str| Name::from_components(text.split('.'));
        let mpz = || OleanDeclarationError::Unsupported {
            offset: 4096,
            what: "Name.num mpz",
        };
        let cases = [
            (
                OleanCheckError::Decode(OleanDecodeError::Declaration(mpz())),
                "Name.num mpz",
            ),
            (
                OleanCheckError::ModuleDecode {
                    module: module.clone(),
                    error: OleanDecodeError::CompanionDeclaration {
                        part: super::OleanCompanionPart::Private,
                        error: mpz(),
                    },
                },
                "Name.num mpz",
            ),
            (
                OleanCheckError::UnsupportedDeclaration {
                    name: name("Planted.Quot"),
                    kind: "quotient",
                },
                "Planted.Quot",
            ),
            (
                OleanCheckError::MutualEnvelopeUnsupported {
                    name: name("Planted.left"),
                    members: vec![name("Planted.left"), name("Planted.right")],
                },
                "mutual declaration envelope for `Planted.left`",
            ),
            (
                OleanCheckError::InductiveEnvelopeUnsupported {
                    name: name("Planted.T"),
                    members: vec![name("Planted.T.mk")],
                },
                "inductive declaration envelope for `Planted.T`",
            ),
            (
                OleanCheckError::QuotientEnvelopeUnsupported {
                    names: vec![name("Quot"), name("Quot.mk")],
                },
                "quotient initialization envelope",
            ),
        ];
        for (error, construct) in cases {
            let verdict = super::frontier_error_verdict(error);
            match &verdict {
                super::OleanModuleVerdict::Inconclusive(Inconclusive {
                    cause: InconclusiveCause::Unsupported { construct: named },
                    ..
                }) => assert!(
                    named.text().contains(construct),
                    "the row names the construct `{construct}`: {named:?}"
                ),
                other => panic!("an unsupported construct is a typed non-answer, got {other:?}"),
            }
        }
        let malformed = super::frontier_error_verdict(OleanCheckError::Decode(
            OleanDecodeError::Declaration(OleanDeclarationError::Shape {
                offset: 64,
                what: "planted shape",
            }),
        ));
        assert!(
            matches!(malformed, super::OleanModuleVerdict::Failed(_)),
            "malformed input stays failed, got {malformed:?}"
        );
    }

    /// The real frontier over a real artifact whose mutual definitions name a member
    /// list the planner cannot rebuild: the row is an `Unsupported` non-answer naming
    /// the declaration, and the well-formed control is accepted.
    #[test]
    fn a_planted_unbuildable_mutual_envelope_is_an_unsupported_frontier_row() {
        use fln_core::outcome::{Inconclusive, InconclusiveCause};

        let engine = Engine::from_environment(Environment::new());
        let module = Name::from_components(["Planted"]);
        let row = |constants: &[ConstantInfo]| {
            let bytes = standalone_olean(constants);
            let inputs = [OleanModuleInput {
                name: &module,
                artifact: &bytes,
                server_artifact: None,
                private_artifact: None,
            }];
            let frontier = engine
                .check_olean_frontier(
                    &inputs,
                    &KVMap::new(),
                    OleanCheckLimits::new(bytes.len(), test_budget()),
                )
                .expect("a one-module set is a frontier, not a whole-set refusal");
            assert_eq!(frontier.rows.len(), 1);
            frontier.rows.into_iter().next().expect("one row").verdict
        };
        let mut mismatched = mutual_olean_declarations();
        let ConstantInfo::Defn(right) = &mut mismatched[0] else {
            panic!("the fixture's first row is the right mutual definition")
        };
        right.all.reverse();
        match row(&mismatched) {
            super::OleanModuleVerdict::Inconclusive(Inconclusive {
                cause: InconclusiveCause::Unsupported { construct },
                ..
            }) => assert!(
                construct.text().contains("Fixture.mutualRight"),
                "the row names the declaration: {construct:?}"
            ),
            other => panic!("an unbuildable envelope is not a failed module, got {other:?}"),
        }
        let control = row(&mutual_olean_declarations());
        assert!(
            matches!(control, super::OleanModuleVerdict::Accepted { .. }),
            "the well-formed mutual block is accepted, got {control:?}"
        );
    }
}
