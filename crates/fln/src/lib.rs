//! **fln** — the embeddable library facade (plan §17.2).
//!
//! The first live surfaces are the typed diagnostic return adapter (bead
//! `franken_lean-wlan`) and a bounded, real engine path (bead `franken_lean-7kc`)
//! from a bounded Nat definition or first-order application source, or from an
//! already-elaborated definition, through Crucible, the compiler's validated
//! FIR and canonical FLBC, and Golem. The source path is deliberately the
//! implemented grammar subset, not a claim of general Lean elaboration or
//! Prelude support. Already-elaborated axioms, definitions, theorems, opaques,
//! and non-safe mutual definition blocks can also advance an immutable engine
//! snapshot through admission and publication without compiling or executing a
//! body. Embedders can also validate and execute an existing canonical FLBC
//! artifact without reaching into the compiler or VM crates, and inspect or
//! re-derive a real pinned-format `.olean` through the codec's audited reader.

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
use fln_comp::ingress::{FunctionBinding, IngressResource, LambdaBinding, LambdaRecursion};
pub use fln_comp::ingress::{IngressError, IngressLimits};
use fln_core::diag::{
    DiagnosticChannel, DiagnosticColorPolicy, DiagnosticFormat, DiagnosticFrontend, ExitClass,
    ProjectionRefusal, ProjectionRequest, ProjectionSnapshot,
};
pub use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
pub use fln_core::level::Level;
pub use fln_core::name::Name;
pub use fln_core::options::KVMap;
pub use fln_core::outcome::Outcome;
pub use fln_elab::{NatDefinitionFrontendError, seed::SeedEnvironmentError};
pub use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, OpaqueVal,
    ReducibilityHints, TheoremVal,
};
use fln_env::environment::DeclarationCommitted;
pub use fln_env::environment::{DeclarationBudget, Environment};
pub use fln_env::pmap::CollisionBudget;
use fln_hash::canon::Canonical;
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
    ArtifactStoreDirectory, BoundArtifactSet, InjectedIoError, PublicationControl,
    PublicationIoPoint, PublicationPoint, ResolvedArtifactSet, SCHEMA_ARTIFACT_SET_MANIFEST,
    StagedArtifactSet, artifact_byte_hash, artifact_semantic_hash,
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
use fln_vm::interpreter::CommandExecutionContext;
pub use fln_vm::interpreter::{
    ExecutionLimits as VmExecutionLimits, ValueKind as VmValueKind, VmExit,
    value_kind as vm_value_kind,
};
use std::collections::BTreeSet;
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

/// Independent resource ceilings for canonical FLBC decoding and execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FlbcExecutionLimits {
    pub codec: CodecLimits,
    pub vm: VmExecutionLimits,
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
}

/// Typed refusal from the public `.olean` read path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OleanDecodeError {
    ArtifactTooLarge { bytes: usize, limit: usize },
    Region(OleanRegionError),
    Declaration(OleanDeclarationError),
}

impl fmt::Display for OleanDecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ArtifactTooLarge { bytes, limit } => {
                write!(f, ".olean artifact has {bytes} bytes; limit is {limit}")
            }
            Self::Region(error) => write!(f, ".olean region: {error}"),
            Self::Declaration(error) => write!(f, ".olean declaration: {error}"),
        }
    }
}

impl std::error::Error for OleanDecodeError {}

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
    })
}

/// One immutable embeddable engine snapshot.
///
/// The currently live constructor seeds only the axiomatic `Nat : Sort 1` name
/// needed by the bounded natural-definition frontend. It is not the real
/// Prelude. Successful admission or execution returns a new `Engine` snapshot
/// containing the published declaration; the receiver is never mutated.
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

    /// Construct the bounded natural-definition engine through the same kernel
    /// admission and publication capability used for ordinary declarations.
    pub fn with_nat_seed(budget: Budget) -> Result<Self, SeedEnvironmentError> {
        fln_elab::seed::bootstrap_nat_environment(budget).map(|environment| Self {
            environment,
            checker_environment: None,
        })
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
        let declaration = fln_elab::elaborate_nat_definition(parsed.syntax())
            .map_err(NatDefinitionFrontendError::Elaborate)
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
    /// References to closed, universe-free first-order `Nat -> ... -> Nat`
    /// definitions are compiled from the exact types and bodies already
    /// published in the base environment. This is the first
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

        let functions = executable_nat_dependencies(&self.environment, &expression, limits.ingress)
            .map_err(EngineExecutionError::Ingress)?;
        let local_lambda = executable_nat_lambda(&admission.declaration, limits.ingress)
            .map_err(EngineExecutionError::Ingress)?;
        let lambdas = local_lambda.as_slice();
        let ingress = fln_comp::ingress::lower_closed_expr_with_lambdas(
            &expression,
            &[],
            &[],
            &functions,
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
/// This deliberately supports one exact family of erased signatures. A raw
/// caller-supplied [`FunctionBinding`] would be able to replace a checked
/// constant's body or lie about its runtime type; neither is an acceptable
/// embeddable-engine boundary.
fn executable_nat_dependencies(
    environment: &Environment,
    source: &Expr,
    limits: IngressLimits,
) -> Result<Vec<FunctionBinding>, IngressError> {
    let nat_type = Expr::const_(Name::from_components(["Nat"]), Vec::new());
    let mut pending = BTreeSet::new();
    let mut resolved = BTreeSet::new();
    let mut visited_nodes = 0usize;
    collect_executable_constants(source, &mut pending, &mut visited_nodes, limits)?;

    let maximum_functions = limits.fir.max_functions.saturating_sub(1);
    let mut functions = Vec::new();
    while let Some(name) = pending.pop_first() {
        if !resolved.insert(name.clone()) {
            continue;
        }
        let Some(ConstantInfo::Defn(definition)) = environment.find(&name) else {
            continue;
        };
        let Some((arity, body)) =
            executable_nat_signature(definition, &nat_type, &mut visited_nodes, limits)?
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
        let (parameters, parameter_ownership) = nat_runtime_parameters(arity)?;
        collect_executable_constants(body, &mut pending, &mut visited_nodes, limits)?;
        functions.push(FunctionBinding {
            name,
            universe_arity: 0,
            parameters,
            parameter_ownership,
            result: ValueType::Nat,
            result_ownership: CallableResultOwnership::Scalar,
            body: body.clone(),
        });
    }
    Ok(functions)
}

/// Describe the definition currently being published when its full value is a
/// supported first-order Nat lambda. This lets the same compiler path execute
/// the function value itself and expose the checked successor snapshot.
fn executable_nat_lambda(
    declaration: &Declaration,
    limits: IngressLimits,
) -> Result<Option<LambdaBinding>, IngressError> {
    let Declaration::Defn(definition) = declaration else {
        return Ok(None);
    };
    let nat_type = Expr::const_(Name::from_components(["Nat"]), Vec::new());
    let mut visited_nodes = 0usize;
    let Some((arity, _)) =
        executable_nat_signature(definition, &nat_type, &mut visited_nodes, limits)?
    else {
        return Ok(None);
    };
    if arity == 0 {
        return Ok(None);
    }
    let (parameters, parameter_ownership) = nat_runtime_parameters(arity)?;
    Ok(Some(LambdaBinding {
        lambda: definition.value.clone(),
        parameters,
        parameter_ownership,
        result: ValueType::Nat,
        result_ownership: CallableResultOwnership::Scalar,
        recursion: LambdaRecursion::NonRecursive,
    }))
}

fn nat_runtime_parameters(
    arity: usize,
) -> Result<(Vec<ValueType>, Vec<fln_comp::flbc::ArgumentOwnership>), IngressError> {
    let mut parameters = Vec::new();
    parameters
        .try_reserve_exact(arity)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: arity,
        })?;
    parameters.resize(arity, ValueType::Nat);
    let mut parameter_ownership = Vec::new();
    parameter_ownership
        .try_reserve_exact(arity)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: arity,
        })?;
    parameter_ownership.resize(arity, fln_comp::flbc::ArgumentOwnership::Borrowed);
    Ok((parameters, parameter_ownership))
}

/// Bind one checked definition to the compiler's exact first-order Nat ABI.
///
/// Pi binders and lambda binders must match structurally and in count. K1 has
/// already proved the declaration well typed, but the runtime bridge accepts a
/// deliberately narrower representation than definitional equality so it
/// never invents an erasure rule. The returned body has its top-level lambdas
/// removed, as required by [`FunctionBinding`].
fn executable_nat_signature<'a>(
    definition: &'a DefinitionVal,
    nat_type: &Expr,
    visited_nodes: &mut usize,
    limits: IngressLimits,
) -> Result<Option<(usize, &'a Expr)>, IngressError> {
    use fln_core::expr::ExprNode;

    if !definition.base.level_params.is_empty() {
        return Ok(None);
    }

    let mut declared_type = &definition.base.type_;
    let mut body = &definition.value;
    let mut arity = 0usize;
    loop {
        charge_catalog_node(visited_nodes, limits)?;
        match declared_type.node() {
            ExprNode::ForallE {
                binder_type,
                body: result_type,
                ..
            } if binder_type == nat_type => {
                charge_catalog_node(visited_nodes, limits)?;
                let ExprNode::Lam {
                    binder_type: value_binder_type,
                    body: value_body,
                    ..
                } = body.node()
                else {
                    return Ok(None);
                };
                if value_binder_type != nat_type {
                    return Ok(None);
                }
                arity = arity.saturating_add(1);
                if arity > limits.max_context_depth {
                    return Err(IngressError::ResourceLimit {
                        resource: IngressResource::ContextDepth,
                        limit: limits.max_context_depth,
                        observed: arity,
                    });
                }
                declared_type = result_type;
                body = value_body;
            }
            _ => break,
        }
    }

    Ok((declared_type == nat_type).then_some((arity, body)))
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
        AxiomVal, BinderInfo, Budget, CheckerAdmissionBudget, CheckerAdmissionGround, ConstantInfo,
        ConstantVal, Declaration, DefinitionSafety, DefinitionVal, Engine, EngineAdmissionError,
        EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits, Environment, Expr,
        FlbcExecutionLimits, IngressError, IngressResource, KVMap, Level, Literal, Name,
        NatDefinitionFrontendError, NatLit, OleanDeclarationError, OleanDecodeError,
        OleanDecodeLimits, OleanRebuildError, OleanRegionError, OleanWalkBudget, OpaqueVal,
        Outcome, ReducibilityHints, RejectClass, TheoremVal, VmExecutionLimits,
        decode_olean_artifact, execute_flbc_artifact, execute_golem_with_options,
        rebuild_olean_artifact,
    };
    use fln_comp::flbc::{
        ArgumentOwnership, CallableResultOwnership, CodecError, CodecLimits, Function, FunctionId,
        Instruction, Program, Register, ResultOwnership, ValidatedProgram, encode_canonical,
        validate,
    };
    use fln_core::diag::ResourceReason;
    use fln_core::options::DataValue;
    use fln_core::outcome::InconclusiveCause;
    use fln_vm::interpreter::{ValueKind, VmExit, value_kind};

    fn test_budget() -> Budget {
        Budget::for_stack_bytes(2 * 1024 * 1024)
    }

    fn test_limits() -> EngineExecutionLimits {
        EngineExecutionLimits::new(test_budget())
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

    fn definition(name: &str, value: Expr) -> Declaration {
        let name = Name::from_components([name]);
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_: nat_type(),
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
        let name = Name::from_components([name]);
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_: Expr::forall_e(
                    Name::from_components(["value"]),
                    nat_type(),
                    nat_type(),
                    BinderInfo::Default,
                ),
            },
            value: Expr::lam(
                Name::from_components(["value"]),
                nat_type(),
                Expr::bvar(0).expect("one Nat parameter fits the term covenant"),
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
    fn independent_checker_non_answer_vetoes_publication() {
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
    fn admission_only_axioms_publish_and_retain_the_checker_projection() {
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let seeded = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
    fn checked_multi_parameter_nat_function_preserves_argument_order() {
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
        let engine = Engine::with_nat_seed(test_budget()).expect("Nat seed publishes through K1");
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
