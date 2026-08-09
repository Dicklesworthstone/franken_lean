//! **fln** — the embeddable library facade (plan §17.2).
//!
//! The first live surfaces are the typed diagnostic return adapter (bead
//! `franken_lean-wlan`) and a bounded, real engine path (bead `franken_lean-7kc`)
//! from a bounded Nat definition or first-order application source, or from an
//! already-elaborated definition, through Crucible, the compiler's validated
//! FIR and canonical FLBC, and Golem. The source path is deliberately the
//! implemented grammar subset, not a claim of general Lean elaboration or
//! Prelude support.

#![forbid(unsafe_code)]

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
use fln_env::constants::ConstantInfo;
pub use fln_env::constants::{
    AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_env::environment::DeclarationCommitted;
pub use fln_env::environment::{DeclarationBudget, Environment};
pub use fln_env::pmap::CollisionBudget;
pub use fln_hash::root::LogicalRoot;
pub use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
pub use fln_kernel::verdict::{Budget, RejectClass};
pub use fln_vm::interpreter::{ExecutionLimits as VmExecutionLimits, VmExit};
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

/// One immutable embeddable engine snapshot.
///
/// The currently live constructor seeds only the axiomatic `Nat : Sort 1` name
/// needed by the bounded natural-definition frontend. It is not the real
/// Prelude. Successful execution returns a new `Engine` snapshot containing
/// the published declaration; the receiver is never mutated.
#[derive(Debug, Clone)]
pub struct Engine {
    environment: Environment,
}

impl Engine {
    /// Attach the embeddable facade to an existing immutable environment
    /// produced by an importer, module transaction, or earlier engine session.
    /// This performs no admission and grants no new authority.
    pub fn from_environment(environment: Environment) -> Self {
        Self { environment }
    }

    /// Construct the bounded natural-definition engine through the same kernel
    /// admission and publication capability used for ordinary declarations.
    pub fn with_nat_seed(budget: Budget) -> Result<Self, SeedEnvironmentError> {
        fln_elab::seed::bootstrap_nat_environment(budget).map(|environment| Self { environment })
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

    /// Parse, elaborate, admit, publish, compile, canonically encode/decode,
    /// and execute one bounded Nat-valued definition command. The source value
    /// may be a natural literal, a constant identifier, or a saturated
    /// identifier-headed application of those atom forms.
    ///
    /// The publication council is explicitly empty because no independent
    /// checker is configured on this bounded facade yet. This is a real K1
    /// admission and publication, but it is not consensus-receipt evidence.
    /// Kernel and VM non-answers remain [`Outcome::Inconclusive`] or
    /// [`Outcome::InternalFault`]; they are never collapsed into rejection.
    pub fn execute_nat_definition(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionExecution>, EngineExecutionError> {
        let parsed = fln_parse::parse_nat_definition(source)
            .map_err(NatDefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        let declaration = fln_elab::elaborate_nat_definition(parsed.syntax())
            .map_err(NatDefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        self.execute_definition(declaration, options, limits)
    }

    /// Execute a nonempty sequence of bounded source definitions atomically.
    ///
    /// Each command observes the immutable successor of the command before it.
    /// A refusal or non-answer at any index returns no batch successor, so the
    /// caller can only retain the original `self`. Completed per-command roots
    /// remain in the successful result and form a checkable continuity chain.
    pub fn execute_nat_definitions(
        &self,
        sources: &[&[u8]],
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> Result<Outcome<DefinitionBatchExecution>, EngineExecutionError> {
        self.execute_batch(sources.len(), options, |engine, index| {
            engine.execute_nat_definition(sources[index], options, limits)
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
    /// The publication council is still explicitly empty: this is real K1
    /// admission, not independent-checker consensus. Publication creates only a
    /// local immutable successor until compilation and execution complete, so a
    /// later refusal or non-answer exposes no partially advanced engine.
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
        let base_logical_root = self.logical_root(options);

        let admitted = match admit(&self.environment, declaration.clone(), limits.kernel) {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let checked = match convene(&Council::nobody_was_asked(), admitted) {
            CouncilOutcome::Agreed(checked) => checked,
            CouncilOutcome::KernelRejected { class, message, .. } => {
                return Err(EngineExecutionError::KernelRejected { class, message });
            }
            CouncilOutcome::Halted(halt) => {
                return Err(EngineExecutionError::CouncilHalted {
                    summary: halt.summary(),
                });
            }
        };
        let environment = match checked.publish(limits.declaration, limits.collisions, None) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                publication,
            ))) => publication.environment,
            Outcome::Complete(Published::Committed(DeclarationCommitted::DuplicateName {
                name,
            }))
            | Outcome::Complete(Published::DuplicateName { name }) => {
                return Err(EngineExecutionError::DuplicateName { name });
            }
            Outcome::Complete(Published::BlockCommitted(_)) => {
                return Err(EngineExecutionError::UnexpectedPublication {
                    detail: "a single definition published as a block",
                });
            }
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };

        let functions = executable_nat_dependencies(&self.environment, &expression, limits.ingress)
            .map_err(EngineExecutionError::Ingress)?;
        let local_lambda = executable_nat_lambda(&declaration, limits.ingress)
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
        let exit = match fln_vm::interpreter::execute(&executable, limits.vm, None) {
            Outcome::Complete(exit) => exit,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let result_logical_root = environment.logical_root(options);

        Ok(Outcome::Complete(DefinitionExecution {
            engine: Engine { environment },
            declaration,
            base_logical_root,
            result_logical_root,
            flbc_artifact,
            exit,
        }))
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

/// Independent caller-supplied bounds for every bounded stage of one execution.
///
/// There is deliberately no `Default`: a kernel budget is calibrated to the
/// native stack on which the caller will run it, and an embeddable API cannot
/// infer that stack size honestly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineExecutionLimits {
    pub kernel: Budget,
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
            declaration: DeclarationBudget::default(),
            collisions: CollisionBudget::default(),
            ingress: IngressLimits::default(),
            flbc_codec: CodecLimits::default(),
            vm: VmExecutionLimits::default(),
        }
    }
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
            Self::Frontend(error) => write!(formatter, "frontend refused source: {error:?}"),
            Self::KernelRejected { class, message } => {
                write!(
                    formatter,
                    "kernel rejected declaration ({class:?}): {message}"
                )
            }
            Self::CouncilHalted { summary } => write!(formatter, "council halted: {summary}"),
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

#[cfg(test)]
mod tests {
    use super::{
        AxiomVal, BinderInfo, Budget, ConstantVal, Declaration, DefinitionSafety, DefinitionVal,
        Engine, EngineExecutionError, EngineExecutionLimits, Expr, IngressError, IngressResource,
        KVMap, Level, Literal, Name, NatLit, Outcome, ReducibilityHints, RejectClass,
    };
    use fln_vm::interpreter::{ValueKind, VmExit, value_kind};

    fn test_budget() -> Budget {
        Budget::for_stack_bytes(2 * 1024 * 1024)
    }

    fn test_limits() -> EngineExecutionLimits {
        EngineExecutionLimits::new(test_budget())
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
        let VmExit::Returned(returned) = completed.exit else {
            panic!("the literal definition must return normally");
        };
        assert_eq!(value_kind(&returned.value), ValueKind::Scalar);
        assert_eq!(returned.value.unbox(), 42);
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
