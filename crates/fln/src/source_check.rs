//! Admission-only source batches. No compiler, VM, or artifact publication.
use super::*;
pub(crate) mod grammar;
pub mod inspect;
pub(crate) mod instance_attributes;
pub mod modules;
mod reducibility;
pub(crate) mod scopes;

pub(crate) fn source_site(
    source: &[u8],
) -> Result<fln_elab::source::scope::SourceSite, EngineExecutionError> {
    fln_syntax::source::SourceText::from_utf8(source)
        .map(fln_elab::source::scope::SourceSite::new)
        .map_err(fln_parse::NatDefinitionParseError::Source)
        .map_err(DefinitionFrontendError::Parse)
        .map_err(EngineExecutionError::Frontend)
}

#[derive(Debug, Clone, Copy)]
pub struct SourceCheckLimits {
    pub admission: EngineAdmissionLimits,
    pub max_bytes: usize,
    pub max_commands: usize,
}
impl SourceCheckLimits {
    pub fn new(admission: EngineAdmissionLimits) -> Self {
        Self {
            admission,
            max_bytes: 1024 * 1024,
            max_commands: 4096,
        }
    }
}

/// A complete batch shares the ordinary dual-checker admission authority.
/// No successor is exposed on a failure in any file or command.
#[derive(Debug)]
pub struct SourceFileCheck {
    pub engine: Engine,
    pub files: usize,
    pub commands: usize,
    pub theorems: usize,
    pub base_logical_root: LogicalRoot,
    pub result_logical_root: LogicalRoot,
    /// Exact lexical state after the last file's checked command prefix.
    /// It is not an exported module effect and does not confer proof authority.
    pub scope: fln_elab::source::scope::SourceScope,
}

#[derive(Debug)]
pub enum SourceCheckError {
    Scope {
        file: usize,
        command: usize,
        offset: usize,
        message: String,
    },
    EmptyInput,
    Limit {
        resource: &'static str,
        limit: usize,
    },
    Command {
        file: usize,
        command: usize,
        offset: usize,
        error: Box<EngineExecutionError>,
    },
}
impl std::fmt::Display for SourceCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Scope {
                file,
                command,
                offset,
                message,
            } => write!(
                f,
                "file {file}, command {command}, byte {offset}: {message}"
            ),
            Self::EmptyInput => write!(f, "source checking requires a nonempty file set"),
            Self::Limit { resource, limit } => {
                write!(f, "source check exceeds {resource} limit {limit}")
            }
            Self::Command {
                file,
                command,
                offset,
                error,
            } => write!(f, "file {file}, command {command}, byte {offset}: {error}"),
        }
    }
}
impl std::error::Error for SourceCheckError {}

impl SourceCheckError {
    /// Reuse the same command effects in the execution stream without turning
    /// a resource stop into a source rejection or discarding a typed cause.
    pub(crate) fn into_execution_error(self) -> EngineExecutionError {
        match self {
            Self::Scope { message, .. } => EngineExecutionError::ScopeTransition { message },
            Self::EmptyInput => EngineExecutionError::EmptyBatch,
            Self::Limit { resource, limit } => {
                EngineExecutionError::SourceScopeLimit { resource, limit }
            }
            Self::Command { error, .. } => *error,
        }
    }

    /// Wire classification preserves frontend, compiler and codec resource
    /// stops as nonanswers, including commands executed in imported worlds.
    pub fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::EmptyInput | Self::Scope { .. } => ("input", false, 1),
            Self::Limit { .. } => ("resource", false, 3),
            Self::Command { error, .. } => classify(error),
        }
    }
}
pub(crate) fn classify(error: &EngineExecutionError) -> (&'static str, bool, u8) {
    use fln_elab::constraint::unify::UnificationError;
    use fln_elab::universe::UniverseInstantiationError;
    use fln_elab::{NatDefinitionElabError, source::SourceInferenceError};
    match error {
        EngineExecutionError::BatchCommand { error, .. } => classify(error),
        EngineExecutionError::KernelRejected { .. } => ("kernel-rejection", true, 1),
        EngineExecutionError::CouncilHalted { .. }
        | EngineExecutionError::CouncilNoAnswer { .. } => ("inconclusive", false, 3),
        EngineExecutionError::CheckerBridge { .. }
        | EngineExecutionError::UnexpectedPublication { .. } => ("internal-fault", false, 4),
        EngineExecutionError::AllocationFailure { .. }
        | EngineExecutionError::SourceScopeLimit { .. } => ("resource", false, 3),
        EngineExecutionError::Ingress(error) if error.is_resource_exhaustion() => {
            ("resource", false, 3)
        }
        EngineExecutionError::Codec(error) if error.is_resource_exhaustion() => {
            ("resource", false, 3)
        }
        EngineExecutionError::Lowering(error) => {
            if error.is_resource_exhaustion() {
                ("resource", false, 3)
            } else if error.is_internal_fault() {
                ("internal-fault", false, 4)
            } else {
                ("execution", true, 1)
            }
        }
        EngineExecutionError::Ingress(_) | EngineExecutionError::Codec(_) => ("execution", true, 1),
        EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
            NatDefinitionElabError::Inference(reason),
        )) => match reason {
            SourceInferenceError::ArithmeticInconclusive(_)
            | SourceInferenceError::NativeEvaluationInconclusive(_) => ("inconclusive", false, 3),
            // A native evaluation this engine could not run is not a verdict on the source.
            SourceInferenceError::NativeEvaluation(
                fln_elab::native::NativeEvaluationError::Fault(_),
            ) => ("internal-fault", false, 4),
            SourceInferenceError::NativeEvaluation(_) => ("capability", false, 5),
            SourceInferenceError::EvaluationPrinting(_)
            | SourceInferenceError::EquationTheorem(_) => ("capability", false, 5),
            SourceInferenceError::SimpSet(
                fln_elab::source::scope::simp::SimpSetError::Malformed,
            )
            | SourceInferenceError::ProtectedJournal(
                fln_elab::protected_names::ProtectedError::Malformed,
            )
            | SourceInferenceError::DeprecationJournal(
                fln_elab::deprecations::DeprecationError::Malformed,
            )
            | SourceInferenceError::AuxiliaryJournal(
                fln_elab::aux_recursors::AuxRecursorError::Malformed,
            ) => ("internal-fault", false, 4),
            SourceInferenceError::ResourceLimit
            | SourceInferenceError::SimpSet(fln_elab::source::scope::simp::SimpSetError::Limit)
            | SourceInferenceError::ProtectedJournal(
                fln_elab::protected_names::ProtectedError::Limit,
            )
            | SourceInferenceError::DeprecationJournal(
                fln_elab::deprecations::DeprecationError::Limit,
            )
            | SourceInferenceError::Record(fln_elab::records::RecordError::ResourceLimit)
            | SourceInferenceError::Inductive(fln_elab::inductive::InductiveError::ResourceLimit)
            | SourceInferenceError::Auxiliary(
                fln_elab::inductive::auxiliaries::AuxiliaryError::ResourceLimit,
            )
            | SourceInferenceError::AuxiliaryJournal(
                fln_elab::aux_recursors::AuxRecursorError::Limit,
            )
            | SourceInferenceError::InstanceRegistry(
                fln_elab::instances::InstanceRegistryError::Limit,
            ) => ("resource", false, 3),
            SourceInferenceError::TypeObligation(outcome) => match outcome.as_ref() {
                Outcome::Complete(fln_kernel::verdict::Verdict::Rejected { .. }) => {
                    ("kernel-rejection", true, 1)
                }
                Outcome::Inconclusive(_) => ("inconclusive", false, 3),
                _ => ("internal-fault", false, 4),
            },
            SourceInferenceError::Universe(
                UniverseInstantiationError::VisitLimit { .. }
                | UniverseInstantiationError::LevelTooDeep(_),
            ) => ("resource", false, 3),
            SourceInferenceError::Unification(error) => match error.as_ref() {
                UnificationError::StepLimit { .. }
                | UnificationError::NodeLimit { .. }
                | UnificationError::AssignmentLimit { .. }
                | UnificationError::HeartbeatLimit => ("resource", false, 3),
                UnificationError::Reducibility(
                    fln_elab::reducibility::ReducibilityError::Limit
                    | fln_elab::reducibility::ReducibilityError::Instances(
                        fln_elab::instances::InstanceRegistryError::Limit,
                    ),
                )
                | UnificationError::InstanceRegistry(
                    fln_elab::instances::InstanceRegistryError::Limit,
                ) => ("resource", false, 3),
                UnificationError::Reducibility(_) | UnificationError::InstanceRegistry(_) => {
                    ("internal-fault", false, 4)
                }
                UnificationError::Cancelled => ("cancelled", false, 3),
                UnificationError::Universe(
                    UniverseInstantiationError::VisitLimit { .. }
                    | UniverseInstantiationError::LevelTooDeep(_),
                ) => ("resource", false, 3),
                UnificationError::AssignmentCheck { outcome, .. }
                | UnificationError::ConversionCheck { outcome } => match outcome.as_ref() {
                    Outcome::Inconclusive(_) => ("inconclusive", false, 3),
                    Outcome::InternalFault(_) => ("internal-fault", false, 4),
                    _ => ("elaboration", false, 1),
                },
                _ => ("elaboration", false, 1),
            },
            _ => ("elaboration", false, 1),
        },
        // The `lean` front door's `CAPABILITY_NOT_IMPLEMENTED_EXIT`: not a verdict.
        EngineExecutionError::NotImplemented { .. } => ("capability", false, 5),
        EngineExecutionError::EvaluationDependsOnSorry => ("elaboration", false, 1),
        _ => ("input", false, 1),
    }
}

/// The non-expanding source controls have identical meaning in check-only and
/// executable files. Every metadata command publishes a whole successor only
/// after its names and registrations succeed; variables live solely in the
/// lexical scope. `file_base` prevents attributes from rewriting imported
/// declarations' reducibility, including when the file executes on Golem.
pub(crate) fn apply_control_command(
    engine: &mut Engine,
    scope: &mut fln_elab::source::scope::SourceScope,
    file_base: &Environment,
    control: fln_parse::command_scope::ScopeCommand,
    kernel: Budget,
    position @ (file, command, offset): (usize, usize, usize),
) -> Result<Outcome<()>, SourceCheckError> {
    use fln_parse::command_scope::ScopeCommand;

    match control {
        ScopeCommand::Variable(syntax) => {
            let variables =
                source_records::elaboration_outcome(fln_elab::source::scope::variables::declare(
                    &syntax,
                    engine.environment(),
                    kernel,
                    scope,
                ))
                .map_err(|error| command_error(file, command, fln_parse::BytePos(offset), error))?;
            scope.variables = match variables {
                Outcome::Complete(variables) => variables,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        }
        ScopeCommand::Instance(attribute) => {
            engine.environment = instance_attributes::apply(
                engine.environment(),
                scope,
                attribute,
                file,
                command,
                offset,
            )?;
        }
        ScopeCommand::Reducibility(attribute) => {
            engine.environment =
                reducibility::apply(engine.environment(), file_base, scope, attribute, position)?;
        }
        ScopeCommand::Executable(syntax) => {
            let (rows, names) = fln_elab::source::scope::executable::command(&syntax)
                .map_err(DefinitionFrontendError::Elaborate)
                .map_err(EngineExecutionError::Frontend)
                .map_err(|error| command_error(file, command, fln_parse::BytePos(offset), error))?;
            let mut environment = engine.environment.clone();
            for requested in names {
                let name =
                    fln_elab::source::scope::executable::resolve(&environment, scope, &requested)
                        .map_err(DefinitionFrontendError::Elaborate)
                        .map_err(EngineExecutionError::Frontend)
                        .map_err(|error| {
                            command_error(file, command, fln_parse::BytePos(offset), error)
                        })?
                        .ok_or_else(|| SourceCheckError::Scope {
                            file,
                            command,
                            offset,
                            message: format!(
                                "unknown executable attribute declaration `{}`",
                                requested.to_display_string()
                            ),
                        })?;
                if file_base.contains(&name) {
                    return Err(SourceCheckError::Scope {
                        file,
                        command,
                        offset,
                        message: "executable attributes cannot modify imported declarations".into(),
                    });
                }
                environment = fln_elab::source::scope::executable::apply(
                    &environment,
                    scope,
                    &name,
                    &rows,
                    true,
                )
                .map_err(DefinitionFrontendError::Elaborate)
                .map_err(EngineExecutionError::Frontend)
                .map_err(|error| command_error(file, command, fln_parse::BytePos(offset), error))?;
            }
            engine.environment = environment;
        }
        ScopeCommand::Simp(attribute) => {
            // Resolve in the lexical scope, but retain exact declaration
            // identities. A later failure discards every earlier update.
            let mut environment = engine.environment.clone();
            for requested in attribute.declarations {
                let name = scope
                    .resolve(&requested, |name| environment.contains(name))
                    .map_err(|error| SourceCheckError::Scope {
                        file,
                        command,
                        offset,
                        message: error.to_string(),
                    })?
                    .ok_or_else(|| SourceCheckError::Scope {
                        file,
                        command,
                        offset,
                        message: format!(
                            "unknown simp declaration `{}`",
                            requested.to_display_string()
                        ),
                    })?;
                environment =
                    fln_elab::source::scope::simp::update(&environment, &name, attribute.rule)
                        .map_err(|error| {
                            command_error(
                                file,
                                command,
                                fln_parse::BytePos(offset),
                                EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                                    fln_elab::NatDefinitionElabError::Inference(
                                        fln_elab::source::SourceInferenceError::SimpSet(error),
                                    ),
                                )),
                            )
                        })?;
            }
            engine.environment = environment;
        }
        _ => {
            return Err(SourceCheckError::Scope {
                file,
                command,
                offset,
                message: "lexical controls require the source scope driver".into(),
            });
        }
    }
    Ok(Outcome::Complete(()))
}

/// Public section controls use the same exported world as public declarations.
/// Their successful native journal suffix is replayed into the private world;
/// a private section's attributes and local variables never enter that receipt.
#[allow(clippy::too_many_arguments)]
pub(crate) fn apply_module_control_command(
    engine: &mut Engine,
    scopes: &mut scopes::Scopes,
    file_base: &Environment,
    control: fln_parse::command_scope::ScopeCommand,
    kernel: Budget,
    position: (usize, usize, usize),
    mut public: Option<&mut modules::visibility::PublicWorld<'_>>,
    options: &KVMap,
) -> Result<Outcome<()>, SourceCheckError> {
    use fln_parse::command_scope::ScopeCommand;

    if let ScopeCommand::Export { namespace, names } = &control {
        let (file, command, offset) = position;
        let refuse = |message: String| SourceCheckError::Scope {
            file,
            command,
            offset,
            message,
        };
        scopes
            .check_limits(&control)
            .map_err(|(resource, limit)| SourceCheckError::Limit { resource, limit })?;
        let aliases = scopes
            .export_aliases(engine.environment(), namespace, names)
            .map_err(|error| error.into_source(file, command, offset))?;
        if let Some(public) = public {
            // `elabExport` adds aliasExtension entries regardless of the section's
            // declaration visibility (Lean/Elab/BuiltinCommand.lean). The native
            // journal currently requires every target to exist, so a private-only
            // target remains an explicit unsupported case, never a dropped alias
            // or a copied declaration. Public targets retain their distinct checked
            // implementations/signatures in the two worlds.
            let mut next = public.engine().clone();
            for (alias, declaration) in aliases {
                if !next.environment().contains(&declaration) {
                    return Err(refuse(format!(
                        "export of a private-only declaration `{}` requires hidden alias metadata",
                        declaration.to_display_string()
                    )));
                }
                next.environment =
                    fln_elab::aliases::register(next.environment(), &alias, &declaration)
                        .map_err(|error| refuse(error.to_string()))?;
            }
            return match public
                .publish(engine, next, Vec::new(), &scopes.public_scope(), options)
                .map_err(|error| command_error(file, command, fln_parse::BytePos(offset), error))?
            {
                Outcome::Complete(next) => {
                    *engine = next;
                    Ok(Outcome::Complete(()))
                }
                Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
            };
        }
        let mut environment = engine.environment.clone();
        for (alias, declaration) in aliases {
            environment = fln_elab::aliases::register(&environment, &alias, &declaration)
                .map_err(|error| refuse(format!("{error:?}")))?;
        }
        engine.environment = environment;
        return Ok(Outcome::Complete(()));
    }
    // `attribute [local simp] x`: a rule of `simp`'s default set until the enclosing scope ends,
    // validated as a registered rule is, and never registered.
    if let ScopeCommand::Simp(attribute) = &control
        && attribute.local
        && let Some((priority, reverse)) = attribute.rule
    {
        let (file, command, offset) = position;
        let refuse = |message: String| SourceCheckError::Scope {
            file,
            command,
            offset,
            message,
        };
        let environment = engine.environment();
        let mut rules = Vec::with_capacity(attribute.declarations.len());
        for requested in &attribute.declarations {
            let name = scopes
                .current
                .resolve(requested, |name| environment.contains(name))
                .map_err(|error| refuse(error.to_string()))?
                .ok_or_else(|| {
                    refuse(format!(
                        "unknown simp declaration `{}`",
                        requested.to_display_string()
                    ))
                })?;
            fln_elab::source::scope::simp::update(environment, &name, Some((priority, reverse)))
                .map_err(|error| {
                    command_error(
                        file,
                        command,
                        fln_parse::BytePos(offset),
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::SimpSet(error),
                            ),
                        )),
                    )
                })?;
            rules.push(fln_elab::source::scope::simp::SimpEntry {
                declaration: name,
                proof: None,
                priority,
                reverse,
                order: usize::MAX - scopes.current.local_simp.len() - rules.len(),
            });
        }
        scopes.current.local_simp.extend(rules);
        return Ok(Outcome::Complete(()));
    }
    // Erasure changes only the lexical selection state. In particular it must
    // not enter the persistent registration branch below or a module export.
    if let ScopeCommand::Instance(attribute) = &control
        && attribute.erase
    {
        let (file, command, offset) = position;
        if attribute.local || attribute.scoped || attribute.is_default {
            return Err(SourceCheckError::Scope {
                file,
                command,
                offset,
                message: "instance erasure has no registration kind".into(),
            });
        }
        if attribute.declarations.len() > 4096 {
            return Err(SourceCheckError::Limit {
                resource: "instance erasure declarations",
                limit: 4096,
            });
        }
        scopes
            .erase_instance_attribute(
                engine.environment(),
                public.as_ref().map(|world| world.engine().environment()),
                &attribute.declarations,
            )
            .map_err(|error| error.into_source(file, command, offset))?;
        return Ok(Outcome::Complete(()));
    }
    // `attribute [local instance] x`: selected until the enclosing scope ends, as a `local
    // instance` declaration is; nothing is written to the persistent registration journal.
    if let ScopeCommand::Instance(attribute) = &control
        && attribute.local
    {
        let (file, command, offset) = position;
        scopes
            .local_instance_attribute(
                engine.environment(),
                public.as_ref().map(|world| world.engine().environment()),
                &attribute.declarations,
                attribute.priority,
            )
            .map_err(|message| SourceCheckError::Scope {
                file,
                command,
                offset,
                message,
            })?;
        return Ok(Outcome::Complete(()));
    }
    if !matches!(
        control,
        ScopeCommand::Variable(_)
            | ScopeCommand::Instance(_)
            | ScopeCommand::Reducibility(_)
            | ScopeCommand::Executable(_)
            | ScopeCommand::Simp(_)
    ) {
        scopes
            .check_limits(&control)
            .map_err(|(resource, limit)| SourceCheckError::Limit { resource, limit })?;
        let (file, command, offset) = position;
        let namespace_command = matches!(control, ScopeCommand::Namespace(_));
        let transitioned = if let Some(public) = public.as_ref() {
            scopes.transition_worlds(
                control,
                engine.environment(),
                Some(public.engine().environment()),
            )
        } else {
            scopes.transition(control, engine.environment())
        };
        transitioned.map_err(|error| error.into_source(file, command, offset))?;
        if namespace_command {
            let register = |env: &Environment| {
                fln_elab::namespaces::register_source(env, &scopes.current.namespace).map_err(
                    |error| {
                        scopes::TransitionError::Registry(error).into_source(file, command, offset)
                    },
                )
            };
            if let Some(public) = public {
                let mut next = public.engine().clone();
                next.environment = register(next.environment())?;
                return match public
                    .publish(engine, next, Vec::new(), &scopes.public_scope(), options)
                    .map_err(|error| {
                        command_error(file, command, fln_parse::BytePos(offset), error)
                    })? {
                    Outcome::Complete(next) => {
                        *engine = next;
                        Ok(Outcome::Complete(()))
                    }
                    Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
                };
            }
            engine.environment = register(engine.environment())?;
        }
        return Ok(Outcome::Complete(()));
    }
    // Global default attributes export according to each candidate's visibility,
    // including commands written in a private section or mixing both worlds.
    if !scopes.current.exports_declaration()
        && let (ScopeCommand::Instance(attribute), Some(public)) = (&control, public.as_deref_mut())
        && attribute.is_default
    {
        let (file, command, offset) = position;
        let next = instance_attributes::apply(
            engine.environment(),
            &scopes.current,
            attribute.clone(),
            file,
            command,
            offset,
        )?;
        return match public
            .publish_default_attributes(engine, next)
            .map_err(|error| command_error(file, command, fln_parse::BytePos(offset), error))?
        {
            Outcome::Complete(next) => {
                *engine = next;
                Ok(Outcome::Complete(()))
            }
            Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
        };
    }
    let Some(public) = public.filter(|_| scopes.current.exports_declaration()) else {
        return apply_control_command(
            engine,
            &mut scopes.current,
            file_base,
            control,
            kernel,
            position,
        );
    };
    let mut scope = scopes.public_scope();
    let mut next = public.engine().clone();
    match apply_control_command(
        &mut next,
        &mut scope,
        public.file_base(),
        control,
        kernel,
        position,
    )? {
        Outcome::Complete(()) => {}
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    }
    let (file, command, offset) = position;
    match public
        .publish(engine, next, Vec::new(), &scope, options)
        .map_err(|error| command_error(file, command, fln_parse::BytePos(offset), error))?
    {
        Outcome::Complete(next) => {
            *engine = next;
            // Variable declarations are the only material control with a
            // lexical effect. Preserve the private journal's activation anchor.
            scopes.current.variables = scope.variables;
        }
        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
    }
    Ok(Outcome::Complete(()))
}

impl Engine {
    /// Check ordered, import-free declarations with native namespace, section,
    /// open and universe scopes. File boundaries restore source scope; checked
    /// declarations survive. Earlier declarations are available later. Imports,
    /// evaluation and queries are not silently ignored: the parser refuses them.
    /// Limits apply across the batch; each kernel check uses the supplied budget.
    pub fn check_source_files(
        &self,
        sources: &[&[u8]],
        options: &KVMap,
        limits: SourceCheckLimits,
    ) -> Result<Outcome<SourceFileCheck>, SourceCheckError> {
        self.check_source_files_recording(sources, options, limits, None, None, None, None, None)
    }

    // Module imports record only the candidates that survived ordinary admission.
    // The optional recorder is private and never returned on a failed batch.
    #[allow(clippy::too_many_arguments)]
    fn check_source_files_recording(
        &self,
        sources: &[&[u8]],
        options: &KVMap,
        limits: SourceCheckLimits,
        mut declarations: Option<&mut Vec<Declaration>>,
        private_module: Option<&Name>,
        source_module: Option<&Name>,
        mut public: Option<&mut modules::visibility::PublicWorld<'_>>,
        original_source: Option<(&[u8], fln_parse::BytePos)>,
    ) -> Result<Outcome<SourceFileCheck>, SourceCheckError> {
        if sources.is_empty() {
            return Err(SourceCheckError::EmptyInput);
        }
        if sources.len() > limits.max_commands {
            return Err(SourceCheckError::Limit {
                resource: "commands",
                limit: limits.max_commands,
            });
        }
        let mut bytes = 0_usize;
        for source in sources {
            bytes = bytes
                .checked_add(source.len())
                .filter(|n| *n <= limits.max_bytes)
                .ok_or(SourceCheckError::Limit {
                    resource: "source bytes",
                    limit: limits.max_bytes,
                })?;
        }
        let base_logical_root = self.logical_root(options);
        let mut engine = self.clone();
        let mut count = 0;
        let mut theorems = 0;
        let mut final_scope = engine.base_source_scope();
        for (file, source) in sources.iter().enumerate() {
            let (original, source_offset) =
                original_source.unwrap_or((source, fln_parse::BytePos(0)));
            let site = source_site(original)
                .map_err(|error| command_error(file, count, fln_parse::BytePos(0), error))?;
            // Global reducibility attributes may change only definitions authored
            // in this file, never declarations supplied by its predecessor.
            let file_base = engine.environment.clone();
            let mut scopes = scopes::Scopes::new(&engine);
            scopes.current.private_module = private_module.cloned();
            scopes.current.source_module = source_module.cloned();
            // The syntax this file declares extends the grammar of what follows it.
            let mut grammar = grammar::SourceGrammar::for_engine(
                &engine,
                source_module,
                private_module.is_some(),
            )
            .map_err(|error| command_error(file, count, fln_parse::BytePos(0), error))?;
            grammar.extend_scopes(&mut scopes);
            let commands = grammar.enter(|| partition_commands(source, file, count))?;
            if commands.len() > limits.max_commands.saturating_sub(count) {
                return Err(SourceCheckError::Limit {
                    resource: "commands",
                    limit: limits.max_commands,
                });
            }
            // A work list rather than a plain loop: `open A in <command>` expands in place to
            // the pin's `section open A <command> end`, whose scope steps are not commands of
            // their own (they neither count nor run elaboration).
            let mut queue: std::collections::VecDeque<SourceStep<'_>> =
                commands.into_iter().map(SourceStep::Command).collect();
            while let Some(step) = queue.pop_front() {
                let (start, command) = match step {
                    SourceStep::Command(command) => command,
                    SourceStep::Scope(start, transition) => {
                        grammar.observe(&transition);
                        scopes
                            .check_limits(&transition)
                            .map_err(|(resource, limit)| SourceCheckError::Limit {
                                resource,
                                limit,
                            })?;
                        scopes
                            .transition_worlds(
                                transition,
                                engine.environment(),
                                public.as_ref().map(|world| world.engine().environment()),
                            )
                            .map_err(|error| error.into_source(file, count, start.0))?;
                        continue;
                    }
                };
                scopes.current.source_site =
                    Some(site.at_offset(fln_parse::BytePos(source_offset.0 + start.0)));
                let control =
                    grammar.enter(|| parse_control_command(command, start, file, count))?;
                if let Some(control) = control {
                    if matches!(control, fln_parse::command_scope::ScopeCommand::Trivia) {
                        continue;
                    }
                    if let fln_parse::command_scope::ScopeCommand::In { head, body } = control {
                        for step in in_command_steps(start, command, head, body)
                            .into_iter()
                            .rev()
                        {
                            queue.push_front(step);
                        }
                        continue;
                    }
                    let expanded = match control {
                        fln_parse::command_scope::ScopeCommand::OpenIn {
                            names,
                            scoped,
                            body,
                        } => Ok((
                            if scoped {
                                fln_parse::command_scope::ScopeCommand::OpenScoped(names)
                            } else {
                                fln_parse::command_scope::ScopeCommand::Open(names)
                            },
                            body,
                        )),
                        fln_parse::command_scope::ScopeCommand::SetOptionIn {
                            name,
                            value,
                            body,
                        } => Ok((
                            fln_parse::command_scope::ScopeCommand::SetOption { name, value },
                            body,
                        )),
                        // A check-only pass prints nothing, so it cannot judge a guard's
                        // messages: a non-answer, not an unjudged acceptance.
                        fln_parse::command_scope::ScopeCommand::GuardMsgs { .. } => {
                            return Err(SourceCheckError::Command {
                                file,
                                command: count,
                                offset: start.0,
                                error: Box::new(EngineExecutionError::NotImplemented {
                                    feature: "`#guard_msgs` outside the `lean` front door",
                                }),
                            });
                        }
                        other => Err(other),
                    };
                    let control = match expanded {
                        Ok((scope, body)) => {
                            for step in in_steps(start, command, scope, body).into_iter().rev() {
                                queue.push_front(step);
                            }
                            continue;
                        }
                        Err(control) => control,
                    };
                    grammar.observe(&control);
                    match apply_module_control_command(
                        &mut engine,
                        &mut scopes,
                        &file_base,
                        control,
                        limits.admission.kernel,
                        (file, count, start.0),
                        public.as_deref_mut(),
                        options,
                    )? {
                        Outcome::Complete(()) => {}
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    }
                    count += 1;
                    continue;
                }
                // A command that declares syntax extends the grammar and admits nothing.
                if grammar
                    .declare(
                        command,
                        grammar::resolver(engine.environment(), &scopes.current),
                    )
                    .map_err(|error| command_error(file, count, start, error))?
                {
                    grammar.extend_scopes(&mut scopes);
                    count += 1;
                    continue;
                }
                let scope = if public.is_some() {
                    grammar
                        .enter(|| scopes.command_scope(command))
                        .map_err(EngineExecutionError::Frontend)
                        .map_err(|error| command_error(file, count, start, error))?
                } else {
                    scopes.current.clone()
                };
                let exported = scope.exports_declaration() && public.is_some();
                let (next, admitted) = if exported {
                    match grammar
                        .enter(|| {
                            public
                                .as_deref_mut()
                                .expect("public module receipt")
                                .admit_command(
                                    &engine,
                                    command,
                                    options,
                                    limits.admission,
                                    &scope,
                                    &scopes.current,
                                )
                        })
                        .map_err(|error| command_error(file, count, start, error))?
                    {
                        Outcome::Complete(result) => result,
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    }
                } else {
                    match grammar
                        .enter(|| {
                            engine.admit_source_command_in_scope(
                                command,
                                options,
                                limits.admission,
                                &scope,
                            )
                        })
                        .map_err(|error| command_error(file, count, start, error))?
                    {
                        Outcome::Complete(admitted) => (admitted.engine.clone(), admitted),
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    }
                };
                theorems += admitted
                    .admissions
                    .iter()
                    .filter(|row| matches!(row.declaration, Declaration::Thm(_)))
                    .count();
                scopes
                    .admitted_batch(
                        &admitted,
                        next.environment(),
                        public
                            .as_deref()
                            .filter(|_| exported)
                            .map(|world| world.engine().environment()),
                    )
                    .map_err(|error| error.into_source(file, count, start.0))?;
                for row in &admitted.admissions {
                    if let Some(journal) = declarations.as_deref_mut() {
                        journal.push(row.declaration.clone());
                    }
                }
                engine = next;
                count += 1;
            }
            if let Some(public) = public.as_deref_mut() {
                public.retain_scope(scopes.public_scope());
            }
            if source_module.is_some() {
                engine.environment = grammar.record(engine.environment()).map_err(|error| {
                    command_error(file, count, fln_parse::BytePos(source.len()), error)
                })?;
            }
            final_scope = scopes.current;
        }
        Ok(Outcome::Complete(SourceFileCheck {
            result_logical_root: engine.logical_root(options),
            engine,
            files: sources.len(),
            commands: count,
            theorems,
            base_logical_root,
            scope: final_scope,
        }))
    }
}

/// Refuse a source batch that no environment could make parseable, before any
/// environment exists.
///
/// Runs every parser [`Engine::check_source_files`] runs, in the same order
/// and with the same error construction, and skips only elaboration. Each of
/// those parsers reads nothing but the command's bytes, so a refusal here is
/// the refusal the checked path reaches, with the same error. Success proves
/// nothing about elaboration. The checked path elaborates as it goes, so when
/// an earlier command fails elaboration and a later one fails to parse, it
/// reports the elaboration failure while this reports the parse failure;
/// either way the batch is refused.
///
/// Front doors call this before admitting an import closure, so malformed
/// source is refused before any `.olean` is read or checked.
pub fn preflight_source_files(sources: &[&[u8]]) -> Result<(), SourceCheckError> {
    let mut count = 0;
    for (file, source) in sources.iter().enumerate() {
        let mut grammar = grammar::SourceGrammar::implicit_init();
        for (mut start, mut command) in grammar.enter(|| partition_commands(source, file, count))? {
            // `open A in <command>`: the inner command is parsed as the checked path parses
            // it, at its own offset; the open itself is one command with it.
            loop {
                match grammar.enter(|| parse_control_command(command, start, file, count))? {
                    Some(fln_parse::command_scope::ScopeCommand::Trivia) => {}
                    Some(
                        fln_parse::command_scope::ScopeCommand::OpenIn { body, .. }
                        | fln_parse::command_scope::ScopeCommand::SetOptionIn { body, .. }
                        | fln_parse::command_scope::ScopeCommand::GuardMsgs { body, .. }
                        | fln_parse::command_scope::ScopeCommand::In { body, .. },
                    ) => {
                        start = fln_parse::BytePos(start.0 + body);
                        command = &command[body..];
                        continue;
                    }
                    Some(scope) => {
                        grammar.observe(&scope);
                        count += 1;
                    }
                    None => {
                        // A syntax declaration is registered, not parsed as a declaration;
                        // with no environment yet, its precheck is the checked path's.
                        let declared = grammar
                            .declare(command, |_| grammar::Resolution::Unchecked)
                            .map_err(|error| command_error(file, count, start, error))?;
                        if !declared {
                            grammar
                                .enter(|| crate::source_records::parse_scoped_command(command))
                                .map_err(|error| command_error(file, count, start, error))?;
                        }
                        count += 1;
                    }
                }
                break;
            }
        }
    }
    Ok(())
}

/// [`preflight_source_files`] for one source module, reporting header and body
/// failures, and body positions relative to the whole module, exactly as
/// [`Engine::check_source_modules`] does.
pub fn preflight_source_module(
    module: &Name,
    source: &[u8],
) -> Result<(), modules::SourceModuleCheckError> {
    let header = modules::parse_source_header(source).map_err(|error| {
        modules::SourceModuleCheckError::Header {
            module: module.clone(),
            error,
        }
    })?;
    modules::validate_source_header(module, &header)?;
    let body = &source[header.body_start.0..];
    if body.is_empty() {
        return Ok(());
    }
    preflight_source_files(&[body]).map_err(|mut error| {
        if let SourceCheckError::Scope { offset, .. } | SourceCheckError::Command { offset, .. } =
            &mut error
        {
            *offset = offset.saturating_add(header.body_start.0);
        }
        modules::SourceModuleCheckError::Source {
            module: module.clone(),
            error,
        }
    })
}

/// One unit of a source file's command loop: a command's own bytes at its offset, or a scope
/// transition that an enclosing command implies.
enum SourceStep<'source> {
    Command((fln_parse::BytePos, &'source [u8])),
    Scope(fln_parse::BytePos, fln_parse::command_scope::ScopeCommand),
}

/// `open A in <command>` as the pin's `Command.in` macro elaborates it: `section`, `open A`,
/// the command, `end`. The command keeps its true offset in the file.
/// The same macro serves `set_option o v in <command>`, with `set_option o v` as `scope`.
fn in_steps<'source>(
    start: fln_parse::BytePos,
    command: &'source [u8],
    scope: fln_parse::command_scope::ScopeCommand,
    body: usize,
) -> [SourceStep<'source>; 4] {
    use fln_parse::command_scope::ScopeCommand;
    [
        SourceStep::Scope(start, ScopeCommand::Section(None)),
        SourceStep::Scope(start, scope),
        SourceStep::Command((fln_parse::BytePos(start.0 + body), &command[body..])),
        SourceStep::Scope(start, ScopeCommand::End(None)),
    ]
}

/// `<head> in <body>` (`Lean.Parser.Command.in`): the pin's `section <head> <body> end`, each
/// command at its own offset.
fn in_command_steps<'source>(
    start: fln_parse::BytePos,
    command: &'source [u8],
    head: usize,
    body: usize,
) -> [SourceStep<'source>; 4] {
    use fln_parse::command_scope::ScopeCommand;
    [
        SourceStep::Scope(start, ScopeCommand::Section(None)),
        SourceStep::Command((start, &command[..head])),
        SourceStep::Command((fln_parse::BytePos(start.0 + body), &command[body..])),
        SourceStep::Scope(start, ScopeCommand::End(None)),
    ]
}

fn partition_commands(
    source: &[u8],
    file: usize,
    count: usize,
) -> Result<Vec<(fln_parse::BytePos, &[u8])>, SourceCheckError> {
    fln_parse::command_scope::partition(source).map_err(|error| SourceCheckError::Command {
        file,
        command: count,
        offset: error.primary_offset().map_or(0, |at| at.0),
        error: Box::new(EngineExecutionError::Frontend(
            DefinitionFrontendError::Parse(error),
        )),
    })
}

fn parse_control_command(
    command: &[u8],
    start: fln_parse::BytePos,
    file: usize,
    count: usize,
) -> Result<Option<fln_parse::command_scope::ScopeCommand>, SourceCheckError> {
    fln_parse::command_scope::parse(command).map_err(|error| SourceCheckError::Command {
        file,
        command: count,
        offset: start
            .0
            .saturating_add(error.primary_offset().map_or(0, |at| at.0)),
        error: Box::new(EngineExecutionError::Frontend(
            DefinitionFrontendError::Parse(error),
        )),
    })
}

fn command_error(
    file: usize,
    count: usize,
    start: fln_parse::BytePos,
    error: EngineExecutionError,
) -> SourceCheckError {
    SourceCheckError::Command {
        file,
        command: count,
        offset: start
            .0
            .saturating_add(error.primary_source_offset().map_or(0, |at| at.0)),
        error: Box::new(error),
    }
}
