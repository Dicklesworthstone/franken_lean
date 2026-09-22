//! Admission-only source batches. No compiler, VM, or artifact publication.
use super::*;
pub mod inspect;
mod instance_attributes;
pub mod modules;
mod scopes;

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
    /// Wire classification never turns a frontend resource stop into rejection.
    pub fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::EmptyInput | Self::Scope { .. } => ("input", false, 1),
            Self::Limit { .. } => ("resource", false, 3),
            Self::Command { error, .. } => classify(error),
        }
    }
}
fn classify(error: &EngineExecutionError) -> (&'static str, bool, u8) {
    use fln_elab::constraint::unify::UnificationError;
    use fln_elab::universe::UniverseInstantiationError;
    use fln_elab::{NatDefinitionElabError, source::SourceInferenceError};
    match error {
        EngineExecutionError::BatchCommand { error, .. } => classify(error),
        EngineExecutionError::KernelRejected { .. } => ("kernel-rejection", true, 1),
        EngineExecutionError::CouncilHalted { .. } => ("inconclusive", false, 3),
        EngineExecutionError::CheckerBridge { .. }
        | EngineExecutionError::UnexpectedPublication { .. } => ("internal-fault", false, 4),
        EngineExecutionError::AllocationFailure { .. } => ("resource", false, 3),
        EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
            NatDefinitionElabError::Inference(reason),
        )) => match reason {
            SourceInferenceError::SimpSet(
                fln_elab::source::scope::simp::SimpSetError::Malformed,
            ) => ("internal-fault", false, 4),
            SourceInferenceError::ResourceLimit
            | SourceInferenceError::SimpSet(fln_elab::source::scope::simp::SimpSetError::Limit)
            | SourceInferenceError::Record(fln_elab::records::RecordError::ResourceLimit)
            | SourceInferenceError::Inductive(fln_elab::inductive::InductiveError::ResourceLimit)
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
        _ => ("input", false, 1),
    }
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
        self.check_source_files_recording(sources, options, limits, None)
    }

    // Module imports record only the candidates that survived ordinary admission.
    // The optional recorder is private and never returned on a failed batch.
    fn check_source_files_recording(
        &self,
        sources: &[&[u8]],
        options: &KVMap,
        limits: SourceCheckLimits,
        mut declarations: Option<&mut Vec<Declaration>>,
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
        for (file, source) in sources.iter().enumerate() {
            let mut scopes = scopes::Scopes::new(engine.environment());
            let commands = fln_parse::command_scope::partition(source).map_err(|error| {
                SourceCheckError::Command {
                    file,
                    command: count,
                    offset: error.primary_offset().map_or(0, |at| at.0),
                    error: Box::new(EngineExecutionError::Frontend(
                        DefinitionFrontendError::Parse(error),
                    )),
                }
            })?;
            if commands.len() > limits.max_commands.saturating_sub(count) {
                return Err(SourceCheckError::Limit {
                    resource: "commands",
                    limit: limits.max_commands,
                });
            }
            for (start, command) in commands {
                let control = fln_parse::command_scope::parse(command).map_err(|error| {
                    SourceCheckError::Command {
                        file,
                        command: count,
                        offset: start
                            .0
                            .saturating_add(error.primary_offset().map_or(0, |at| at.0)),
                        error: Box::new(EngineExecutionError::Frontend(
                            DefinitionFrontendError::Parse(error),
                        )),
                    }
                })?;
                if let Some(control) = control {
                    if matches!(control, fln_parse::command_scope::ScopeCommand::Trivia) {
                        continue;
                    }
                    if let fln_parse::command_scope::ScopeCommand::Variable(syntax) = control {
                        scopes.current.variables = fln_elab::source::scope::variables::declare(
                            &syntax,
                            engine.environment(),
                            limits.admission.kernel,
                            &scopes.current,
                        )
                        .map_err(|error| SourceCheckError::Command {
                            file,
                            command: count,
                            offset: start.0,
                            error: Box::new(EngineExecutionError::Frontend(
                                DefinitionFrontendError::Elaborate(error),
                            )),
                        })?;
                        count += 1;
                        continue;
                    }
                    if let fln_parse::command_scope::ScopeCommand::Instance(attribute) = control {
                        engine.environment = instance_attributes::apply(
                            engine.environment(),
                            &scopes.current,
                            attribute,
                            file,
                            count,
                            start.0,
                        )?;
                        count += 1;
                        continue;
                    }
                    if let fln_parse::command_scope::ScopeCommand::Simp(attribute) = control {
                        // Attribute resolution uses the current source scope,
                        // but the journal records exact declaration identities.
                        // Publish the entire command only after every name and
                        // registration succeeds; late failure exposes no prefix.
                        let mut environment = engine.environment.clone();
                        for requested in attribute.declarations {
                            let name = scopes
                                .current
                                .resolve(&requested, |name| environment.contains(name))
                                .map_err(|error| SourceCheckError::Scope {
                                    file,
                                    command: count,
                                    offset: start.0,
                                    message: error.to_string(),
                                })?
                                .ok_or_else(|| SourceCheckError::Scope {
                                    file,
                                    command: count,
                                    offset: start.0,
                                    message: format!(
                                        "unknown simp declaration `{}`",
                                        requested.to_display_string()
                                    ),
                                })?;
                            environment = fln_elab::source::scope::simp::update(
                                &environment,
                                &name,
                                attribute.rule,
                            )
                            .map_err(|error| {
                                SourceCheckError::Command {
                                    file,
                                    command: count,
                                    offset: start.0,
                                    error: Box::new(EngineExecutionError::Frontend(
                                        DefinitionFrontendError::Elaborate(
                                            fln_elab::NatDefinitionElabError::Inference(
                                                fln_elab::source::SourceInferenceError::SimpSet(
                                                    error,
                                                ),
                                            ),
                                        ),
                                    )),
                                }
                            })?;
                        }
                        engine.environment = environment;
                        count += 1;
                        continue;
                    }
                    scopes
                        .check_limits(&control)
                        .map_err(|(resource, limit)| SourceCheckError::Limit { resource, limit })?;
                    scopes
                        .apply(control)
                        .map_err(|message| SourceCheckError::Scope {
                            file,
                            command: count,
                            offset: start.0,
                            message,
                        })?;
                    count += 1;
                    continue;
                }
                let result = engine
                    .admit_source_command_in_scope(
                        command,
                        options,
                        limits.admission,
                        &scopes.current,
                    )
                    .map_err(|error| SourceCheckError::Command {
                        file,
                        command: count,
                        offset: start
                            .0
                            .saturating_add(error.primary_source_offset().map_or(0, |at| at.0)),
                        error: Box::new(error),
                    })?;
                let admitted = match result {
                    Outcome::Complete(admitted) => admitted,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                theorems += admitted
                    .admissions
                    .iter()
                    .filter(|row| matches!(row.declaration, Declaration::Thm(_)))
                    .count();
                for row in &admitted.admissions {
                    scopes.admitted(&row.declaration);
                    if let Some(journal) = declarations.as_deref_mut() {
                        journal.push(row.declaration.clone());
                    }
                }
                engine = admitted.engine;
                count += 1;
            }
        }
        Ok(Outcome::Complete(SourceFileCheck {
            result_logical_root: engine.logical_root(options),
            engine,
            files: sources.len(),
            commands: count,
            theorems,
            base_logical_root,
        }))
    }
}
