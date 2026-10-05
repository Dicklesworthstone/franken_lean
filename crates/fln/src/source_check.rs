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
        EngineExecutionError::CouncilHalted { .. }
        | EngineExecutionError::CouncilNoAnswer { .. } => ("inconclusive", false, 3),
        EngineExecutionError::CheckerBridge { .. }
        | EngineExecutionError::UnexpectedPublication { .. } => ("internal-fault", false, 4),
        EngineExecutionError::AllocationFailure { .. } => ("resource", false, 3),
        EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
            NatDefinitionElabError::Inference(reason),
        )) => match reason {
            SourceInferenceError::SimpSet(
                fln_elab::source::scope::simp::SimpSetError::Malformed,
            )
            | SourceInferenceError::ProtectedJournal(
                fln_elab::protected_names::ProtectedError::Malformed,
            ) => ("internal-fault", false, 4),
            SourceInferenceError::ResourceLimit
            | SourceInferenceError::SimpSet(fln_elab::source::scope::simp::SimpSetError::Limit)
            | SourceInferenceError::ProtectedJournal(
                fln_elab::protected_names::ProtectedError::Limit,
            )
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
        let mut final_scope = fln_elab::source::scope::SourceScope::default();
        for (file, source) in sources.iter().enumerate() {
            let mut scopes = scopes::Scopes::new(engine.environment());
            let commands = partition_commands(source, file, count)?;
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
                        scopes
                            .check_limits(&transition)
                            .map_err(|(resource, limit)| SourceCheckError::Limit {
                                resource,
                                limit,
                            })?;
                        scopes
                            .transition(transition, engine.environment())
                            .map_err(|error| error.into_source(file, count, start.0))?;
                        continue;
                    }
                };
                let control = parse_control_command(command, start, file, count)?;
                if let Some(control) = control {
                    if matches!(control, fln_parse::command_scope::ScopeCommand::Trivia) {
                        continue;
                    }
                    if let fln_parse::command_scope::ScopeCommand::OpenIn {
                        names,
                        scoped,
                        body,
                    } = control
                    {
                        for step in open_in_steps(start, command, names, scoped, body)
                            .into_iter()
                            .rev()
                        {
                            queue.push_front(step);
                        }
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
                        .transition(control, engine.environment())
                        .map_err(|error| error.into_source(file, count, start.0))?;
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
                    .map_err(|error| command_error(file, count, start, error))?;
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
        for (mut start, mut command) in partition_commands(source, file, count)? {
            // `open A in <command>`: the inner command is parsed as the checked path parses
            // it, at its own offset; the open itself is one command with it.
            loop {
                match parse_control_command(command, start, file, count)? {
                    Some(fln_parse::command_scope::ScopeCommand::Trivia) => {}
                    Some(fln_parse::command_scope::ScopeCommand::OpenIn { body, .. }) => {
                        start = fln_parse::BytePos(start.0 + body);
                        command = &command[body..];
                        continue;
                    }
                    Some(_) => count += 1,
                    None => {
                        crate::source_records::parse_scoped_command(command)
                            .map_err(|error| command_error(file, count, start, error))?;
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
fn open_in_steps<'source>(
    start: fln_parse::BytePos,
    command: &'source [u8],
    names: Vec<Name>,
    scoped: bool,
    body: usize,
) -> [SourceStep<'source>; 4] {
    use fln_parse::command_scope::ScopeCommand;
    let open = if scoped {
        ScopeCommand::OpenScoped(names)
    } else {
        ScopeCommand::Open(names)
    };
    [
        SourceStep::Scope(start, ScopeCommand::Section(None)),
        SourceStep::Scope(start, open),
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
