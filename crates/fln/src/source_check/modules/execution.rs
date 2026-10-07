//! Execute source in each module's actual, council-admitted import world.
//! Imported library definitions reach the ordinary native compiler on demand.
//! Source exports retain declarations and metadata; evaluation candidates and
//! scratch queries never become another module's declarations.
use super::*;
use crate::{EngineExecutionLimits, SourceCommandBatchExecution};

#[derive(Debug, Clone, Copy)]
pub struct SourceProgramLimits {
    pub execution: EngineExecutionLimits,
    pub modules: SourceModuleCheckLimits,
}

impl SourceProgramLimits {
    pub fn new(execution: EngineExecutionLimits) -> Self {
        Self {
            execution,
            modules: SourceModuleCheckLimits::new(SourceCheckLimits::new(execution.admission())),
        }
    }
}

/// A module's own command stream, checked against its exact import context.
#[derive(Debug)]
pub struct SourceModuleExecution {
    pub module: Name,
    pub commands: SourceCommandBatchExecution,
}

/// Dependency-first executions, with the entry last. Each module has its own
/// base and successor: sibling environments are not a single publication chain.
/// A presentation must inspect every VM exit before exposing buffered output.
#[derive(Debug)]
pub struct SourceProgramExecution {
    pub modules: Vec<SourceModuleExecution>,
}

fn source_error(module: &Name, error: EngineExecutionError) -> SourceModuleCheckError {
    let (command, offset, error) = match error {
        EngineExecutionError::BatchCommand { index, at, error } => {
            (index, at.map_or(0, |at| at.0), error)
        }
        error => (
            0,
            error.primary_source_offset().map_or(0, |at| at.0),
            Box::new(error),
        ),
    };
    SourceModuleCheckError::Source {
        module: module.clone(),
        error: SourceCheckError::Command {
            file: 0,
            command,
            offset,
            error,
        },
    }
}

fn parse_error(
    module: &Name,
    command: usize,
    at: fln_parse::BytePos,
    error: DefinitionParseError,
) -> SourceModuleCheckError {
    source_error(
        module,
        EngineExecutionError::BatchCommand {
            index: command,
            at: Some(at),
            error: Box::new(EngineExecutionError::Frontend(
                DefinitionFrontendError::Parse(error.with_original_offset(at)),
            )),
        },
    )
}

fn commands<'a>(
    module: &Name,
    source: &'a [u8],
    header: &SourceHeader,
) -> Result<Vec<(fln_parse::BytePos, &'a [u8])>, SourceModuleCheckError> {
    fln_parse::command_scope::partition(&source[header.body_start.0..])
        .map(|commands| {
            commands
                .into_iter()
                .filter(|(_, bytes)| {
                    !matches!(
                        fln_parse::command_scope::parse(bytes),
                        Ok(Some(fln_parse::command_scope::ScopeCommand::Trivia))
                    )
                })
                .map(|(at, bytes)| (fln_parse::BytePos(header.body_start.0 + at.0), bytes))
                .collect()
        })
        .map_err(|error| parse_error(module, 0, header.body_start, error))
}

/// Parse the same mixed command grammar as execution before admitting a costly
/// import closure. This performs no elaboration, execution or publication.
pub fn preflight_source_program(
    modules: &[SourceModuleInput<'_>],
    limits: SourceModuleCheckLimits,
) -> Result<(), SourceModuleCheckError> {
    if modules.len() > limits.max_modules {
        return Err(SourceModuleCheckError::Limit {
            resource: "modules",
            limit: limits.max_modules,
        });
    }
    let mut bytes = 0usize;
    let mut count = 0usize;
    for module in modules {
        bytes = bytes
            .checked_add(module.source.len())
            .filter(|n| *n <= limits.source.max_bytes)
            .ok_or(SourceModuleCheckError::Limit {
                resource: "source bytes",
                limit: limits.source.max_bytes,
            })?;
        let header =
            parse_source_header(module.source).map_err(|error| SourceModuleCheckError::Header {
                module: module.name.clone(),
                error,
            })?;
        for (index, (mut at, mut bytes)) in commands(module.name, module.source, &header)?
            .into_iter()
            .enumerate()
        {
            count = count
                .checked_add(1)
                .filter(|n| *n <= limits.source.max_commands)
                .ok_or(SourceModuleCheckError::Limit {
                    resource: "source commands",
                    limit: limits.source.max_commands,
                })?;
            loop {
                match fln_parse::command_scope::parse(bytes)
                    .map_err(|error| parse_error(module.name, index, at, error))?
                {
                    Some(fln_parse::command_scope::ScopeCommand::OpenIn { body, .. }) => {
                        at.0 += body;
                        bytes = &bytes[body..];
                    }
                    Some(_) => break,
                    None => {
                        if fln_parse::command_scope::mutual::parse(bytes)
                            .map_err(|error| parse_error(module.name, index, at, error))?
                            .is_none()
                        {
                            fln_parse::parse_source_command(bytes)
                                .map_err(|error| parse_error(module.name, index, at, error))?;
                        }
                        break;
                    }
                }
            }
        }
    }
    Ok(())
}

fn declarations(
    completed: &SourceCommandBatchExecution,
    meter: &mut Meter,
) -> Result<Vec<Declaration>, SourceModuleCheckError> {
    let mut ordered = BTreeMap::<usize, Vec<Declaration>>::new();
    let evaluations: std::collections::BTreeSet<_> = completed
        .batch
        .source_evaluation_indices
        .iter()
        .copied()
        .collect();
    for (index, (&command, execution)) in completed
        .execution_command_indices
        .iter()
        .zip(&completed.batch.executions)
        .enumerate()
    {
        meter.work(1)?;
        if !evaluations.contains(&index) {
            ordered
                .entry(command)
                .or_default()
                .push(execution.declaration.clone());
        }
    }
    for admission in &completed.batch.source_admissions {
        for checked in &admission.admission.admissions {
            meter.work(1)?;
            ordered
                .entry(admission.command_index)
                .or_default()
                .push(checked.declaration.clone());
        }
    }
    Ok(ordered.into_values().flatten().collect())
}

impl imported::SourceOleanImport {
    /// An empty import world for explicit `prelude` programs. No declaration,
    /// metadata registration or imported module is installed. The private
    /// contexts retain that empty world independently of the public reports.
    pub fn empty(options: &KVMap) -> Self {
        let engine = Engine::from_environment(Environment::new());
        let root = engine.logical_root(options);
        let checked = CheckedOleanSet {
            engine: engine.clone(),
            base_logical_root: root,
            result_logical_root: root,
            modules: Vec::new(),
        };
        let contexts =
            contexts::ImportContexts::capture(&engine, &engine, &checked, BTreeMap::new());
        Self {
            contexts,
            engine,
            checked,
            result_logical_root: root,
            modules: Vec::new(),
        }
    }

    /// Compile and run an explicit source import graph against this receipt's
    /// private checked contexts. An imported declaration is executable library
    /// input, never an upstream runtime component. No seed is installed.
    ///
    /// Every source module starts with exactly its transitive imports. Local
    /// registrations and artifact metadata replay in declared import order.
    /// Dependencies execute once; only their real declarations and exported
    /// metadata are replayed into consumers. Failure returns no partial program
    /// or successor, and cancellation is observed at module/replay boundaries.
    pub fn execute_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceProgramLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceProgramExecution>, SourceModuleCheckError> {
        self.execute_source_modules_with_implicit_init(
            modules,
            entry,
            options,
            limits,
            cancellation,
            false,
        )
    }

    /// Compile and run ordinary Lean source modules, including the implicit
    /// `Init` dependency of every module that does not declare `prelude`.
    /// `Init` must be supplied by this receipt or the source graph; the method
    /// never installs a seed or obtains authority from the public reports.
    ///
    /// The implicit import is a graph edge, not a change to the source bytes.
    /// Source budgets and diagnostic positions refer to the original input.
    /// Execution, import isolation and cancellation follow
    /// [`Self::execute_source_modules`].
    pub fn execute_lean_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceProgramLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceProgramExecution>, SourceModuleCheckError> {
        self.execute_source_modules_with_implicit_init(
            modules,
            entry,
            options,
            limits,
            cancellation,
            true,
        )
    }

    fn execute_source_modules_with_implicit_init(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceProgramLimits,
        cancellation: Option<&dyn CancellationProbe>,
        implicit_init: bool,
    ) -> Result<Outcome<SourceProgramExecution>, SourceModuleCheckError> {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-program/before-plan",
            )));
        }
        preflight_source_program(modules, limits.modules)?;
        let mut meter = Meter {
            work: 0,
            bytes: 0,
            limits: limits.modules,
        };
        let plan = graph::Plan::with_implicit_init(
            modules,
            entry,
            self.contexts.complete.imported_modules(),
            &mut meter,
            implicit_init,
        )?;
        let mut exports = BTreeMap::<usize, replay::Export>::new();
        let mut completed_modules = Vec::new();
        for &index in &plan.order {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "source-program/before-module",
                )));
            }
            let steps = self.contexts.order(index, &plan, modules, &mut meter)?;
            let mut engine = match self.contexts.project(&steps, &mut meter, cancellation)? {
                Outcome::Complete(engine) => engine,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            for step in &steps {
                let replayed = match step {
                    contexts::Step::External(name) => self.contexts.replay_metadata(
                        name,
                        engine,
                        options,
                        &mut meter,
                        cancellation,
                    )?,
                    contexts::Step::Source(dependency) => exports
                        .get(dependency)
                        .expect("postorder source predecessor")
                        .replay(
                            engine,
                            modules[*dependency].name,
                            options,
                            &mut meter,
                            cancellation,
                        )?,
                };
                engine = match replayed {
                    Outcome::Complete(engine) => engine,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
            }
            let module = modules[index];
            let body = commands(module.name, module.source, &plan.headers[index])?;
            let completed = if body.is_empty() {
                engine.empty_source_command_execution(options)
            } else {
                match engine
                    .execute_source_command_stream(body, options, limits.execution, true)
                    .map_err(|error| source_error(module.name, error))?
                {
                    Outcome::Complete(completed) => completed,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                }
            };
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "source-program/after-module",
                )));
            }
            if index != plan.entry {
                let declarations = declarations(&completed, &mut meter)?;
                exports.insert(
                    index,
                    replay::Export::capture(
                        module.name,
                        engine.environment(),
                        completed.batch.engine.environment(),
                        declarations,
                        &mut meter,
                    )?,
                );
            }
            completed_modules.push(SourceModuleExecution {
                module: module.name.clone(),
                commands: completed,
            });
        }
        Ok(Outcome::Complete(SourceProgramExecution {
            modules: completed_modules,
        }))
    }
}
