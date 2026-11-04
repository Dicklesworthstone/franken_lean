//! Imported macros bound to each source module's exact checked import world.
//!
//! Registrations come from the receipt's retained journals. Every module starts
//! from the supplied MacroM state and its own quotation context, while expansion
//! work shares one graph-wide allowance. Only a complete graph publishes states.

use super::execution::{SourceProgramExecution, SourceProgramExecutionError, SourceProgramLimits};
use super::*;
use crate::imported_ir::VerifiedPartition;
use crate::imported_macros::registrations::{
    MacroAttempt, MacroCompilationInputs, MacroRegistrationError, MacroRegistryLimits,
    MacroTreeLimits, MacroTreeUsage, RegisteredMacros,
};
use crate::imported_macros::source::{
    FileSession, FileSessionReport, SourceMacroError, SourceMacroInvocation,
};
use crate::imported_macros::{MacroContext, MacroState};
use crate::imported_parsers::{ParserRegistrationError, ParserRegistryLimits, RegisteredParsers};
use fln_env::modules::CancellationProbe as ModuleCancellationProbe;
use fln_olean::ir::IrModule;
use fln_vm::interpreter::{CancellationProbe, ExecutionUsage};
use std::collections::BTreeSet;

/// Explicit compilation inputs, initial MacroM state and expansion ceilings.
/// The receipt supplies the complete registrations; callers cannot substitute
/// a partial registry or an ambient native lookup environment.
pub struct SourceModuleMacroInputs<'a> {
    pub code: &'a [IrModule],
    pub partition: &'a VerifiedPartition,
    pub user_declarations: &'a BTreeSet<Name>,
    pub registry_limits: MacroRegistryLimits,
    /// Initial recursion and hygiene coordinates. Each module replaces only
    /// `quotation_context` with its own name. This bounded source adapter does
    /// not implement the pin frontend's command-hash hygiene seed.
    pub context: MacroContext,
    /// Independently cloned for each source module, never inherited from its
    /// imports or a previously checked sibling.
    pub state: MacroState,
    /// Attempts, VM steps, visits and generated syntax accumulate over the
    /// complete source graph, including modules preceding a failed module.
    pub limits: MacroTreeLimits,
}

/// Owned compilation inputs for source modules that compile imported macros on
/// first use. Context, initial state and graph-wide expansion limits have the
/// same meaning as in `SourceModuleMacroInputs`. No partial registration table
/// can be supplied: the receipt still provides every captured journal.
pub struct SourceModuleDeferredMacroInputs {
    pub compilation: MacroCompilationInputs,
    pub registry_limits: MacroRegistryLimits,
    pub context: MacroContext,
    pub state: MacroState,
    pub limits: MacroTreeLimits,
}

/// A module graph admitted through the ordinary council path after expansion.
/// Failure retains actual macro work, but publishes neither a checked prefix
/// nor any terminal module state. Scoped activation is local to each module.
#[derive(Debug)]
pub struct SourceMacroModuleCheck {
    pub outcome: Outcome<Result<SourceModuleCheck, SourceModuleCheckError>>,
    pub states: Option<BTreeMap<Name, MacroState>>,
    pub attempts: Vec<MacroAttempt>,
    pub completed_vm_usage: ExecutionUsage,
    pub tree_usage: MacroTreeUsage,
}

/// Executed source modules and the macro work consumed by their real command
/// streams. A failed module, caller validation, cancellation or macro resource
/// stop exposes neither a partial program nor terminal module states. Runtime
/// stops retain the ordinary program evidence, but withhold terminal states.
#[derive(Debug)]
pub struct SourceMacroProgramExecution<E = std::convert::Infallible> {
    pub outcome: Outcome<Result<SourceProgramExecution, SourceProgramExecutionError<E>>>,
    pub states: Option<BTreeMap<Name, MacroState>>,
    pub attempts: Vec<MacroAttempt>,
    pub completed_vm_usage: ExecutionUsage,
    pub tree_usage: MacroTreeUsage,
}

impl<E> SourceMacroProgramExecution<E> {
    fn stopped(
        outcome: Outcome<Result<SourceProgramExecution, SourceProgramExecutionError<E>>>,
    ) -> Self {
        Self {
            outcome,
            states: None,
            attempts: Vec::new(),
            completed_vm_usage: empty_usage(),
            tree_usage: MacroTreeUsage::default(),
        }
    }
}

impl SourceMacroModuleCheck {
    fn stopped(outcome: Outcome<Result<SourceModuleCheck, SourceModuleCheckError>>) -> Self {
        Self {
            outcome,
            states: None,
            attempts: Vec::new(),
            completed_vm_usage: empty_usage(),
            tree_usage: MacroTreeUsage::default(),
        }
    }
}

fn empty_usage() -> ExecutionUsage {
    ExecutionUsage {
        steps: 0,
        system_polls: 0,
        peak_stack_depth: 0,
    }
}

fn binding_error(error: MacroRegistrationError) -> SourceCheckError {
    SourceCheckError::ImportedMacro {
        file: 0,
        command: 0,
        offset: 0,
        error: Box::new(SourceMacroError::Binding(Box::new(error))),
    }
}

fn parser_binding_error(error: ParserRegistrationError) -> SourceCheckError {
    SourceCheckError::ImportedMacro {
        file: 0,
        command: 0,
        offset: 0,
        error: Box::new(SourceMacroError::ParserBinding(Box::new(error))),
    }
}

fn parser_resource(error: &SourceCheckError) -> Option<Inconclusive> {
    match error {
        SourceCheckError::ImportedMacro { error, .. } => match error.as_ref() {
            SourceMacroError::ParserBinding(error) if error.is_resource() => {
                Some(Inconclusive::dependency_unavailable(format!(
                    "source-module parser preparation: {error}"
                )))
            }
            _ => None,
        },
        SourceCheckError::Command { error, .. } => match error.as_ref() {
            EngineExecutionError::ImportedMacro {
                message,
                disposition: ("resource", false, 3),
            } if message.starts_with("imported parser installation: ") => {
                Some(Inconclusive::dependency_unavailable(message.clone()))
            }
            _ => None,
        },
        _ => None,
    }
}

fn module_parser_resource(error: &SourceModuleCheckError) -> Option<Inconclusive> {
    match error {
        SourceModuleCheckError::Source { error, .. } => parser_resource(error),
        _ => None,
    }
}

// The module importer and VM expose independent read-only probe traits. Keep
// both existing APIs intact and forward every poll to the caller's same probe.
struct ModuleCancellation<'a>(&'a dyn CancellationProbe);
impl ModuleCancellationProbe for ModuleCancellation<'_> {
    fn is_cancelled(&self) -> bool {
        self.0.is_cancelled()
    }
}

struct MacroCancellation<'a>(&'a dyn ModuleCancellationProbe);
impl CancellationProbe for MacroCancellation<'_> {
    fn is_cancelled(&self) -> bool {
        self.0.is_cancelled()
    }
}

pub(super) struct ModuleMacroSession {
    registry: RegisteredMacros,
    parsers: RegisteredParsers,
    context: MacroContext,
    state: MacroState,
    limits: MacroTreeLimits,
    states: BTreeMap<Name, MacroState>,
    attempts: Vec<MacroAttempt>,
    completed_vm_usage: ExecutionUsage,
    tree_usage: MacroTreeUsage,
}

impl ModuleMacroSession {
    fn new(
        registry: RegisteredMacros,
        parsers: RegisteredParsers,
        context: MacroContext,
        state: MacroState,
        limits: MacroTreeLimits,
    ) -> Self {
        Self {
            registry,
            parsers,
            context,
            state,
            limits,
            states: BTreeMap::new(),
            attempts: Vec::new(),
            completed_vm_usage: empty_usage(),
            tree_usage: MacroTreeUsage::default(),
        }
    }

    fn remaining_limits(&self) -> MacroTreeLimits {
        let mut remaining = self.limits;
        remaining.dispatch.max_attempts = remaining
            .dispatch
            .max_attempts
            .saturating_sub(self.attempts.len() as u64);
        remaining.dispatch.execution.vm.max_steps = remaining
            .dispatch
            .execution
            .vm
            .max_steps
            .saturating_sub(self.completed_vm_usage.steps);
        remaining.max_visits = remaining.max_visits.saturating_sub(self.tree_usage.visits);
        remaining.generation.max_nodes = remaining
            .generation
            .max_nodes
            .saturating_sub(self.tree_usage.generated_nodes);
        remaining.generation.max_bytes = remaining
            .generation
            .max_bytes
            .saturating_sub(self.tree_usage.generated_bytes);
        remaining
    }

    /// Preflight uses the immutable artifact context to verify the selected
    /// bindings without replaying or executing source predecessors. Only this
    /// module's external import order enters its grammar. Actual execution
    /// rechecks the same bindings against the module's projected engine.
    pub(super) fn install_parsers_for_preflight(
        &self,
        ordered_imports: &[Name],
        artifacts: &Engine,
        grammar: &mut grammar::SourceGrammar,
    ) -> Result<(), SourceCheckError> {
        let parsers = self
            .parsers
            .project_imports(ordered_imports, artifacts)
            .map_err(parser_binding_error)?;
        grammar
            .import_artifact(&parsers)
            .map_err(|error| SourceCheckError::Command {
                file: 0,
                command: 0,
                offset: 0,
                error: Box::new(error),
            })
    }

    /// The driver supplies the authoritative mixed import order after replay,
    /// and retains ordinary declaration recording and module source positions.
    /// Binding is checked even for an empty forwarding module.
    pub(super) fn check_module<T>(
        &mut self,
        module: &Name,
        ordered_imports: &[Name],
        engine: &Engine,
        cancellation: Option<&dyn ModuleCancellationProbe>,
        check: impl FnOnce(&mut FileSession<'_>) -> Result<Outcome<T>, SourceCheckError>,
    ) -> Result<Outcome<T>, SourceCheckError> {
        if cancellation.is_some_and(ModuleCancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-module macros/before-module",
            )));
        }
        let registry = self
            .registry
            .project_imports(ordered_imports)
            .map_err(binding_error)?;
        registry
            .validate_source_engine(engine)
            .map_err(binding_error)?;
        let parsers = match self.parsers.project_imports(ordered_imports, engine) {
            Ok(parsers) => parsers,
            Err(error) => {
                let error = parser_binding_error(error);
                return match parser_resource(&error) {
                    Some(reason) => Ok(Outcome::Inconclusive(reason)),
                    None => Err(error),
                };
            }
        };
        let mut context = self.context.clone();
        context.quotation_context = module.clone();
        let cancellation = cancellation.map(MacroCancellation);
        let mut session = FileSession::new(SourceMacroInvocation {
            registry: &registry,
            context: &context,
            state: self.state.clone(),
            lookup: None,
            limits: self.remaining_limits(),
            cancellation: cancellation
                .as_ref()
                .map(|probe| probe as &dyn CancellationProbe),
        });
        session.set_parsers(parsers);
        let result = check(&mut session);
        let (finished, report) = session.finish();
        let successful = matches!(&result, Ok(Outcome::Complete(_)))
            && matches!(&finished, Outcome::Complete(()));
        if let Err(reason) = self.record(module, report, successful) {
            return Ok(Outcome::Inconclusive(reason));
        }
        match finished {
            Outcome::Complete(()) => {}
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        }
        result
    }

    fn record(
        &mut self,
        module: &Name,
        mut report: FileSessionReport,
        successful: bool,
    ) -> Result<(), Inconclusive> {
        let overflow =
            || Inconclusive::dependency_unavailable("imported macro module graph usage overflow");
        let usage = ExecutionUsage {
            steps: self
                .completed_vm_usage
                .steps
                .checked_add(report.completed_vm_usage.steps)
                .ok_or_else(overflow)?,
            system_polls: self
                .completed_vm_usage
                .system_polls
                .checked_add(report.completed_vm_usage.system_polls)
                .ok_or_else(overflow)?,
            peak_stack_depth: self
                .completed_vm_usage
                .peak_stack_depth
                .max(report.completed_vm_usage.peak_stack_depth),
        };
        let tree_usage = MacroTreeUsage {
            visits: self
                .tree_usage
                .visits
                .checked_add(report.tree_usage.visits)
                .ok_or_else(overflow)?,
            generated_nodes: self
                .tree_usage
                .generated_nodes
                .checked_add(report.tree_usage.generated_nodes)
                .ok_or_else(overflow)?,
            generated_bytes: self
                .tree_usage
                .generated_bytes
                .checked_add(report.tree_usage.generated_bytes)
                .ok_or_else(overflow)?,
        };
        self.attempts
            .try_reserve(report.attempts.len())
            .map_err(|_| {
                Inconclusive::dependency_unavailable(
                    "imported macro module graph attempt allocation",
                )
            })?;
        self.completed_vm_usage = usage;
        self.tree_usage = tree_usage;
        self.attempts.append(&mut report.attempts);
        if successful {
            self.states.insert(module.clone(), report.state);
        }
        Ok(())
    }

    fn finish_execution<E>(
        self,
        outcome: Outcome<Result<SourceProgramExecution, SourceProgramExecutionError<E>>>,
    ) -> SourceMacroProgramExecution<E> {
        let successful = match &outcome {
            Outcome::Complete(Ok(program)) => program.modules.iter().all(|module| {
                module.commands.batch.executions.iter().all(|execution| {
                    matches!(execution.exit, fln_vm::interpreter::VmExit::Returned(_))
                })
            }),
            _ => false,
        };
        let states = successful.then_some(self.states);
        SourceMacroProgramExecution {
            outcome,
            states,
            attempts: self.attempts,
            completed_vm_usage: self.completed_vm_usage,
            tree_usage: self.tree_usage,
        }
    }

    fn finish(
        self,
        outcome: Outcome<Result<SourceModuleCheck, SourceModuleCheckError>>,
    ) -> SourceMacroModuleCheck {
        let states = matches!(&outcome, Outcome::Complete(Ok(_))).then_some(self.states);
        SourceMacroModuleCheck {
            outcome,
            states,
            attempts: self.attempts,
            completed_vm_usage: self.completed_vm_usage,
            tree_usage: self.tree_usage,
        }
    }
}

impl imported::SourceOleanImport {
    fn module_parsers(
        &self,
        limits: MacroRegistryLimits,
    ) -> Result<RegisteredParsers, SourceCheckError> {
        self.prepare_selected_imported_parsers(ParserRegistryLimits {
            max_modules: limits.max_modules,
            max_declarations: limits.max_declarations,
            metadata: limits.metadata,
            ..ParserRegistryLimits::default()
        })
        .map_err(parser_binding_error)
    }

    /// Execute an explicit source graph with the receipt's imported node macros.
    /// Expansion precedes ordinary elaboration, admission, compilation and VM
    /// execution. Every module retains its exact import order and fresh macro
    /// state; the graph shares one expansion allowance.
    ///
    /// This explicit adapter accepts the same registered-macro subset as
    /// `check_source_modules_with_imported_macros`. Owned sessions execute
    /// imported tactics at native tactic dispatch. Source templates, atomic
    /// macros outside tactics, and borrowed cancellation overrides at the
    /// tactic boundary remain explicit capability refusals.
    #[allow(clippy::too_many_arguments)]
    pub fn execute_source_modules_with_imported_macros(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceProgramLimits,
        input: SourceModuleMacroInputs<'_>,
        cancellation: Option<&dyn CancellationProbe>,
        presentation: crate::EvaluationPresentation,
    ) -> SourceMacroProgramExecution {
        self.execute_program_with_macro_preparation(
            modules,
            entry,
            options,
            limits,
            || {
                let parsers = self.module_parsers(input.registry_limits)?;
                let registry = self
                    .prepare_imported_macros(
                        input.code,
                        input.partition,
                        input.user_declarations,
                        input.registry_limits,
                    )
                    .map_err(binding_error)?;
                Ok(ModuleMacroSession::new(
                    registry,
                    parsers,
                    input.context,
                    input.state,
                    input.limits,
                ))
            },
            cancellation,
            false,
            presentation,
            &mut |_, _| Ok::<(), std::convert::Infallible>(()),
        )
    }

    /// Execute ordinary Lean source with implicit Init edges and imported
    /// macros. Validate each completed module before exporting it or running
    /// a successor, exactly as the ordinary source-program entry point does.
    #[allow(clippy::too_many_arguments)]
    pub fn execute_lean_source_modules_with_imported_macros_and_validation<E>(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceProgramLimits,
        input: SourceModuleMacroInputs<'_>,
        cancellation: Option<&dyn CancellationProbe>,
        presentation: crate::EvaluationPresentation,
        validate: &mut impl FnMut(&Name, &crate::SourceCommandBatchExecution) -> Result<(), E>,
    ) -> SourceMacroProgramExecution<E> {
        self.execute_program_with_macro_preparation(
            modules,
            entry,
            options,
            limits,
            || {
                let parsers = self.module_parsers(input.registry_limits)?;
                let registry = self
                    .prepare_imported_macros(
                        input.code,
                        input.partition,
                        input.user_declarations,
                        input.registry_limits,
                    )
                    .map_err(binding_error)?;
                Ok(ModuleMacroSession::new(
                    registry,
                    parsers,
                    input.context,
                    input.state,
                    input.limits,
                ))
            },
            cancellation,
            true,
            presentation,
            validate,
        )
    }

    /// Execute the same source graph while compiling registered macros on
    /// demand. Every captured owner and registration is validated up front;
    /// reaching an unsupported macro stops the program without a partial result.
    #[allow(clippy::too_many_arguments)]
    pub fn execute_source_modules_with_deferred_imported_macros(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceProgramLimits,
        input: SourceModuleDeferredMacroInputs,
        cancellation: Option<&dyn CancellationProbe>,
        presentation: crate::EvaluationPresentation,
    ) -> SourceMacroProgramExecution {
        self.execute_program_with_macro_preparation(
            modules,
            entry,
            options,
            limits,
            || {
                let parsers = self.module_parsers(input.registry_limits)?;
                let registry = self
                    .prepare_imported_macros_deferred(input.compilation, input.registry_limits)
                    .map_err(binding_error)?;
                Ok(ModuleMacroSession::new(
                    registry,
                    parsers,
                    input.context,
                    input.state,
                    input.limits,
                ))
            },
            cancellation,
            false,
            presentation,
            &mut |_, _| Ok::<(), std::convert::Infallible>(()),
        )
    }

    /// Execute ordinary Lean source with demand-driven imported macros and
    /// implicit Init edges. Each completed module must pass caller validation
    /// before it is exported or any successor runs.
    #[allow(clippy::too_many_arguments)]
    pub fn execute_lean_source_modules_with_deferred_imported_macros_and_validation<E>(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceProgramLimits,
        input: SourceModuleDeferredMacroInputs,
        cancellation: Option<&dyn CancellationProbe>,
        presentation: crate::EvaluationPresentation,
        validate: &mut impl FnMut(&Name, &crate::SourceCommandBatchExecution) -> Result<(), E>,
    ) -> SourceMacroProgramExecution<E> {
        self.execute_program_with_macro_preparation(
            modules,
            entry,
            options,
            limits,
            || {
                let parsers = self.module_parsers(input.registry_limits)?;
                let registry = self
                    .prepare_imported_macros_deferred(input.compilation, input.registry_limits)
                    .map_err(binding_error)?;
                Ok(ModuleMacroSession::new(
                    registry,
                    parsers,
                    input.context,
                    input.state,
                    input.limits,
                ))
            },
            cancellation,
            true,
            presentation,
            validate,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn execute_program_with_macro_preparation<E>(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceProgramLimits,
        prepare: impl FnOnce() -> Result<ModuleMacroSession, SourceCheckError>,
        cancellation: Option<&dyn CancellationProbe>,
        implicit_init: bool,
        presentation: crate::EvaluationPresentation,
        validate: &mut impl FnMut(&Name, &crate::SourceCommandBatchExecution) -> Result<(), E>,
    ) -> SourceMacroProgramExecution<E> {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return SourceMacroProgramExecution::stopped(Outcome::Inconclusive(
                Inconclusive::cancelled("source-program macros/before-preparation"),
            ));
        }
        if self.contexts.has_inherited_imports() {
            return SourceMacroProgramExecution::stopped(Outcome::Complete(Err(
                SourceModuleCheckError::ImportContext {
                    module: entry.clone(),
                    reason: "imported macro execution requires retained journals for the complete artifact closure",
                }
                .into(),
            )));
        }
        let mut session = match prepare() {
            Ok(session) => session,
            Err(error) => {
                if let Some(reason) = parser_resource(&error) {
                    return SourceMacroProgramExecution::stopped(Outcome::Inconclusive(reason));
                }
                return SourceMacroProgramExecution::stopped(Outcome::Complete(Err(
                    SourceModuleCheckError::Source {
                        module: entry.clone(),
                        error,
                    }
                    .into(),
                )));
            }
        };
        let cancellation = cancellation.map(ModuleCancellation);
        let outcome = match self.execute_source_modules_with_implicit_init(
            modules,
            entry,
            options,
            limits,
            cancellation
                .as_ref()
                .map(|probe| probe as &dyn ModuleCancellationProbe),
            implicit_init,
            presentation,
            validate,
            Some(&mut session),
        ) {
            Ok(outcome) => outcome.map_complete(Ok),
            Err(error) => {
                let reason = match &error {
                    SourceProgramExecutionError::Source(error) => module_parser_resource(error),
                    SourceProgramExecutionError::Validation { .. } => None,
                };
                match reason {
                    Some(reason) => Outcome::Inconclusive(reason),
                    None => Outcome::Complete(Err(error)),
                }
            }
        };
        session.finish_execution(outcome)
    }

    /// Check source modules with all imported node macros from this receipt.
    /// Each module sees only its declared import closure, in its own import
    /// order. Expansion enters the ordinary module driver and dual-check
    /// admission, preserving original source locations and declaration replay.
    ///
    /// Macro state resets per module; expansion allowances cover the whole
    /// graph. Parser journals explicitly enabled with `enable_imported_syntax`
    /// supply custom syntax before parsing. Every selected journal remains
    /// complete. Closed descriptions use cumulative preparation
    /// ceilings from `ParserRegistryLimits::default`, with module, declaration
    /// and metadata ceilings taken from `registry_limits`. Executable parser
    /// closures and unsupported grammar forms refuse the whole transaction.
    /// Module-system sources retain separate public-signature and
    /// private-implementation checks, selected from the expanded modifiers.
    /// Source-declared templates and receipts built on previously imported
    /// artifacts are typed refusals.
    /// Reusable source caches and persisted artifacts are not consulted.
    pub fn check_source_modules_with_imported_macros(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        input: SourceModuleMacroInputs<'_>,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> SourceMacroModuleCheck {
        self.check_source_modules_with_macro_preparation(
            modules,
            entry,
            options,
            limits,
            || {
                let parsers = self.module_parsers(input.registry_limits)?;
                let registry = self
                    .prepare_imported_macros(
                        input.code,
                        input.partition,
                        input.user_declarations,
                        input.registry_limits,
                    )
                    .map_err(binding_error)?;
                Ok(ModuleMacroSession::new(
                    registry,
                    parsers,
                    input.context,
                    input.state,
                    input.limits,
                ))
            },
            cancellation,
        )
    }

    /// Check the same complete import world while compiling each macro only
    /// when dispatch reaches it. Unused and inactive candidates need valid
    /// checked owners but need not have executable closures in this native
    /// Mirror slice. An invoked unsupported closure stops the check; it never
    /// disappears from the table or falls back to an older candidate.
    pub fn check_source_modules_with_deferred_imported_macros(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        input: SourceModuleDeferredMacroInputs,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> SourceMacroModuleCheck {
        self.check_source_modules_with_macro_preparation(
            modules,
            entry,
            options,
            limits,
            || {
                let parsers = self.module_parsers(input.registry_limits)?;
                let registry = self
                    .prepare_imported_macros_deferred(input.compilation, input.registry_limits)
                    .map_err(binding_error)?;
                Ok(ModuleMacroSession::new(
                    registry,
                    parsers,
                    input.context,
                    input.state,
                    input.limits,
                ))
            },
            cancellation,
        )
    }

    fn check_source_modules_with_macro_preparation(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        prepare: impl FnOnce() -> Result<ModuleMacroSession, SourceCheckError>,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> SourceMacroModuleCheck {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return SourceMacroModuleCheck::stopped(Outcome::Inconclusive(
                Inconclusive::cancelled("source-module macros/before-preparation"),
            ));
        }
        if self.contexts.has_inherited_imports() {
            return SourceMacroModuleCheck::stopped(Outcome::Complete(Err(
                SourceModuleCheckError::ImportContext {
                    module: entry.clone(),
                    reason: "imported macro checking requires retained journals for the complete artifact closure",
                },
            )));
        }
        let mut session = match prepare() {
            Ok(session) => session,
            Err(error) => {
                if let Some(reason) = parser_resource(&error) {
                    return SourceMacroModuleCheck::stopped(Outcome::Inconclusive(reason));
                }
                return SourceMacroModuleCheck::stopped(Outcome::Complete(Err(
                    SourceModuleCheckError::Source {
                        module: entry.clone(),
                        error,
                    },
                )));
            }
        };
        let cancellation = cancellation.map(ModuleCancellation);
        let outcome = match cache::run_collecting(
            &self.contexts.complete,
            modules,
            entry,
            options,
            limits,
            cancellation
                .as_ref()
                .map(|probe| probe as &dyn ModuleCancellationProbe),
            cache::RunOptions {
                cache: None,
                collect_artifacts: false,
                contexts: Some(&self.contexts),
                records: None,
                macros: Some(&mut session),
            },
        ) {
            Ok(outcome) => outcome.map_complete(|run| Ok(run.result.checked)),
            Err(error) => match module_parser_resource(&error) {
                Some(reason) => Outcome::Inconclusive(reason),
                None => Outcome::Complete(Err(error)),
            },
        };
        session.finish(outcome)
    }
}
