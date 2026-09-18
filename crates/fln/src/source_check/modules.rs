//! Source libraries checked module-by-module, without compiling or executing code.
//!
//! Each module elaborates exactly once against its own transitive imports. Imports
//! replay the already elaborated declaration terms through both checking engines;
//! source is never re-elaborated in a larger sibling environment. Only native,
//! append-ordered extension suffixes are exported. Diamonds replay shared modules
//! once in first-discovery order, including their instance and simp journals.
use super::*;
use crate::SourceModuleInput;
use std::collections::BTreeMap;

mod graph;
mod replay;
pub use fln_parse::command_scope::imports::{SourceHeader, parse_source_header};

#[derive(Debug, Clone, Copy)]
pub struct SourceModuleCheckLimits {
    pub source: SourceCheckLimits,
    pub max_modules: usize,
    pub max_imports: usize,
    pub max_name_depth: usize,
    /// Graph visits, captured declarations/journal entries and replay operations.
    pub max_work: usize,
    /// Aggregate bytes examined or copied while exporting/replaying metadata.
    pub max_extension_bytes: usize,
}
impl SourceModuleCheckLimits {
    pub fn new(source: SourceCheckLimits) -> Self {
        Self {
            source,
            max_modules: 256,
            max_imports: 4096,
            max_name_depth: 128,
            max_work: 1_000_000,
            max_extension_bytes: 64 * 1024 * 1024,
        }
    }
}

#[derive(Debug)]
pub struct SourceModuleCheck {
    /// Aggregate counts and the entry module's complete checked import environment.
    pub checked: SourceFileCheck,
    pub module_order: Vec<Name>,
    pub replayed_declarations: usize,
}

#[derive(Debug)]
pub enum SourceModuleCheckError {
    EmptyInput,
    InvalidName(Name),
    DuplicateModule(Name),
    MissingModule { importer: Name, module: Name },
    Cycle(Name),
    UnreachableModule(Name),
    Limit { resource: &'static str, limit: usize },
    Header { module: Name, error: DefinitionParseError },
    Source { module: Name, error: SourceCheckError },
    Replay { module: Name, error: Box<EngineExecutionError> },
    Extension { module: Name, extension: Name, reason: &'static str },
}
impl std::fmt::Display for SourceModuleCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyInput => write!(f, "source module checking requires an entry module"),
            Self::InvalidName(name) => write!(f, "invalid source module name `{}`", name.to_display_string()),
            Self::DuplicateModule(name) => write!(f, "duplicate source module `{}`", name.to_display_string()),
            Self::MissingModule { importer, module } => write!(f, "module `{}` requires missing module `{}`", importer.to_display_string(), module.to_display_string()),
            Self::Cycle(name) => write!(f, "source import cycle through `{}`", name.to_display_string()),
            Self::UnreachableModule(name) => write!(f, "source module `{}` is outside the entry import closure", name.to_display_string()),
            Self::Limit { resource, limit } => write!(f, "source module check exceeds {resource} limit {limit}"),
            Self::Header { module, error } => write!(f, "module `{}` header: {error}", module.to_display_string()),
            Self::Source { module, error } => write!(f, "module `{}`: {error}", module.to_display_string()),
            Self::Replay { module, error } => write!(f, "importing checked module `{}`: {error}", module.to_display_string()),
            Self::Extension { module, extension, reason } => write!(f, "module `{}` extension `{}`: {reason}", module.to_display_string(), extension.to_display_string()),
        }
    }
}
impl std::error::Error for SourceModuleCheckError {}
impl SourceModuleCheckError {
    pub fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::Source { error, .. } => error.disposition(),
            Self::Replay { error, .. } => super::classify(error),
            Self::Limit { .. } => ("resource", false, 3),
            Self::Extension { .. } => ("inconclusive", false, 3),
            _ => ("input", false, 1),
        }
    }
}

struct Meter {
    work: usize,
    bytes: usize,
    limits: SourceModuleCheckLimits,
}
impl Meter {
    fn work(&mut self, amount: usize) -> Result<(), SourceModuleCheckError> {
        self.work = self.work.checked_add(amount).filter(|n| *n <= self.limits.max_work)
            .ok_or(SourceModuleCheckError::Limit { resource: "module work", limit: self.limits.max_work })?;
        Ok(())
    }
    fn bytes(&mut self, amount: usize) -> Result<(), SourceModuleCheckError> {
        self.bytes = self.bytes.checked_add(amount).filter(|n| *n <= self.limits.max_extension_bytes)
            .ok_or(SourceModuleCheckError::Limit { resource: "extension bytes", limit: self.limits.max_extension_bytes })?;
        Ok(())
    }
}

impl Engine {
    /// Check one closed source-library graph and return only its fully checked entry.
    /// The supplied engine is the explicit initial environment (typically the native
    /// source seed); no implicit Reference Init module, filesystem access, or runtime
    /// execution is hidden here. Every provided module must belong to the closure.
    pub fn check_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
    ) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
        self.check_source_modules_with_cancel(modules, entry, options, limits, None)
    }

    /// Cancellation is sampled at module and import-replay boundaries. Individual
    /// declaration checks retain their existing bounded, synchronous contract.
    pub fn check_source_modules_with_cancel(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled("source-modules/before-plan")));
        }
        let mut meter = Meter { work: 0, bytes: 0, limits };
        let plan = graph::Plan::new(modules, entry, &mut meter)?;
        let base_logical_root = self.logical_root(options);
        let mut exports = BTreeMap::new();
        let mut commands = 0usize;
        let mut theorems = 0usize;
        let mut replayed_declarations = 0usize;
        let mut entry_result = None;
        for &index in &plan.order {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled("source-modules/before-module")));
            }
            let dependencies = plan.dependencies_of(index, modules, &mut meter)?;
            let mut imported = self.clone();
            for dependency in dependencies {
                if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled("source-modules/before-import")));
                }
                let export: &replay::Export = exports.get(&dependency).expect("postorder predecessor");
                imported = match export.replay(imported, modules[dependency].name, options, &mut meter, cancellation)? {
                    Outcome::Complete(engine) => engine,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                replayed_declarations += export.declarations.len();
            }
            let mut declarations = Vec::new();
            let header = &plan.headers[index];
            let source = &modules[index].source[header.body_start.0..];
            let mut source_limits = limits.source;
            source_limits.max_commands = source_limits.max_commands.saturating_sub(commands);
            let result = if source.is_empty() {
                // An import-only module has no command to charge. In particular,
                // a dependency may consume the exact aggregate command budget.
                let root = imported.logical_root(options);
                Ok(Outcome::Complete(SourceFileCheck {
                    engine: imported.clone(), files: 1, commands: 0, theorems: 0,
                    base_logical_root: root, result_logical_root: root,
                }))
            } else {
                imported.check_source_files_recording(
                    &[source], options, source_limits, Some(&mut declarations),
                )
            }.map_err(|mut error| {
                // The declaration checker operates on the untouched body slice.
                // Public errors must still point into the original module bytes.
                match &mut error {
                    SourceCheckError::Scope { offset, .. } | SourceCheckError::Command { offset, .. } => {
                        *offset = offset.saturating_add(header.body_start.0);
                    }
                    _ => {}
                }
                SourceModuleCheckError::Source { module: modules[index].name.clone(), error }
            })?;
            let mut checked = match result {
                Outcome::Complete(checked) => checked,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            commands += checked.commands;
            theorems += checked.theorems;
            let export = replay::Export::capture(
                modules[index].name, imported.environment(), checked.engine.environment(),
                declarations, &mut meter,
            )?;
            exports.insert(index, export);
            if index == plan.entry {
                checked.files = plan.order.len();
                checked.commands = commands;
                checked.theorems = theorems;
                checked.base_logical_root = base_logical_root;
                entry_result = Some(checked);
            }
        }
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled("source-modules/before-publication")));
        }
        Ok(Outcome::Complete(SourceModuleCheck {
            checked: entry_result.expect("entry is last in its postorder"),
            module_order: plan.order.iter().map(|&index| modules[index].name.clone()).collect(),
            replayed_declarations,
        }))
    }
}
