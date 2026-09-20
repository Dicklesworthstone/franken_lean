//! Source libraries checked module-by-module, without compiling or executing code.
//!
//! Imports replay already elaborated declarations through both checking engines.
//! `SourceModuleSession` additionally retains exact, checked module snapshots and
//! invalidates their transitive consumers when source or import identities change.
use super::*;
use crate::SourceModuleInput;
use std::collections::BTreeMap;

mod cache;
mod graph;
mod replay;
pub use cache::{SourceModuleCacheLimits, SourceModuleSession, SourceModuleSessionCheck};
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
    pub checked: SourceFileCheck,
    pub module_order: Vec<Name>,
    /// Declarations actually replayed in this invocation, not cache-hit work.
    pub replayed_declarations: usize,
}

#[derive(Debug)]
pub enum SourceModuleCheckError {
    EmptyInput,
    InvalidName(Name),
    DuplicateModule(Name),
    MissingModule {
        importer: Name,
        module: Name,
    },
    Cycle(Name),
    UnreachableModule(Name),
    Limit {
        resource: &'static str,
        limit: usize,
    },
    Header {
        module: Name,
        error: DefinitionParseError,
    },
    Source {
        module: Name,
        error: SourceCheckError,
    },
    Replay {
        module: Name,
        error: Box<EngineExecutionError>,
    },
    Extension {
        module: Name,
        extension: Name,
        reason: &'static str,
    },
}
impl std::fmt::Display for SourceModuleCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyInput => write!(f, "source module checking requires an entry module"),
            Self::InvalidName(name) => write!(
                f,
                "invalid source module name `{}`",
                name.to_display_string()
            ),
            Self::DuplicateModule(name) => {
                write!(f, "duplicate source module `{}`", name.to_display_string())
            }
            Self::MissingModule { importer, module } => write!(
                f,
                "module `{}` requires missing module `{}`",
                importer.to_display_string(),
                module.to_display_string()
            ),
            Self::Cycle(name) => write!(
                f,
                "source import cycle through `{}`",
                name.to_display_string()
            ),
            Self::UnreachableModule(name) => write!(
                f,
                "source module `{}` is outside the entry import closure",
                name.to_display_string()
            ),
            Self::Limit { resource, limit } => {
                write!(f, "source module check exceeds {resource} limit {limit}")
            }
            Self::Header { module, error } => {
                write!(f, "module `{}` header: {error}", module.to_display_string())
            }
            Self::Source { module, error } => {
                write!(f, "module `{}`: {error}", module.to_display_string())
            }
            Self::Replay { module, error } => write!(
                f,
                "importing checked module `{}`: {error}",
                module.to_display_string()
            ),
            Self::Extension {
                module,
                extension,
                reason,
            } => write!(
                f,
                "module `{}` extension `{}`: {reason}",
                module.to_display_string(),
                extension.to_display_string()
            ),
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
        self.work = self
            .work
            .checked_add(amount)
            .filter(|n| *n <= self.limits.max_work)
            .ok_or(SourceModuleCheckError::Limit {
                resource: "module work",
                limit: self.limits.max_work,
            })?;
        Ok(())
    }
    fn bytes(&mut self, amount: usize) -> Result<(), SourceModuleCheckError> {
        self.bytes = self
            .bytes
            .checked_add(amount)
            .filter(|n| *n <= self.limits.max_extension_bytes)
            .ok_or(SourceModuleCheckError::Limit {
                resource: "extension bytes",
                limit: self.limits.max_extension_bytes,
            })?;
        Ok(())
    }
}

impl Engine {
    /// Check a closed source graph against this explicit initial environment.
    /// No Reference Init loader, filesystem access or runtime execution is hidden here.
    pub fn check_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
    ) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
        self.check_source_modules_with_cancel(modules, entry, options, limits, None)
    }

    /// Cancellation is sampled at module, replay and publication boundaries.
    pub fn check_source_modules_with_cancel(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
        cache::run(self, modules, entry, options, limits, cancellation, None)
            .map(|outcome| outcome.map_complete(|run| run.result.checked))
    }
}
