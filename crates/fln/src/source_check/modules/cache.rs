//! Process-local reuse of immutable, successfully checked module snapshots.
//! Identity is exact bytes plus private dependency stamps, never a digest match.
use super::*;
use std::sync::Arc;

/// Retention limits, independent of checking limits. These count source bytes and
/// module snapshots, not allocator RSS. Terms remain under native checker budgets.
#[derive(Debug, Clone, Copy)]
pub struct SourceModuleCacheLimits {
    pub max_modules: usize,
    pub max_source_bytes: usize,
}
impl Default for SourceModuleCacheLimits {
    fn default() -> Self {
        Self {
            max_modules: 256,
            max_source_bytes: 4 * 1024 * 1024,
        }
    }
}

struct CachedModule {
    source: Arc<[u8]>,
    /// Stamps own no engine or dependencies, so eviction cannot retain old worlds
    /// transitively or recursively drop a dependency-shaped chain of snapshots.
    stamp: Arc<()>,
    dependencies: Vec<(Name, Arc<()>)>,
    engine: Engine,
    export: Arc<replay::Export>,
    commands: usize,
    theorems: usize,
    base_root: LogicalRoot,
    result_root: LogicalRoot,
    work: usize,
    bytes: usize,
}
impl CachedModule {
    fn matches(&self, source: &[u8], dependencies: &[(Name, Arc<()>)]) -> bool {
        self.source.as_ref() == source
            && self.dependencies.len() == dependencies.len()
            && self
                .dependencies
                .iter()
                .zip(dependencies)
                .all(|((old_name, old), (name, new))| old_name == name && Arc::ptr_eq(old, new))
    }
    fn checked(&self) -> SourceFileCheck {
        SourceFileCheck {
            engine: self.engine.clone(),
            files: 1,
            commands: self.commands,
            theorems: self.theorems,
            base_logical_root: self.base_root,
            result_logical_root: self.result_root,
        }
    }
}

/// A reusable source-library checker bound to one immutable initial engine,
/// options map and checking budget. Create a new session to change any of them.
/// No API installs unverified cache entries or loads persisted cache bytes.
/// Only a completely successful graph replaces the retained closure. Failures
/// and cancellation leave the prior cache intact, but it is never returned as
/// an answer for different source bytes or dependency identities.
pub struct SourceModuleSession {
    base: Engine,
    options: KVMap,
    limits: SourceModuleCheckLimits,
    retention: SourceModuleCacheLimits,
    entries: BTreeMap<Name, Arc<CachedModule>>,
    source_bytes: usize,
}

#[derive(Debug)]
pub struct SourceModuleSessionCheck {
    pub checked: SourceModuleCheck,
    pub reused_modules: usize,
    pub elaborated_modules: usize,
}
impl SourceModuleSession {
    pub fn new(
        base: Engine,
        options: KVMap,
        limits: SourceModuleCheckLimits,
        retention: SourceModuleCacheLimits,
    ) -> Self {
        Self {
            base,
            options,
            limits,
            retention,
            entries: BTreeMap::new(),
            source_bytes: 0,
        }
    }
    /// Observe an unfinished declaration against the exact checked import and
    /// command prefix. The declaration at the cursor is never admitted.
    pub fn inspect(
        &mut self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        offset: usize,
        kind: super::super::inspect::ObservationKind,
    ) -> Result<Outcome<super::super::inspect::SourceInspection>, SourceModuleCheckError> {
        super::super::inspect::module(self, modules, entry, offset, kind, self.limits)
    }

    pub fn retained_modules(&self) -> usize {
        self.entries.len()
    }
    pub fn retained_source_bytes(&self) -> usize {
        self.source_bytes
    }
    pub fn clear(&mut self) {
        self.entries.clear();
        self.source_bytes = 0;
    }
    pub fn check(
        &mut self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
    ) -> Result<Outcome<SourceModuleSessionCheck>, SourceModuleCheckError> {
        self.check_with_cancel(modules, entry, None)
    }
    pub fn check_with_cancel(
        &mut self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceModuleSessionCheck>, SourceModuleCheckError> {
        let view = CacheView {
            entries: &self.entries,
            limits: self.retention,
        };
        let outcome = run(
            &self.base,
            modules,
            entry,
            &self.options,
            self.limits,
            cancellation,
            Some(view),
        )?;
        Ok(match outcome {
            Outcome::Complete(run) => {
                self.entries = run.entries;
                self.source_bytes = run.source_bytes;
                Outcome::Complete(run.result)
            }
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        })
    }
}

pub(super) struct CacheView<'a> {
    entries: &'a BTreeMap<Name, Arc<CachedModule>>,
    limits: SourceModuleCacheLimits,
}
pub(super) struct Run {
    pub(super) result: SourceModuleSessionCheck,
    entries: BTreeMap<Name, Arc<CachedModule>>,
    source_bytes: usize,
}

/// Single execution path for stateless checks and reusable sessions. Cache hits
/// reserve the original work/extension charges so warming cannot bypass bounds.
pub(super) fn run(
    base: &Engine,
    modules: &[SourceModuleInput<'_>],
    entry: &Name,
    options: &KVMap,
    limits: SourceModuleCheckLimits,
    cancellation: Option<&dyn CancellationProbe>,
    cache: Option<CacheView<'_>>,
) -> Result<Outcome<Run>, SourceModuleCheckError> {
    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
        return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
            "source-modules/before-plan",
        )));
    }
    let mut meter = Meter {
        work: 0,
        bytes: 0,
        limits,
    };
    let plan = graph::Plan::new(modules, entry, base.imported_modules(), &mut meter)?;
    let base_logical_root = base.logical_root(options);
    let mut exports: BTreeMap<usize, Arc<replay::Export>> = BTreeMap::new();
    let mut stamps: BTreeMap<usize, Arc<()>> = BTreeMap::new();
    let mut pending = BTreeMap::new();
    let mut retained_bytes = 0usize;
    let mut commands = 0usize;
    let mut theorems = 0usize;
    let mut replayed_declarations = 0usize;
    let mut reused_modules = 0usize;
    let mut elaborated_modules = 0usize;
    let mut entry_result = None;
    for &index in &plan.order {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-modules/before-module",
            )));
        }
        let dependencies = plan.dependencies_of(index, modules, &mut meter)?;
        let identities: Vec<_> = if cache.is_some() {
            dependencies
                .iter()
                .map(|dependency| {
                    (
                        modules[*dependency].name.clone(),
                        Arc::clone(stamps.get(dependency).expect("predecessor stamp")),
                    )
                })
                .collect()
        } else {
            Vec::new()
        };
        let module = modules[index];
        let hit = cache
            .as_ref()
            .and_then(|view| view.entries.get(module.name))
            .filter(|cached| cached.matches(module.source, &identities));
        let keep = cache.as_ref().is_some_and(|view| {
            pending.len() < view.limits.max_modules
                && retained_bytes
                    .checked_add(module.source.len())
                    .is_some_and(|n| n <= view.limits.max_source_bytes)
        });
        let mut checked = if let Some(cached) = hit {
            meter.work(cached.work)?;
            meter.bytes(cached.bytes)?;
            exports.insert(index, Arc::clone(&cached.export));
            stamps.insert(index, Arc::clone(&cached.stamp));
            if keep {
                pending.insert(module.name.clone(), Arc::clone(cached));
                retained_bytes += module.source.len();
            }
            reused_modules += 1;
            cached.checked()
        } else {
            let before_work = meter.work;
            let before_bytes = meter.bytes;
            let mut imported = base.clone();
            for dependency in dependencies {
                if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                        "source-modules/before-import",
                    )));
                }
                let export = exports.get(&dependency).expect("postorder predecessor");
                imported = match export.replay(
                    imported,
                    modules[dependency].name,
                    options,
                    &mut meter,
                    cancellation,
                )? {
                    Outcome::Complete(engine) => engine,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                replayed_declarations += export.declarations.len();
            }
            let mut declarations = Vec::new();
            let header = &plan.headers[index];
            let source = &module.source[header.body_start.0..];
            let mut source_limits = limits.source;
            source_limits.max_commands = source_limits.max_commands.saturating_sub(commands);
            let result = if source.is_empty() {
                let root = imported.logical_root(options);
                Ok(Outcome::Complete(SourceFileCheck {
                    engine: imported.clone(),
                    files: 1,
                    commands: 0,
                    theorems: 0,
                    base_logical_root: root,
                    result_logical_root: root,
                }))
            } else {
                imported.check_source_files_recording(
                    &[source],
                    options,
                    source_limits,
                    Some(&mut declarations),
                )
            }
            .map_err(|mut error| {
                match &mut error {
                    SourceCheckError::Scope { offset, .. }
                    | SourceCheckError::Command { offset, .. } => {
                        *offset = offset.saturating_add(header.body_start.0);
                    }
                    _ => {}
                }
                SourceModuleCheckError::Source {
                    module: module.name.clone(),
                    error,
                }
            })?;
            let checked = match result {
                Outcome::Complete(checked) => checked,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            let export = Arc::new(replay::Export::capture(
                module.name,
                imported.environment(),
                checked.engine.environment(),
                declarations,
                &mut meter,
            )?);
            if cache.is_some() {
                let stamp = Arc::new(());
                stamps.insert(index, Arc::clone(&stamp));
                if keep {
                    pending.insert(
                        module.name.clone(),
                        Arc::new(CachedModule {
                            source: Arc::from(module.source),
                            stamp,
                            dependencies: identities,
                            engine: checked.engine.clone(),
                            export: Arc::clone(&export),
                            commands: checked.commands,
                            theorems: checked.theorems,
                            base_root: checked.base_logical_root,
                            result_root: checked.result_logical_root,
                            work: meter.work - before_work,
                            bytes: meter.bytes - before_bytes,
                        }),
                    );
                    retained_bytes += module.source.len();
                }
            }
            exports.insert(index, export);
            elaborated_modules += 1;
            checked
        };
        // Semantic source limits apply to reused modules too, including when a
        // changed sibling consumes more of the same aggregate command budget.
        commands = commands
            .checked_add(checked.commands)
            .filter(|n| *n <= limits.source.max_commands)
            .ok_or(SourceModuleCheckError::Limit {
                resource: "commands",
                limit: limits.source.max_commands,
            })?;
        theorems += checked.theorems;
        if index == plan.entry {
            checked.files = plan.order.len();
            checked.commands = commands;
            checked.theorems = theorems;
            checked.base_logical_root = base_logical_root;
            entry_result = Some(checked);
        }
    }
    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
        return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
            "source-modules/before-publication",
        )));
    }
    Ok(Outcome::Complete(Run {
        result: SourceModuleSessionCheck {
            checked: SourceModuleCheck {
                checked: entry_result.expect("entry is last in its postorder"),
                module_order: plan
                    .order
                    .iter()
                    .map(|&index| modules[index].name.clone())
                    .collect(),
                replayed_declarations,
            },
            reused_modules,
            elaborated_modules,
        },
        entries: pending,
        source_bytes: retained_bytes,
    }))
}
