//! Per-module external worlds assembled only from retained council-checked entries.
//! Native metadata is replayed in the same mixed source/artifact postorder as
//! declarations. A sibling's imports are never an ambient source environment.
use super::*;
use fln_env::environment::EnvironmentEntry;
use std::sync::Arc;

#[derive(Debug)]
struct ExternalModule {
    imports: Vec<Name>,
    entries: Vec<EnvironmentEntry>,
    unavailable: bool,
    before: Environment,
    after: Environment,
}

/// Private provenance, independent of the public, caller-editable import report.
#[derive(Debug)]
pub(super) struct ImportContexts {
    origin: Engine,
    pub(super) complete: Engine,
    modules: BTreeMap<Name, ExternalModule>,
}

pub(super) enum Step {
    Source(usize),
    External(Name),
}

fn unavailable(module: &Name, reason: &'static str) -> SourceModuleCheckError {
    SourceModuleCheckError::ImportContext {
        module: module.clone(),
        reason,
    }
}

impl ImportContexts {
    pub(super) fn capture(
        origin: &Engine,
        complete: &Engine,
        checked: &CheckedOleanSet,
        mut journals: BTreeMap<Name, (Environment, Environment)>,
    ) -> Self {
        let modules = checked
            .modules
            .iter()
            .map(|module| {
                let mut entries = Vec::new();
                let mut unavailable = false;
                for constant in &module.decoded.constants {
                    match checked.engine.environment.entry(constant.name()) {
                        Some(entry) if entry.declaration() == constant => entries.push(entry),
                        // A subsuming repeat can have a different proof. Never take
                        // an unrelated module's proof just because its name agrees.
                        _ => unavailable = true,
                    }
                }
                let (before, after) = journals
                    .remove(&module.name)
                    .expect("each replayed module has one metadata snapshot");
                (
                    module.name.clone(),
                    ExternalModule {
                        imports: module
                            .decoded
                            .module
                            .imports
                            .iter()
                            .map(|i| i.module.clone())
                            .collect(),
                        entries,
                        unavailable,
                        before,
                        after,
                    },
                )
            })
            .collect();
        Self {
            origin: origin.clone(),
            complete: complete.clone(),
            modules,
        }
    }

    /// One heap DFS handles both kinds of import, so a local registration
    /// between two external imports stays between them. Shared imports run once.
    pub(super) fn order(
        &self,
        index: usize,
        plan: &graph::Plan,
        modules: &[SourceModuleInput<'_>],
        meter: &mut Meter,
    ) -> Result<Vec<Step>, SourceModuleCheckError> {
        meter.work(modules.len())?;
        let local: BTreeMap<_, _> = modules
            .iter()
            .enumerate()
            .map(|(i, m)| (m.name, i))
            .collect();
        for module in modules {
            if self.modules.contains_key(module.name)
                || self.origin.imported_modules().contains(module.name)
            {
                return Err(SourceModuleCheckError::DuplicateModule(module.name.clone()));
            }
        }
        let mut seen = BTreeSet::new();
        let mut pending = vec![(modules[index].name.clone(), false)];
        let mut order = Vec::new();
        while let Some((name, finish)) = pending.pop() {
            meter.work(1)?;
            if finish {
                if let Some(&source) = local.get(&name) {
                    if source != index {
                        order.push(Step::Source(source));
                    }
                } else if self.modules.contains_key(&name) {
                    order.push(Step::External(name));
                }
                continue;
            }
            if !seen.insert(name.clone()) {
                continue;
            }
            let imports = if let Some(&source) = local.get(&name) {
                &plan.headers[source].imports
            } else if let Some(module) = self.modules.get(&name) {
                &module.imports
            } else if self.origin.imported_modules().contains(&name) {
                continue;
            } else {
                return Err(SourceModuleCheckError::MissingModule {
                    importer: modules[index].name.clone(),
                    module: name,
                });
            };
            meter.work(imports.len())?;
            pending.push((name, true));
            pending.extend(imports.iter().rev().cloned().map(|name| (name, false)));
        }
        Ok(order)
    }

    pub(super) fn project(
        &self,
        steps: &[Step],
        meter: &mut Meter,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<Engine>, SourceModuleCheckError> {
        let mut engine = self.origin.clone();
        let bound = engine.environment == Environment::new()
            || engine.imported_environment.as_ref() == Some(&engine.environment);
        let mut imported = (*engine.imported_modules).clone();
        let mut dependencies = (*engine.imported_module_dependencies).clone();
        for step in steps {
            let Step::External(name) = step else { continue };
            let module = &self.modules[name];
            if module.unavailable {
                return Err(unavailable(
                    name,
                    "an exact checked declaration snapshot for this import is unavailable",
                ));
            }
            for entry in &module.entries {
                meter.work(1)?;
                if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                        "source-modules/project-import",
                    )));
                }
                engine.environment = crate::merge_frontier_entry(engine.environment, entry)
                    .map_err(|_| unavailable(name, "conflicting checked import declarations"))?;
            }
            imported.insert(name.clone());
            dependencies.insert(name.clone(), module.imports.clone());
        }
        // The full closure's checker projection is not valid for a subset. The
        // ordinary admission path constructs a checker for the projected world.
        engine.checker_environment = None;
        engine.imported_modules = Arc::new(imported);
        engine.imported_module_dependencies = Arc::new(dependencies);
        engine.imported_environment = bound.then(|| engine.environment.clone());
        Ok(Outcome::Complete(engine))
    }

    pub(super) fn replay_metadata(
        &self,
        name: &Name,
        engine: Engine,
        options: &KVMap,
        meter: &mut Meter,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<Engine>, SourceModuleCheckError> {
        let module = &self.modules[name];
        let export =
            replay::Export::capture(name, &module.before, &module.after, Vec::new(), meter)?;
        export.replay(engine, name, options, meter, cancellation)
    }
}

impl imported::SourceOleanImport {
    /// Check each source module in its own declared import world. The retained
    /// import receipt, not caller-mutated public report fields, owns the bases.
    pub fn check_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
        cache::run_collecting(
            &self.contexts.complete,
            modules,
            entry,
            options,
            limits,
            cancellation,
            cache::RunOptions {
                cache: None,
                collect_artifacts: false,
                contexts: Some(&self.contexts),
            },
        )
        .map(|outcome| outcome.map_complete(|run| run.result.checked))
    }

    /// Encode only after the whole source graph has passed both checkers in
    /// exact import contexts. Unsupported source metadata still fails closed.
    pub fn compile_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        write_budget: OleanWriteBudget,
    ) -> Result<Outcome<SourceModuleBuild>, SourceModuleBuildError> {
        let base = &self.contexts.complete;
        if base.imported_environment.as_ref() != Some(base.environment()) {
            return Err(SourceModuleBuildError::UnboundBase);
        }
        let run = cache::run_collecting(
            base,
            modules,
            entry,
            options,
            limits,
            None,
            cache::RunOptions {
                cache: None,
                collect_artifacts: true,
                contexts: Some(&self.contexts),
            },
        )
        .map_err(SourceModuleBuildError::Check)?;
        match run {
            Outcome::Complete(run) => artifacts::finish(run, write_budget).map(Outcome::Complete),
            Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
        }
    }
}
