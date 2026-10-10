//! Separate public and private source worlds. Exported declarations are checked
//! entirely against exported imports and prior exports, then ordinarily admitted
//! into the full module world. No filtered or caller-authored proof is trusted.
use super::*;

/// This receipt is private to the source module driver. Its public engine never
/// contains a private dependency or a module-local private declaration.
pub(crate) struct PublicWorld<'a> {
    module: Name,
    initial: Environment,
    engine: Engine,
    scope: fln_elab::source::scope::SourceScope,
    declarations: Vec<Declaration>,
    meter: &'a mut Meter,
    cancellation: Option<&'a dyn CancellationProbe>,
}

impl<'a> PublicWorld<'a> {
    pub(super) fn new(
        module: &Name,
        engine: Engine,
        meter: &'a mut Meter,
        cancellation: Option<&'a dyn CancellationProbe>,
    ) -> Self {
        let scope = fln_elab::source::scope::SourceScope {
            private_module: Some(module.clone()),
            frontier_recursors: engine.mode().permits_frontier(),
            ..Default::default()
        };
        Self {
            module: module.clone(),
            initial: engine.environment.clone(),
            engine,
            scope,
            declarations: Vec::new(),
            meter,
            cancellation,
        }
    }

    pub(crate) fn engine(&self) -> &Engine {
        &self.engine
    }

    pub(crate) fn file_base(&self) -> &Environment {
        &self.initial
    }

    pub(crate) fn scope(&self) -> &fln_elab::source::scope::SourceScope {
        &self.scope
    }

    /// Save the actual final lexical prefix, including private commands between
    /// public declarations. Its activation anchors belong to this engine only.
    pub(crate) fn retain_scope(&mut self, scope: fln_elab::source::scope::SourceScope) {
        self.scope = scope;
    }

    /// Publish one successfully checked public command in both worlds. A failure
    /// in name collision checking, replay or metadata leaves this receipt intact.
    pub(crate) fn publish(
        &mut self,
        private: &Engine,
        next: Engine,
        declarations: Vec<Declaration>,
        scope: &fln_elab::source::scope::SourceScope,
        options: &KVMap,
    ) -> Result<Outcome<Engine>, EngineExecutionError> {
        if !declarations.is_empty() {
            for (name, _) in next.environment().constants() {
                self.meter.work(1).map_err(execution_error)?;
                if self
                    .cancellation
                    .is_some_and(CancellationProbe::is_cancelled)
                {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                        "source-module/public-name",
                    )));
                }
                if !self.engine.environment().contains(name) {
                    scope
                        .check_public_name(name, private.environment())
                        .map_err(DefinitionFrontendError::Elaborate)
                        .map_err(EngineExecutionError::Frontend)?;
                }
            }
        }
        let export = replay::Export::capture(
            &self.module,
            self.engine.environment(),
            next.environment(),
            declarations.clone(),
            self.meter,
        )
        .map_err(execution_error)?;
        let replayed = export
            .replay(
                private.clone(),
                &self.module,
                options,
                self.meter,
                self.cancellation,
            )
            .map_err(execution_error)?;
        if matches!(replayed, Outcome::Complete(_)) {
            self.engine = next;
            self.declarations.extend(declarations);
        }
        Ok(replayed)
    }

    pub(super) fn finish(self) -> Result<replay::Export, SourceModuleCheckError> {
        replay::Export::capture(
            &self.module,
            &self.initial,
            self.engine.environment(),
            self.declarations,
            self.meter,
        )
    }
}

/// Build the module's exported import world independently of the private world.
/// The mixed source/artifact order is retained, including instance precedence.
#[allow(clippy::too_many_arguments)]
pub(super) fn imports<'e>(
    base: &Engine,
    contexts: Option<&contexts::ImportContexts>,
    index: usize,
    plan: &graph::Plan,
    modules: &[SourceModuleInput<'_>],
    export: impl Fn(usize) -> &'e replay::Export,
    options: &KVMap,
    meter: &mut Meter,
    cancellation: Option<&dyn CancellationProbe>,
) -> Result<Outcome<(Engine, usize)>, SourceModuleCheckError> {
    let steps = match contexts {
        Some(contexts) => contexts.public_order(index, plan, modules, meter)?,
        None => plan
            .public_dependencies_of(index, modules, meter)?
            .into_iter()
            .map(contexts::Step::Source)
            .collect(),
    };
    let mut engine = match contexts {
        Some(contexts) => match contexts.project(&steps, meter, cancellation)? {
            Outcome::Complete(engine) => engine,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        },
        None => base.clone(),
    };
    let mut replayed_declarations = 0usize;
    for step in steps {
        let replayed = match step {
            contexts::Step::Source(dependency) => {
                let export = export(dependency);
                replayed_declarations += export.declarations.len();
                export.replay(
                    engine,
                    modules[dependency].name,
                    options,
                    meter,
                    cancellation,
                )?
            }
            contexts::Step::External(name) => contexts
                .expect("external import steps have retained contexts")
                .replay_metadata(&name, engine, options, meter, cancellation)?,
        };
        engine = match replayed {
            Outcome::Complete(engine) => engine,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
    }
    Ok(Outcome::Complete((engine, replayed_declarations)))
}

fn execution_error(error: SourceModuleCheckError) -> EngineExecutionError {
    match error {
        SourceModuleCheckError::Replay { error, .. } => *error,
        SourceModuleCheckError::Source { error, .. } => error.into_execution_error(),
        SourceModuleCheckError::Limit { resource, limit } => {
            EngineExecutionError::SourceScopeLimit { resource, limit }
        }
        SourceModuleCheckError::Extension { reason, .. } => {
            EngineExecutionError::NotImplemented { feature: reason }
        }
        other => EngineExecutionError::ScopeTransition {
            message: other.to_string(),
        },
    }
}
