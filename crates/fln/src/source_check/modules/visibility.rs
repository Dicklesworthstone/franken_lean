//! Separate public and private source worlds. Exported declarations are checked
//! against exported imports and prior exports. A hidden proof fixes its statement
//! in that world, checks its implementation privately, and exports the checked signature.
//! Every declaration still passes ordinary admission; no caller-authored proof is trusted.
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

struct StagedPublicEquations {
    public: Engine,
    private: Engine,
    admissions: Vec<crate::DeclarationAdmission>,
    declarations: Vec<Declaration>,
}

pub(crate) struct PrivateSourceAdmission {
    pub(crate) engine: Engine,
    pub(crate) admission: DeclarationBatchAdmission,
    pub(crate) traces: Vec<fln_elab::source::trace::SourceTrace>,
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
            ..engine.base_source_scope()
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

    /// An implementation may first request an exposed public definition's
    /// equation. Stage only those checked equations in both worlds; the caller
    /// publishes them only after the complete source command succeeds.
    #[allow(clippy::too_many_arguments)]
    fn stage_command_equations(
        &mut self,
        private: &Engine,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
        source_base: Option<&Environment>,
    ) -> Result<Outcome<StagedPublicEquations>, EngineExecutionError> {
        use fln_elab::source::equation_theorems::{self as equations, Request, Suffix};
        use fln_elab::source::scope::simp::equations as simp_equations;

        if !crate::source_records::may_name_equation_theorems(source) {
            return Ok(Outcome::Complete(StagedPublicEquations {
                public: self.engine.clone(),
                private: private.clone(),
                admissions: Vec::new(),
                declarations: Vec::new(),
            }));
        }
        let parsed = crate::source_records::parse_scoped_command(source)?;
        let syntaxes: Vec<_> = match &parsed {
            crate::source_records::ScopedCommandSyntax::Mutual(members) => members.iter().collect(),
            crate::source_records::ScopedCommandSyntax::Example(parsed) => vec![parsed.syntax()],
            crate::source_records::ScopedCommandSyntax::Definition(parsed) => vec![parsed.syntax()],
        };
        // Resolve names in the real private lexical scope. A same-spelled
        // private definition must never trigger generation for a public one.
        let requests = match crate::source_records::elaboration_outcome(equations::requests(
            &syntaxes,
            private.environment(),
            scope,
            limits.kernel,
        ))? {
            Outcome::Complete(requests) => requests,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut public = self.engine.clone();
        let mut equations = Vec::new();
        for request in requests {
            if self
                .cancellation
                .is_some_and(CancellationProbe::is_cancelled)
            {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "source-module/private-equations",
                )));
            }
            let origin = match request {
                Request::Equations(origin) => Some(origin),
                Request::Name(name) => equations::target(private.environment(), &name)
                    .and_then(|(origin, suffix)| (suffix == Suffix::Equation).then_some(origin)),
            };
            let Some(origin) = origin else { continue };
            if source_base.is_some_and(|base| base.contains(&origin))
                || self.initial.contains(&origin)
            {
                continue;
            }
            // The body must be the same exposed definition in both worlds.
            // Hidden interfaces, private declarations and imported defaults
            // provide no authority to infer an exposed source policy here.
            if !matches!(
                (public.environment().find(&origin), private.environment().find(&origin)),
                (Some(ConstantInfo::Defn(exported)), Some(ConstantInfo::Defn(local)))
                    if exported == local && exported.safety == DefinitionSafety::Safe
            ) {
                continue;
            }
            let candidate = match crate::source_records::elaboration_outcome(
                simp_equations::prepare_owned(public.environment(), &origin, limits.kernel),
            )? {
                Outcome::Complete(simp_equations::Preparation::Ready(candidate)) => candidate,
                Outcome::Complete(
                    simp_equations::Preparation::NotRequired
                    | simp_equations::Preparation::Unsupported,
                ) => continue,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            if candidate.existing {
                continue;
            }
            let status = |environment: &Environment| {
                fln_elab::reducibility::table(environment)
                    .map(|table| table.status(&origin))
                    .map_err(|error| {
                        fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::Unification(Box::new(
                                fln_elab::constraint::unify::UnificationError::Reducibility(error),
                            )),
                        )
                    })
            };
            match crate::source_records::elaboration_outcome(
                status(public.environment()).and_then(|exported| {
                    status(private.environment()).map(|local| exported == local)
                }),
            )? {
                Outcome::Complete(true) => {}
                Outcome::Complete(false) => continue,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
            // A private reducibility attribute can differ without changing
            // the constant record. Require the private realization policy and
            // candidate too before moving a public equation into that world.
            match crate::source_records::elaboration_outcome(simp_equations::prepare_owned(
                private.environment(),
                &origin,
                limits.kernel,
            ))? {
                Outcome::Complete(simp_equations::Preparation::Ready(local))
                    if local == candidate => {}
                Outcome::Complete(_) => continue,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
            let admitted =
                match public.admit_declaration(candidate.declaration.clone(), options, limits)? {
                    Outcome::Complete(admitted) => admitted,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
            public = admitted.engine.clone();
            public.environment = match crate::source_records::elaboration_outcome(
                simp_equations::finish(public.environment(), &candidate, limits.kernel),
            )? {
                Outcome::Complete(environment) => environment,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            equations.push(admitted);
        }
        let declarations: Vec<_> = equations
            .iter()
            .map(|admitted| admitted.declaration.clone())
            .collect();
        let staged = if equations.is_empty() {
            private.clone()
        } else {
            let mut public_scope = scope.clone();
            public_scope.public_declarations = true;
            match self.check_new_names(private, &public, &public_scope)? {
                Outcome::Complete(()) => {}
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
            let export = replay::Export::capture(
                &self.module,
                self.engine.environment(),
                public.environment(),
                declarations.clone(),
                self.meter,
            )
            .map_err(execution_error)?;
            match export
                .replay(
                    private.clone(),
                    &self.module,
                    options,
                    self.meter,
                    self.cancellation,
                )
                .map_err(execution_error)?
            {
                Outcome::Complete(engine) => engine,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
        };
        Ok(Outcome::Complete(StagedPublicEquations {
            public,
            private: staged,
            admissions: equations,
            declarations,
        }))
    }

    /// A private theorem's generated public equations remain provisional until
    /// its proof passes both checkers. Executable source retains any observations.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn admit_private_command(
        &mut self,
        private: &Engine,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
        source_base: &Environment,
        observed: Option<&fln_parse::ParsedSourceCommand>,
    ) -> Result<Outcome<PrivateSourceAdmission>, EngineExecutionError> {
        let mut staged = match self.stage_command_equations(
            private,
            source,
            options,
            limits,
            scope,
            Some(source_base),
        )? {
            Outcome::Complete(staged) => staged,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let (mut checked, traces) = if let Some(parsed) = observed {
            // Observed elaboration has no lazy prepass of its own. Keep the
            // ordinary private equations and their receipts before collecting
            // observations, just as the unobserved command path does.
            let mut equations = match staged.private.realize_equation_theorems(
                &[parsed.syntax()],
                scope,
                options,
                limits,
                Some(source_base),
            )? {
                Outcome::Complete(equations) => equations,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            let engine = equations
                .as_ref()
                .map_or(&staged.private, |batch| &batch.engine);
            let mut observed =
                match engine.admit_observed_source_definition(parsed, options, limits, scope)? {
                    Outcome::Complete(observed) => observed,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
            if let Some(mut equations) = equations.take() {
                equations
                    .admissions
                    .append(&mut observed.admission.admissions);
                observed.admission.admissions = equations.admissions;
                observed.admission.base_logical_root = equations.base_logical_root;
            }
            (observed.admission, observed.traces)
        } else {
            let checked = match staged.private.admit_source_command_in_scope_with_base(
                source,
                options,
                limits,
                scope,
                Some(source_base),
            )? {
                Outcome::Complete(checked) => checked,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            (checked, Vec::new())
        };
        if self
            .cancellation
            .is_some_and(CancellationProbe::is_cancelled)
        {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-module/private-equations",
            )));
        }
        if !staged.admissions.is_empty() {
            staged.admissions.append(&mut checked.admissions);
            checked.admissions = staged.admissions;
            checked.base_logical_root = private.logical_root(options);
            self.engine = staged.public;
            self.declarations.extend(staged.declarations);
        }
        Ok(Outcome::Complete(PrivateSourceAdmission {
            engine: checked.engine.clone(),
            admission: checked,
            traces,
        }))
    }

    /// Check and atomically publish a source command in its appropriate worlds.
    /// The returned admission retains the proof's ordinary council evidence;
    /// only this receipt's export journal substitutes its safe signature.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn admit_command(
        &mut self,
        private: &Engine,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
        public_scope: &fln_elab::source::scope::SourceScope,
        private_scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<(Engine, DeclarationBatchAdmission)>, EngineExecutionError> {
        if self
            .cancellation
            .is_some_and(CancellationProbe::is_cancelled)
        {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-module/public-command",
            )));
        }
        let mut equations = match self.stage_command_equations(
            private,
            source,
            options,
            limits,
            private_scope,
            None,
        )? {
            Outcome::Complete(equations) => equations,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut staged = match equations.private.admit_public_source_command_in_scope(
            &equations.public,
            source,
            options,
            limits,
            public_scope,
            private_scope,
        )? {
            Outcome::Complete(staged) => staged,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut declarations = equations.declarations;
        declarations.extend(
            staged
                .public
                .admissions
                .iter()
                .map(|row| row.declaration.clone()),
        );
        let Some(mut checked) = staged.private_implementation else {
            if !equations.admissions.is_empty() {
                equations.admissions.append(&mut staged.public.admissions);
                staged.public.admissions = equations.admissions;
                staged.public.base_logical_root = self.engine.logical_root(options);
            }
            return Ok(
                match self.publish(
                    private,
                    staged.public.engine.clone(),
                    declarations,
                    public_scope,
                    options,
                )? {
                    Outcome::Complete(engine) => Outcome::Complete((engine, staged.public)),
                    Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                },
            );
        };
        match self.check_new_names(private, &staged.public.engine, public_scope)? {
            Outcome::Complete(()) => {}
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        }
        // The private successor already contains its checked theorem, including
        // a proof-valued instance. Replay only metadata, never the same-name
        // public axiom over that checked implementation. Both worlds retain identical
        // instance priorities and reducibility without exposing a private body.
        let metadata = replay::Export::capture(
            &self.module,
            equations.public.environment(),
            staged.public.engine.environment(),
            Vec::new(),
            self.meter,
        )
        .map_err(execution_error)?;
        let engine = match metadata
            .replay(
                checked.engine.clone(),
                &self.module,
                options,
                self.meter,
                self.cancellation,
            )
            .map_err(execution_error)?
        {
            Outcome::Complete(engine) => engine,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        if self
            .cancellation
            .is_some_and(CancellationProbe::is_cancelled)
        {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-module/public-proof",
            )));
        }
        checked.engine = engine.clone();
        checked.result_logical_root = engine.logical_root(options);
        checked.local_instance = staged.public.local_instance;
        if !equations.admissions.is_empty() {
            equations.admissions.append(&mut checked.admissions);
            checked.admissions = equations.admissions;
            checked.base_logical_root = private.logical_root(options);
        }
        self.engine = staged.public.engine;
        self.declarations.extend(declarations);
        Ok(Outcome::Complete((engine, checked)))
    }

    fn check_new_names(
        &mut self,
        private: &Engine,
        next: &Engine,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<()>, EngineExecutionError> {
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
        Ok(Outcome::Complete(()))
    }

    /// Publish the public subset of an already staged global default attribute.
    /// The private journal keeps its complete source order; replaying the public
    /// subset into it would duplicate registrations and change equal priorities.
    pub(crate) fn publish_default_attributes(
        &mut self,
        private: &Engine,
        next_private: Environment,
    ) -> Result<Outcome<Engine>, EngineExecutionError> {
        if self
            .cancellation
            .is_some_and(CancellationProbe::is_cancelled)
        {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-module/default-attributes",
            )));
        }
        let remaining = self.meter.limits.max_work.saturating_sub(self.meter.work);
        let registrations = fln_elab::instances::defaults::registrations(
            private.environment(),
            &next_private,
            remaining,
        )
        .map_err(|error| {
            execution_error(match error {
                fln_elab::instances::InstanceRegistryError::Limit => {
                    SourceModuleCheckError::Limit {
                        resource: "module work",
                        limit: self.meter.limits.max_work,
                    }
                }
                _ => SourceModuleCheckError::Extension {
                    module: self.module.clone(),
                    extension: fln_elab::instances::defaults::journal_name(),
                    reason: "default attributes must extend the checked predecessor journal",
                },
            })
        })?;
        self.meter
            .work(registrations.work)
            .map_err(execution_error)?;
        self.meter
            .bytes(registrations.bytes_examined)
            .map_err(execution_error)?;
        let mut next_public = self.engine.clone();
        for registration in registrations.entries {
            self.meter.work(1).map_err(execution_error)?;
            if self
                .cancellation
                .is_some_and(CancellationProbe::is_cancelled)
            {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "source-module/default-attributes",
                )));
            }
            let candidate = &registration.candidate;
            if next_public.environment().contains(&candidate.declaration) {
                next_public.environment = fln_elab::instances::defaults::register(
                    next_public.environment(),
                    &candidate.declaration,
                    candidate.priority,
                )
                .map_err(|error| {
                    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                        fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::InstanceRegistry(error),
                        ),
                    ))
                })?;
            }
        }
        replay::Export::capture(
            &self.module,
            self.engine.environment(),
            next_public.environment(),
            Vec::new(),
            self.meter,
        )
        .map_err(execution_error)?;
        if self
            .cancellation
            .is_some_and(CancellationProbe::is_cancelled)
        {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-module/default-attributes",
            )));
        }
        let mut next = private.clone();
        next.environment = next_private;
        self.engine = next_public;
        Ok(Outcome::Complete(next))
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
            match self.check_new_names(private, &next, scope)? {
                Outcome::Complete(()) => {}
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
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
