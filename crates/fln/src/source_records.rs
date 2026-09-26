//! One source command may expand to multiple mutually dependent declarations.
//! Preserve the ordinary per-declaration evidence and publish only a full batch.
use super::*;

impl EngineBuilder {
    /// Construct a bounded coercion-seed engine using the specified admission limits.
    pub fn build_with_coercion_seed(
        &self,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<Engine>, EngineAdmissionError> {
        let engine = match self.build_with_source_seed(limits)? {
            Outcome::Complete(engine) => engine,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let seed = fln_elab::instances::coercions::declarations().map_err(|_| {
            EngineAdmissionError::UnexpectedPublication {
                detail: "coercion seed construction failed",
            }
        })?;
        let mut engine =
            match engine.admit_declarations(&seed.declarations, &self.options, limits)? {
                Outcome::Complete(batch) => batch.engine,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        for name in seed.classes {
            engine.environment = fln_elab::instances::register_class(&engine.environment, &name)
                .map_err(|_| EngineAdmissionError::UnexpectedPublication {
                    detail: "coercion class registration failed",
                })?;
        }
        for name in seed.instances {
            engine.environment =
                fln_elab::instances::register_instance(&engine.environment, &name, 1000).map_err(
                    |_| EngineAdmissionError::UnexpectedPublication {
                        detail: "coercion instance registration failed",
                    },
                )?;
        }
        Ok(Outcome::Complete(engine))
    }

    /// Construct a bounded coercion-seed engine using configured or default calibrated limits.
    pub fn build_coercion_seed(&self) -> Result<Outcome<Engine>, EngineAdmissionError> {
        let limits = self.admission_limits.unwrap_or_else(|| {
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
        });
        self.build_with_coercion_seed(limits)
    }
}

impl Engine {
    /// Build the native source environment with the staged coercion library.
    /// Every class, eliminator, projection and composition instance passes both
    /// checking engines before any of its registrations become observable.
    pub fn with_coercion_seed(
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<Self>, EngineAdmissionError> {
        Self::builder().build_with_coercion_seed(limits)
    }

    /// Admit one definition, theorem, instance, structure, class or inductive command,
    /// including a complete `mutual ... end` inductive group.
    /// A record's block and projections all pass K1 and the independent checker
    /// before class metadata is registered. No failed prefix is exposed.
    pub fn admit_source_command(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        self.admit_source_command_in_scope(
            source,
            options,
            limits,
            &fln_elab::source::scope::SourceScope::default(),
        )
    }

    pub(crate) fn admit_source_command_in_scope(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        if let Some(members) = fln_parse::command_scope::mutual::parse(source)
            .map_err(DefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?
        {
            let candidate = if members.len() == 1 {
                fln_elab::source::scope::elaborate_inductive(
                    &members[0],
                    self.environment(),
                    limits.kernel,
                    fln_elab::records::RecordBudget::default(),
                    scope,
                )
            } else {
                fln_elab::source::scope::elaborate_mutual_inductives(
                    &members,
                    self.environment(),
                    limits.kernel,
                    fln_elab::records::RecordBudget::default(),
                    scope,
                )
            }
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
            return self
                .admit_declarations(&[candidate], options, limits)
                .map_err(EngineExecutionError::from);
        }
        let parsed = fln_parse::parse_definition(source)
            .map_err(DefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        if fln_elab::source::scope::is_example(parsed.syntax()) {
            let parsed = fln_parse::parse_source_command(source)
                .map_err(DefinitionFrontendError::Parse)
                .map_err(EngineExecutionError::Frontend)?;
            return Ok(
                match self
                    .check_parsed_source_command_in_scope(parsed, options, limits, 0, scope)?
                {
                    Outcome::Complete(_) => {
                        let root = self.logical_root(options);
                        Outcome::Complete(DeclarationBatchAdmission {
                            engine: self.clone(),
                            base_logical_root: root,
                            result_logical_root: root,
                            admissions: Vec::new(),
                        })
                    }
                    Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                },
            );
        }
        if fln_elab::source::is_inductive(parsed.syntax()) {
            let candidate = fln_elab::source::scope::elaborate_inductive(
                parsed.syntax(),
                self.environment(),
                limits.kernel,
                fln_elab::records::RecordBudget::default(),
                scope,
            )
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
            return self
                .admit_declarations(&[candidate], options, limits)
                .map_err(EngineExecutionError::from);
        }
        if !fln_elab::source::is_record(parsed.syntax()) {
            if scope != &fln_elab::source::scope::SourceScope::default() {
                let declaration = fln_elab::source::scope::elaborate_definition(
                    parsed.syntax(),
                    self.environment(),
                    limits.kernel,
                    scope,
                )
                .map_err(DefinitionFrontendError::Elaborate)
                .map_err(EngineExecutionError::Frontend)?;
                let registration = fln_elab::source::instance_registration(parsed.syntax())
                    .map_err(DefinitionFrontendError::Elaborate)
                    .map_err(EngineExecutionError::Frontend)?;
                let simp = fln_elab::source::scope::simp::registration(parsed.syntax())
                    .map_err(DefinitionFrontendError::Elaborate)
                    .map_err(EngineExecutionError::Frontend)?;
                let result = self
                    .admit_declarations(&[declaration], options, limits)
                    .map_err(EngineExecutionError::from)?;
                return Ok(match result {
                    Outcome::Complete(mut batch) => {
                        if let Some((name, priority)) = registration {
                            let name = scope.declaration_name(&name).map_err(|error| {
                                EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                                    fln_elab::NatDefinitionElabError::Inference(
                                        fln_elab::source::SourceInferenceError::NameScope(error),
                                    ),
                                ))
                            })?;
                            batch.engine.environment = fln_elab::instances::register_instance(
                                batch.engine.environment(),
                                &name,
                                priority,
                            )
                            .map_err(|error| {
                                EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                                    fln_elab::NatDefinitionElabError::Inference(
                                        fln_elab::source::SourceInferenceError::InstanceRegistry(
                                            error,
                                        ),
                                    ),
                                ))
                            })?;
                            batch.result_logical_root = batch.engine.logical_root(options);
                        }
                        if let Some((name, priority, reverse)) = simp {
                            let name = scope.declaration_name(&name).map_err(|error| {
                                EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                                    fln_elab::NatDefinitionElabError::Inference(
                                        fln_elab::source::SourceInferenceError::NameScope(error),
                                    ),
                                ))
                            })?;
                            batch.engine.environment = fln_elab::source::scope::simp::update(
                                batch.engine.environment(),
                                &name,
                                Some((priority, reverse)),
                            )
                            .map_err(|error| {
                                EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                                    fln_elab::NatDefinitionElabError::Inference(
                                        fln_elab::source::SourceInferenceError::SimpSet(error),
                                    ),
                                ))
                            })?;
                            batch.result_logical_root = batch.engine.logical_root(options);
                        }
                        Outcome::Complete(batch)
                    }
                    Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                });
            }
            return Ok(
                match self.admit_source_declaration(source, options, limits)? {
                    Outcome::Complete(admitted) => Outcome::Complete(DeclarationBatchAdmission {
                        engine: admitted.engine.clone(),
                        base_logical_root: admitted.base_logical_root,
                        result_logical_root: admitted.result_logical_root,
                        admissions: vec![admitted],
                    }),
                    Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                },
            );
        }
        let record = fln_elab::source::scope::elaborate_record(
            parsed.syntax(),
            self.environment(),
            limits.kernel,
            fln_elab::records::RecordBudget::default(),
            scope,
        )
        .map_err(DefinitionFrontendError::Elaborate)
        .map_err(EngineExecutionError::Frontend)?;
        let result = self
            .admit_declarations(&record.declarations, options, limits)
            .map_err(EngineExecutionError::from)?;
        Ok(match result {
            Outcome::Complete(mut batch) => {
                batch.engine.environment = fln_elab::records::defaults::register_defaults(
                    batch.engine.environment(),
                    &record.defaults,
                )
                .map_err(|error| {
                    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                        fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::Record(error),
                        ),
                    ))
                })?;
                batch.engine.environment = fln_elab::records::inheritance::register_parents(
                    batch.engine.environment(),
                    &record.parents,
                )
                .map_err(|error| {
                    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                        fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::Record(error),
                        ),
                    ))
                })?;
                if record.is_class {
                    batch.engine.environment = fln_elab::instances::register_class(
                        batch.engine.environment(),
                        &record.name,
                    )
                    .map_err(|error| {
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::InstanceRegistry(error),
                            ),
                        ))
                    })?;
                }
                for parent in &record.parent_instances {
                    batch.engine.environment = fln_elab::instances::register_instance(
                        batch.engine.environment(),
                        parent,
                        1000,
                    )
                    .map_err(|error| {
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::InstanceRegistry(error),
                            ),
                        ))
                    })?;
                }
                batch.result_logical_root = batch.engine.logical_root(options);
                Outcome::Complete(batch)
            }
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        })
    }
}
