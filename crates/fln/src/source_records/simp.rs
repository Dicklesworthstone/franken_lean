//! Lazy source equation theorems are ordinary untrusted declaration candidates.
//! Retain their own council receipts, and publish metadata only with the whole
//! successful source command. The source journal never grants proof authority.
use super::*;
use fln_elab::source::scope::{SourceScope, simp as source_simp};

fn metadata_error(error: source_simp::SimpSetError) -> EngineExecutionError {
    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
        fln_elab::NatDefinitionElabError::Inference(
            fln_elab::source::SourceInferenceError::SimpSet(error),
        ),
    ))
}

impl Engine {
    /// Freeze equation policy where a source definition is introduced. A later
    /// attribute command must not substitute its own options or exposure scope.
    pub(crate) fn freeze_source_equation_policy(
        &self,
        declaration: &Declaration,
        scope: &SourceScope,
        options: &KVMap,
        kernel: Budget,
    ) -> Result<Outcome<Self>, EngineExecutionError> {
        let Declaration::Defn(definition) = declaration else {
            return Ok(Outcome::Complete(self.clone()));
        };
        Ok(
            elaboration_outcome(source_simp::equations::freeze_definition(
                self.environment(),
                &definition.base.name,
                scope,
                options,
                kernel,
            ))?
            .map_complete(|environment| {
                let mut next = self.clone();
                next.environment = environment;
                next
            }),
        )
    }

    /// Prepare the optional equation theorem, admit it through both checkers,
    /// and only then install its provenance, tags and requested simp entries.
    /// `activate = false` supports a lexical local attribute without adding a
    /// global simp rule; its checked generated theorem remains a declaration.
    /// A default policy is implicit only for a newly admitted owner in this
    /// source file. Definitions inherited from an earlier API call or import
    /// need explicit frozen provenance; they retain the prior source-only
    /// unfolding behavior when that provenance is unavailable.
    pub(crate) fn apply_checked_source_simp(
        &self,
        name: &Name,
        rule: Option<(u32, bool)>,
        activate: bool,
        source_owned: bool,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let root = self.logical_root(options);
        let mut batch = DeclarationBatchAdmission {
            engine: self.clone(),
            base_logical_root: root,
            result_logical_root: root,
            admissions: Vec::new(),
            local_instance: None,
        };
        let mut equations = Vec::new();
        if let Some((_, false)) = rule {
            let preparation = if source_owned {
                source_simp::equations::prepare_owned(
                    batch.engine.environment(),
                    name,
                    limits.kernel,
                )
            } else {
                source_simp::equations::prepare(batch.engine.environment(), name, limits.kernel)
            };
            match elaboration_outcome(preparation)? {
                Outcome::Complete(source_simp::equations::Preparation::Ready(candidate)) => {
                    let Declaration::Thm(theorem) = &candidate.declaration else {
                        return Err(EngineExecutionError::UnexpectedPublication {
                            detail: "a source simp equation candidate must be a theorem",
                        });
                    };
                    equations.push(theorem.base.name.clone());
                    if !candidate.existing {
                        let admitted = match batch.engine.admit_declaration(
                            candidate.declaration.clone(),
                            options,
                            limits,
                        )? {
                            Outcome::Complete(admitted) => admitted,
                            Outcome::Inconclusive(reason) => {
                                return Ok(Outcome::Inconclusive(reason));
                            }
                            Outcome::InternalFault(fault) => {
                                return Ok(Outcome::InternalFault(fault));
                            }
                        };
                        batch.engine = admitted.engine.clone();
                        batch.admissions.push(admitted);
                    }
                    batch.engine.environment =
                        match elaboration_outcome(source_simp::equations::finish(
                            batch.engine.environment(),
                            &candidate,
                            limits.kernel,
                        ))? {
                            Outcome::Complete(environment) => environment,
                            Outcome::Inconclusive(reason) => {
                                return Ok(Outcome::Inconclusive(reason));
                            }
                            Outcome::InternalFault(fault) => {
                                return Ok(Outcome::InternalFault(fault));
                            }
                        };
                }
                Outcome::Complete(source_simp::equations::Preparation::Unsupported)
                    if source_owned && activate =>
                {
                    let candidates =
                        match elaboration_outcome(source_simp::equations::prepare_pattern_owned(
                            batch.engine.environment(),
                            name,
                            limits.kernel,
                        ))? {
                            Outcome::Complete(candidates) => candidates,
                            Outcome::Inconclusive(reason) => {
                                return Ok(Outcome::Inconclusive(reason));
                            }
                            Outcome::InternalFault(fault) => {
                                return Ok(Outcome::InternalFault(fault));
                            }
                        };
                    for (candidate, existing) in candidates {
                        let Declaration::Thm(theorem) = &candidate else {
                            return Err(EngineExecutionError::UnexpectedPublication {
                                detail: "a source pattern equation candidate must be a theorem",
                            });
                        };
                        let equation = theorem.base.name.clone();
                        if !existing {
                            let admitted =
                                match batch.engine.admit_declaration(candidate, options, limits)? {
                                    Outcome::Complete(admitted) => admitted,
                                    Outcome::Inconclusive(reason) => {
                                        return Ok(Outcome::Inconclusive(reason));
                                    }
                                    Outcome::InternalFault(fault) => {
                                        return Ok(Outcome::InternalFault(fault));
                                    }
                                };
                            batch.engine = admitted.engine.clone();
                            batch.admissions.push(admitted);
                        }
                        batch.engine.environment =
                            match elaboration_outcome(source_simp::defeq::infer_generated(
                                batch.engine.environment(),
                                &equation,
                                limits.kernel,
                            ))? {
                                Outcome::Complete(environment) => environment,
                                Outcome::Inconclusive(reason) => {
                                    return Ok(Outcome::Inconclusive(reason));
                                }
                                Outcome::InternalFault(fault) => {
                                    return Ok(Outcome::InternalFault(fault));
                                }
                            };
                        equations.push(equation);
                    }
                }
                // Keep the existing source simplifier's supported unfolding
                // behavior for shapes whose exact equation export is not yet
                // implemented. Their export snapshot remains unsupported.
                Outcome::Complete(
                    source_simp::equations::Preparation::NotRequired
                    | source_simp::equations::Preparation::Unsupported,
                ) => {}
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
        }
        if activate {
            if let Some((priority, false)) = rule {
                for equation in &equations {
                    batch.engine.environment = source_simp::update(
                        batch.engine.environment(),
                        equation,
                        Some((priority, false)),
                    )
                    .map_err(metadata_error)?;
                }
                if !equations.is_empty() {
                    batch.engine.environment = source_simp::register_unfold_theorems(
                        batch.engine.environment(),
                        name,
                        &equations,
                    )
                    .map_err(metadata_error)?;
                }
            }
            batch.engine.environment = source_simp::update(batch.engine.environment(), name, rule)
                .map_err(metadata_error)?;
        } else {
            // Validate the same requested rule without retaining its global
            // activation. The lexical scope driver owns the local SimpEntry.
            source_simp::update(batch.engine.environment(), name, rule).map_err(metadata_error)?;
        }
        batch.result_logical_root = batch.engine.logical_root(options);
        Ok(Outcome::Complete(batch))
    }

    /// Complete primary metadata and lifted helpers before adding equation
    /// receipts; stages that require a single primary cannot see synthetic rows.
    pub(crate) fn finish_source_simp_batch(
        &self,
        mut batch: DeclarationBatchAdmission,
        registration: Option<(Name, u32, bool)>,
        scope: &SourceScope,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        if let Some(primary) = batch.admissions.first() {
            batch.engine = match batch.engine.freeze_source_equation_policy(
                &primary.declaration,
                scope,
                options,
                limits.kernel,
            )? {
                Outcome::Complete(engine) => engine,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        }
        if let Some((name, priority, reverse)) = registration {
            let name = scope.declaration_name(&name).map_err(|error| {
                EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                    fln_elab::NatDefinitionElabError::Inference(
                        fln_elab::source::SourceInferenceError::NameScope(error),
                    ),
                ))
            })?;
            let checked = match batch.engine.apply_checked_source_simp(
                &name,
                Some((priority, reverse)),
                true,
                true,
                options,
                limits,
            )? {
                Outcome::Complete(checked) => checked,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            batch.engine = checked.engine;
            batch.admissions.extend(checked.admissions);
        }
        batch.result_logical_root = batch.engine.logical_root(options);
        Ok(Outcome::Complete(batch))
    }

    pub(crate) fn finish_source_simp_admission(
        &self,
        admitted: SourceDeclarationAdmission,
        registration: Option<(Name, u32, bool)>,
        scope: &SourceScope,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<SourceDeclarationAdmission>, EngineExecutionError> {
        let declaration = admitted.declaration.clone();
        let checker = admitted.checker;
        Ok(self
            .finish_source_simp_batch(admitted.into_batch(), registration, scope, options, limits)?
            .map_complete(|batch| SourceDeclarationAdmission {
                engine: batch.engine,
                declaration,
                checker,
                base_logical_root: batch.base_logical_root,
                result_logical_root: batch.result_logical_root,
                admissions: batch.admissions,
            }))
    }
}
