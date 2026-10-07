//! One source command may expand to multiple mutually dependent declarations.
//! Preserve the ordinary per-declaration evidence and publish only a full batch.
use super::*;
use fln_kernel::verdict::Verdict;

/// Elaboration and admission share the same kernel nonanswer convention.
/// Preserve the kernel's complete cause; other frontend errors stay
/// in the error channel. In particular, a failed check is never a declaration.
pub(crate) fn elaboration_outcome<T>(
    result: Result<T, fln_elab::NatDefinitionElabError>,
) -> Result<Outcome<T>, EngineExecutionError> {
    use fln_elab::NatDefinitionElabError;
    use fln_elab::constraint::unify::UnificationError;
    use fln_elab::source::SourceInferenceError;

    let error = match result {
        Ok(value) => return Ok(Outcome::Complete(value)),
        Err(error) => error,
    };
    let kernel = match &error {
        NatDefinitionElabError::Inference(SourceInferenceError::TypeObligation(outcome)) => {
            Some(outcome.as_ref())
        }
        NatDefinitionElabError::Inference(SourceInferenceError::Unification(error)) => {
            match error.as_ref() {
                UnificationError::AssignmentCheck { outcome, .. }
                | UnificationError::ConversionCheck { outcome }
                | UnificationError::ConstraintCheck { outcome, .. } => Some(outcome.as_ref()),
                _ => None,
            }
        }
        _ => None,
    };
    match kernel {
        Some(Outcome::Inconclusive(reason)) => Ok(Outcome::Inconclusive(reason.clone())),
        Some(Outcome::InternalFault(fault)) => Ok(Outcome::InternalFault(fault.clone())),
        _ => Err(EngineExecutionError::Frontend(
            DefinitionFrontendError::Elaborate(error),
        )),
    }
}

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
        self.admit_source_command_in_scope(source, options, limits, &self.base_source_scope())
    }

    pub(crate) fn admit_source_command_in_scope(
        &self,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let parsed = match parse_scoped_command(source)? {
            ScopedCommandSyntax::Mutual(members) => {
                return self.admit_scoped_inductives(&members, options, limits, scope);
            }
            ScopedCommandSyntax::Example(parsed) => {
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
            ScopedCommandSyntax::Definition(parsed) => parsed,
        };
        self.admit_scoped_definition(source, parsed, options, limits, scope)
    }

    fn admit_scoped_inductives(
        &self,
        members: &[fln_syntax::tree::Syntax],
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let candidate = elaboration_outcome(if members.len() == 1 {
            fln_elab::source::scope::elaborate_inductive(
                &members[0],
                self.environment(),
                limits.kernel,
                fln_elab::records::RecordBudget::default(),
                scope,
            )
        } else {
            fln_elab::source::scope::elaborate_mutual_inductives(
                members,
                self.environment(),
                limits.kernel,
                fln_elab::records::RecordBudget::default(),
                scope,
            )
        })?;
        let candidate = match candidate {
            Outcome::Complete(candidate) => candidate,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        self.admit_declarations(&[candidate], options, limits)
            .map_err(EngineExecutionError::from)
    }

    fn admit_scoped_definition(
        &self,
        source: &[u8],
        parsed: fln_parse::ParsedDefinition,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let deriving =
            match elaboration_outcome(fln_elab::source::deriving::prepare(parsed.syntax()))? {
                Outcome::Complete(request) => request,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        let syntax = deriving
            .as_ref()
            .map_or_else(|| parsed.syntax(), |request| &request.syntax);
        if fln_elab::source::is_inductive(syntax) {
            let candidate =
                match elaboration_outcome(fln_elab::source::scope::elaborate_inductive(
                    syntax,
                    self.environment(),
                    limits.kernel,
                    fln_elab::records::RecordBudget::default(),
                    scope,
                ))? {
                    Outcome::Complete(candidate) => candidate,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
            let result = self
                .admit_declarations(&[candidate], options, limits)
                .map_err(EngineExecutionError::from)?;
            return self.finish_source_deriving(result, deriving.as_ref(), options, limits, scope);
        }
        if !fln_elab::source::is_record(syntax) {
            if scope != &fln_elab::source::scope::SourceScope::default() {
                let declaration =
                    match elaboration_outcome(fln_elab::source::scope::elaborate_definition(
                        parsed.syntax(),
                        self.environment(),
                        limits.kernel,
                        scope,
                    ))? {
                        Outcome::Complete(declaration) => declaration,
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    };
                let registration = fln_elab::source::instance_registration(parsed.syntax())
                    .map_err(DefinitionFrontendError::Elaborate)
                    .map_err(EngineExecutionError::Frontend)?;
                let simp = fln_elab::source::scope::simp::registration(parsed.syntax())
                    .map_err(DefinitionFrontendError::Elaborate)
                    .map_err(EngineExecutionError::Frontend)?;
                let protected = fln_elab::source::protected_registration(parsed.syntax())
                    .map_err(DefinitionFrontendError::Elaborate)
                    .map_err(EngineExecutionError::Frontend)?
                    .map(|name| scope.declaration_name(&name))
                    .transpose()
                    .map_err(|error| {
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::NameScope(error),
                            ),
                        ))
                    })?;
                // An anonymous instance is registered under the name its elaboration
                // generated, already qualified by the scope.
                let declared = match &declaration {
                    Declaration::Defn(definition) => Some(definition.base.name.clone()),
                    _ => None,
                };
                let result = self
                    .admit_declarations(&[declaration], options, limits)
                    .map_err(EngineExecutionError::from)?;
                return Ok(match result {
                    Outcome::Complete(mut batch) => {
                        if let Some((name, priority)) = registration {
                            let name = match (name.is_anonymous(), declared) {
                                (true, Some(declared)) => declared,
                                _ => scope.declaration_name(&name).map_err(|error| {
                                    EngineExecutionError::Frontend(
                                        DefinitionFrontendError::Elaborate(
                                            fln_elab::NatDefinitionElabError::Inference(
                                                fln_elab::source::SourceInferenceError::NameScope(
                                                    error,
                                                ),
                                            ),
                                        ),
                                    )
                                })?,
                            };
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
                        if let Some(name) = protected {
                            batch.engine.environment = tag_protected(&batch.engine, &name)?;
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
        let mut record = match elaboration_outcome(fln_elab::source::scope::elaborate_record(
            syntax,
            self.environment(),
            limits.kernel,
            fln_elab::records::RecordBudget::default(),
            scope,
        ))? {
            Outcome::Complete(record) => record,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut result = self
            .admit_declarations(&record.declarations, options, limits)
            .map_err(EngineExecutionError::from)?;
        if let Outcome::Complete(batch) = &result {
            // The pin emits proof projections as theorems, not definitions
            // (Lean/Meta/Structure.lean:99–116). Ask K1 under its supplied budget
            // against each projection's exact, already checked predecessor;
            // the actual declaration name is still fresh in that environment.
            // Defaults are ordinary definitions even when they return proofs.
            let mut predecessor = self;
            let mut proof_projection = false;
            for (index, admission) in batch.admissions.iter().enumerate() {
                if let Declaration::Defn(definition) = &admission.declaration
                    && !record
                        .defaults
                        .iter()
                        .any(|default| default.helper == definition.base.name)
                {
                    let theorem = Declaration::Thm(TheoremVal {
                        base: definition.base.clone(),
                        value: definition.value.clone(),
                        all: definition.all.clone(),
                    });
                    match fln_kernel::check(predecessor.environment(), &theorem, limits.kernel) {
                        Outcome::Complete(Verdict::Accepted { .. }) => {
                            record.declarations[index] = theorem;
                            proof_projection = true;
                        }
                        Outcome::Complete(Verdict::Rejected {
                            class: RejectClass::TheoremNotProp,
                            ..
                        }) => {}
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                        other => {
                            return Err(EngineExecutionError::Frontend(
                                DefinitionFrontendError::Elaborate(
                                    fln_elab::NatDefinitionElabError::Inference(
                                        fln_elab::source::SourceInferenceError::TypeObligation(
                                            Box::new(other),
                                        ),
                                    ),
                                ),
                            ));
                        }
                    }
                }
                predecessor = &admission.engine;
            }
            if proof_projection {
                // The classification probe grants no publication authority.
                // Recheck the corrected batch from the original predecessor so
                // both checkers certify every final declaration's actual kind.
                result = self
                    .admit_declarations(&record.declarations, options, limits)
                    .map_err(EngineExecutionError::from)?;
            }
        }
        let result = match result {
            Outcome::Complete(mut batch) => {
                // Projection hints and reducibility status are different facts.
                // Non-class data projections are reducible, class fields remain
                // semireducible, and parent instances are implicitReducible.
                // Default helpers remain semireducible despite Abbrev hints
                // (Lean/Elab/Structure.lean:1363–1386).
                for declaration in &record.declarations {
                    let Declaration::Defn(definition) = declaration else {
                        continue;
                    };
                    let status = if record.parent_instances.contains(&definition.base.name) {
                        fln_elab::reducibility::Reducibility::ImplicitReducible
                    } else if record.is_class
                        || record
                            .defaults
                            .iter()
                            .any(|default| default.helper == definition.base.name)
                    {
                        fln_elab::reducibility::Reducibility::Semireducible
                    } else {
                        fln_elab::reducibility::Reducibility::Reducible
                    };
                    batch.engine.environment = fln_elab::reducibility::register(
                        batch.engine.environment(),
                        &definition.base.name,
                        status,
                    )
                    .map_err(|error| {
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::Unification(Box::new(
                                    fln_elab::constraint::unify::UnificationError::Reducibility(
                                        error,
                                    ),
                                )),
                            ),
                        ))
                    })?;
                }
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
        };
        self.finish_source_deriving(result, deriving.as_ref(), options, limits, scope)
    }

    fn finish_source_deriving(
        &self,
        result: Outcome<DeclarationBatchAdmission>,
        request: Option<&fln_elab::source::deriving::DerivingRequest>,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let Some(request) = request.filter(|request| !request.handlers.is_empty()) else {
            return Ok(result);
        };
        let mut batch = match result {
            Outcome::Complete(batch) => batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let frontend = |reason| {
            EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                fln_elab::NatDefinitionElabError::Inference(reason),
            ))
        };
        let type_name = scope
            .declaration_name(&request.type_name)
            .map_err(|error| frontend(fln_elab::source::SourceInferenceError::NameScope(error)))?;
        for handler in &request.handlers {
            let derived = match elaboration_outcome(fln_elab::source::deriving::elaborate_handler(
                handler,
                &type_name,
                request.is_record,
                batch.engine.environment(),
                limits.kernel,
                scope,
            ))? {
                Outcome::Complete(derived) => derived,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            let mut successor = match batch
                .engine
                .admit_declarations(&derived.declarations, options, limits)
                .map_err(EngineExecutionError::from)?
            {
                Outcome::Complete(successor) => successor,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            successor.engine.environment = fln_elab::instances::register_instance(
                successor.engine.environment(),
                &derived.instance,
                1000,
            )
            .map_err(|error| {
                frontend(fln_elab::source::SourceInferenceError::InstanceRegistry(
                    error,
                ))
            })?;
            successor.engine.environment = fln_elab::reducibility::register(
                successor.engine.environment(),
                &derived.instance,
                fln_elab::reducibility::Reducibility::ImplicitReducible,
            )
            .map_err(|error| {
                frontend(fln_elab::source::SourceInferenceError::Unification(
                    Box::new(fln_elab::constraint::unify::UnificationError::Reducibility(
                        error,
                    )),
                ))
            })?;
            // Include every checked helper and dictionary in the ordinary
            // admission stream. Module export/replay must see the whole command.
            batch.admissions.extend(successor.admissions);
            batch.engine = successor.engine;
            batch.result_logical_root = batch.engine.logical_root(options);
        }
        Ok(Outcome::Complete(batch))
    }
}

/// The syntax of one command on the checked source path.
pub(crate) enum ScopedCommandSyntax {
    /// A complete `mutual` group (or a lone inductive inside one).
    Mutual(Vec<fln_syntax::tree::Syntax>),
    /// An `example`, checked and discarded.
    Example(fln_parse::ParsedSourceCommand),
    /// Every other declaration command.
    Definition(fln_parse::ParsedDefinition),
}

/// Parse one command exactly as [`Engine::admit_source_command_in_scope`] does,
/// consulting the parsers in the same order. Every parser here reads only the
/// command's bytes, which is what lets [`crate::source_check::preflight_source_files`]
/// run this before any environment exists.
pub(crate) fn parse_scoped_command(
    source: &[u8],
) -> Result<ScopedCommandSyntax, EngineExecutionError> {
    if let Some(members) = fln_parse::command_scope::mutual::parse(source)
        .map_err(DefinitionFrontendError::Parse)
        .map_err(EngineExecutionError::Frontend)?
    {
        return Ok(ScopedCommandSyntax::Mutual(members));
    }
    let parsed = fln_parse::parse_definition(source)
        .map_err(DefinitionFrontendError::Parse)
        .map_err(EngineExecutionError::Frontend)?;
    if fln_elab::source::scope::is_example(parsed.syntax()) {
        let parsed = fln_parse::parse_source_command(source)
            .map_err(DefinitionFrontendError::Parse)
            .map_err(EngineExecutionError::Frontend)?;
        return Ok(ScopedCommandSyntax::Example(parsed));
    }
    Ok(ScopedCommandSyntax::Definition(parsed))
}

/// Tag an admitted `protected` declaration in the protected-declaration journal,
/// after the council admitted it, so later commands (and this module's olean)
/// see it as the pin's `addProtected` leaves it. A refusal is the command's.
pub(crate) fn tag_protected(
    engine: &Engine,
    name: &Name,
) -> Result<Environment, EngineExecutionError> {
    fln_elab::protected_names::register_module(engine.environment(), std::slice::from_ref(name))
        .map_err(|error| {
            EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                fln_elab::NatDefinitionElabError::Inference(
                    fln_elab::source::SourceInferenceError::ProtectedJournal(error),
                ),
            ))
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::MVarId;
    use fln_core::outcome::{Inconclusive, InternalFault};
    use fln_elab::NatDefinitionElabError;
    use fln_elab::constraint::{ConstraintId, unify::UnificationError};
    use fln_elab::source::SourceInferenceError;
    use fln_kernel::verdict::{Consumption, RejectClass, Verdict};

    #[test]
    fn kernel_carriers_preserve_nonanswers_and_never_turn_verdict_errors_into_values() {
        // Adapter coverage, including a planted internal fault and the currently
        // unobserved source ConstraintCheck carrier; not live kernel-fault proof.
        for outcome in [
            Outcome::Inconclusive(Inconclusive::cancelled("kernel probe").with_progress("term")),
            Outcome::InternalFault(
                InternalFault::new("FL-INV-07", "probe").with_evidence("adapter test"),
            ),
            Outcome::Complete(Verdict::Rejected {
                class: RejectClass::TypeMismatch,
                message: "probe".into(),
                consumption: Consumption::default(),
            }),
            Outcome::Complete(Verdict::Accepted {
                consumption: Consumption::default(),
            }),
        ] {
            for inference in [
                SourceInferenceError::TypeObligation(Box::new(outcome.clone())),
                SourceInferenceError::Unification(Box::new(UnificationError::AssignmentCheck {
                    id: MVarId(Name::from_components(["probe"])),
                    outcome: Box::new(outcome.clone()),
                })),
                SourceInferenceError::Unification(Box::new(UnificationError::ConversionCheck {
                    outcome: Box::new(outcome.clone()),
                })),
                SourceInferenceError::Unification(Box::new(UnificationError::ConstraintCheck {
                    id: ConstraintId(0),
                    outcome: Box::new(outcome.clone()),
                })),
            ] {
                let error = NatDefinitionElabError::Inference(inference);
                let result = elaboration_outcome::<()>(Err(error.clone()));
                match &outcome {
                    Outcome::Inconclusive(reason) => assert!(
                        matches!(result, Ok(Outcome::Inconclusive(ref actual)) if actual == reason)
                    ),
                    Outcome::InternalFault(fault) => assert!(
                        matches!(result, Ok(Outcome::InternalFault(ref actual)) if actual == fault)
                    ),
                    Outcome::Complete(_) => assert!(
                        matches!(result, Err(EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(ref actual))) if actual == &error)
                    ),
                }
            }
        }
        let ordinary = NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit);
        assert!(
            matches!(elaboration_outcome::<()>(Err(ordinary.clone())), Err(EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(actual))) if actual == ordinary)
        );
        assert!(matches!(
            elaboration_outcome(Ok(17)),
            Ok(Outcome::Complete(17))
        ));
    }
}
