//! Checked structure candidates and paired public/private member publication.
use super::*;
use fln_elab::source::{SourceRecord, scope::SourceScope};
use std::sync::Arc;

fn frontend(reason: fln_elab::source::SourceInferenceError) -> EngineExecutionError {
    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
        fln_elab::NatDefinitionElabError::Inference(reason),
    ))
}

/// Copy only the checked command's exact journal suffix. The source and target
/// may have different private histories; no predecessor row is replayed. The
/// caller has already admitted the command's complete declarations in both
/// worlds. A public projection additionally removes entries whose executable
/// declaration or proof is absent there.
fn record_metadata(
    base: &Environment,
    checked: &Environment,
    mut target: Environment,
    public: bool,
) -> Result<Environment, EngineExecutionError> {
    use fln_elab::source::{SourceInferenceError, scope::simp};
    let mut remaining = fln_elab::records::RecordBudget::default().max_nodes;
    let mut charge = |work: usize| {
        remaining = remaining
            .checked_sub(work)
            .ok_or_else(|| frontend(SourceInferenceError::ResourceLimit))?;
        Ok::<(), EngineExecutionError>(())
    };
    for (name, state) in checked.extensions() {
        charge(1)?;
        let prior = base.extension(name);
        if prior.is_some_and(|prior| std::ptr::eq(prior, state)) {
            continue;
        }
        if prior
            .is_some_and(|prior| prior.descriptor != state.descriptor || prior.len() > state.len())
        {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "a checked record must preserve its predecessor journals",
            });
        }
        let mut entries = state.entries();
        if let Some(prior) = prior {
            for old in prior.entries() {
                charge(1)?;
                let Some(next) = entries.next() else {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "a checked record shortened a predecessor journal",
                    });
                };
                if !Arc::ptr_eq(&old.payload, &next.payload) {
                    charge(old.payload.len().saturating_add(next.payload.len()))?;
                    if old != next {
                        return Err(EngineExecutionError::UnexpectedPublication {
                            detail: "a checked record changed a predecessor journal entry",
                        });
                    }
                }
            }
        }
        // Reducibility's wire exporter requires each row's declaration to be
        // visible. Rebuild its checked suffix below, retaining only such rows.
        if public && fln_elab::reducibility::export::supports(&state.descriptor) {
            continue;
        }
        for entry in entries {
            charge(1usize.saturating_add(entry.payload.len()))?;
            if public
                && simp::export::supports(&state.descriptor)
                && !simp::export::source_entry_visible(&target, &entry.payload)
                    .map_err(|error| frontend(SourceInferenceError::SimpSet(error)))?
            {
                continue;
            }
            match target.extension(name) {
                Some(existing) if existing.descriptor != state.descriptor => {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "a record journal conflicts with its destination world",
                    });
                }
                Some(_) => {}
                None => {
                    target = target
                        .register_extension(state.descriptor.clone())
                        .map_err(|_| EngineExecutionError::UnexpectedPublication {
                            detail: "a checked record journal could not be registered",
                        })?;
                }
            }
            target = target
                .push_extension_entry(name, Arc::clone(&entry.payload))
                .map_err(|_| EngineExecutionError::UnexpectedPublication {
                    detail: "a checked record journal suffix could not be replayed",
                })?;
        }
    }
    if public {
        let statuses = fln_elab::reducibility::export::statuses(base, checked, remaining).map_err(
            |error| {
                frontend(SourceInferenceError::Unification(Box::new(
                    fln_elab::constraint::unify::UnificationError::Reducibility(error),
                )))
            },
        )?;
        for row in statuses.imported.into_iter().chain(statuses.owned) {
            if target.contains(&row.declaration) {
                target = fln_elab::reducibility::register(&target, &row.declaration, row.status)
                    .map_err(|error| {
                        frontend(SourceInferenceError::Unification(Box::new(
                            fln_elab::constraint::unify::UnificationError::Reducibility(error),
                        )))
                    })?;
            }
        }
        for name in statuses.default_semireducible {
            if target.contains(&name) {
                target =
                    fln_elab::reducibility::register_default(&target, &name).map_err(|error| {
                        frontend(SourceInferenceError::Unification(Box::new(
                            fln_elab::constraint::unify::UnificationError::Reducibility(error),
                        )))
                    })?;
            }
        }
    }
    Ok(target)
}

impl Engine {
    /// A modern public structure keeps its checked private-named constructor
    /// in the kernel family, while private projections and helpers remain in
    /// its implementation world. Generated eliminator wrappers have public
    /// signatures whose bodies are retained only by the private world.
    pub(super) fn admit_public_source_record(
        &self,
        public: &Engine,
        syntax: &fln_syntax::tree::Syntax,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        public_scope: &SourceScope,
    ) -> Result<Outcome<PublicSourceAdmission>, EngineExecutionError> {
        let deriving = match elaboration_outcome(fln_elab::source::deriving::prepare(syntax))? {
            Outcome::Complete(deriving) => deriving,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let syntax = deriving.as_ref().map_or(syntax, |request| &request.syntax);
        // Public fields, parameters and ordinary defaults must not resolve
        // against private predecessor declarations. Private-field dependencies
        // requiring exported type sanitization remain an explicit capability
        // boundary; elaborating the whole family privately would leak them.
        let record =
            match elaboration_outcome(fln_elab::source::elaborate_record_with_private_names(
                syntax,
                public.environment(),
                self.environment(),
                limits.kernel,
                fln_elab::records::RecordBudget::default(),
                public_scope,
            ))? {
                Outcome::Complete(record) => record,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        let has_private_members = !record.private_members.is_empty();
        let family = record.name.clone();
        let default_helpers = record.default_helpers.clone();
        let candidate =
            public.admit_prepared_source_record(syntax, record, options, limits, public_scope)?;
        if !has_private_members {
            return Ok(
                match public.finish_source_deriving(
                    candidate,
                    deriving.as_ref(),
                    options,
                    limits,
                    public_scope,
                )? {
                    Outcome::Complete(public) => Outcome::Complete(PublicSourceAdmission {
                        public,
                        private_implementation: None,
                        metadata_complete: false,
                    }),
                    Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                },
            );
        }
        if deriving
            .as_ref()
            .is_some_and(|request| !request.handlers.is_empty())
        {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "private-member record derivation requires the paired module handler plan",
            });
        }
        let candidate = match candidate {
            Outcome::Complete(candidate) => candidate,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let private_ctor = matches!(candidate.engine.environment().find(&family),
            Some(ConstantInfo::Induct(inductive))
                if inductive.ctors.iter().any(SourceScope::is_private_name));
        let hidden_wrappers: BTreeSet<_> = ["recOn", "casesOn", "noConfusionType", "noConfusion"]
            .into_iter()
            .map(|suffix| Name::str(family.clone(), suffix))
            .chain(default_helpers)
            .collect();
        let complete: Vec<_> = candidate
            .admissions
            .iter()
            .map(|admitted| admitted.declaration.clone())
            .collect();
        let mut interfaces = Vec::with_capacity(complete.len());
        for declaration in &complete {
            let base = match declaration {
                Declaration::Defn(definition) => Some(&definition.base),
                Declaration::Thm(theorem) => Some(&theorem.base),
                Declaration::Axiom(axiom) => Some(&axiom.base),
                _ => None,
            };
            if base.is_some_and(|base| SourceScope::is_private_name(&base.name)) {
                continue;
            }
            let exposed = if private_ctor
                && base.is_some_and(|base| hidden_wrappers.contains(&base.name))
            {
                let Declaration::Defn(definition) = declaration else {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "a record eliminator interface must originate in a checked definition",
                    });
                };
                if definition.safety != DefinitionSafety::Safe {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "a private-constructor record requires safe eliminator implementations",
                    });
                }
                Declaration::Axiom(AxiomVal {
                    base: definition.base.clone(),
                    is_unsafe: false,
                })
            } else {
                declaration.clone()
            };
            interfaces.push(exposed);
        }
        // Recheck the exact complete batch against the real private predecessor.
        // The transient public-base check above grants no publication authority.
        let mut private = match self.admit_declarations(&complete, options, limits)? {
            Outcome::Complete(private) => private,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        private.engine.environment = record_metadata(
            public.environment(),
            candidate.engine.environment(),
            private.engine.environment,
            false,
        )?;
        private.result_logical_root = private.engine.logical_root(options);
        let mut projected = match public.admit_declarations(&interfaces, options, limits)? {
            Outcome::Complete(projected) => projected,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        projected.engine.environment = record_metadata(
            public.environment(),
            candidate.engine.environment(),
            projected.engine.environment,
            true,
        )?
        .with_imported_metadata_validation(private.engine.environment());
        projected.result_logical_root = projected.engine.logical_root(options);
        Ok(Outcome::Complete(PublicSourceAdmission {
            public: projected,
            private_implementation: Some(private),
            metadata_complete: true,
        }))
    }

    /// Classify projections against their exact predecessor, then check the
    /// complete generated family and journals before exposing any successor.
    pub(super) fn admit_prepared_source_record(
        &self,
        syntax: &fln_syntax::tree::Syntax,
        mut record: SourceRecord,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &SourceScope,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let mut result = self
            .admit_declarations(&record.declarations, options, limits)
            .map_err(EngineExecutionError::from)?;
        if let Outcome::Complete(batch) = &result {
            // The pin emits proof projections as theorems, not definitions
            // (Lean/Meta/Structure.lean:99–116). Ask K1 under its supplied budget
            // against each projection's exact, already checked predecessor;
            // the actual declaration name is still fresh in that environment.
            // Defaults and flat constructors remain ordinary definitions even
            // when they return proofs; consumers must instantiate their bodies.
            let mut predecessor = self;
            let mut proof_projection = false;
            for (index, admission) in batch.admissions.iter().enumerate() {
                if let Declaration::Defn(definition) = &admission.declaration
                    && definition.base.name != record.flat_constructor
                    && !record.default_helpers.contains(&definition.base.name)
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
        // Complete the declaration stream before adding any record journals,
        // so adjacent council receipts retain their exact predecessor roots.
        let result = self.finish_source_inductive_auxiliaries(
            result,
            options,
            limits,
            scope,
            record.is_class,
        )?;
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
                    } else if definition.base.name == record.flat_constructor {
                        fln_elab::reducibility::Reducibility::Reducible
                    } else if record.is_class
                        || record.default_helpers.contains(&definition.base.name)
                    {
                        fln_elab::reducibility::Reducibility::Semireducible
                    } else {
                        fln_elab::reducibility::Reducibility::Reducible
                    };
                    let registered =
                        if status == fln_elab::reducibility::Reducibility::Semireducible {
                            fln_elab::reducibility::register_default(
                                batch.engine.environment(),
                                &definition.base.name,
                            )
                        } else {
                            fln_elab::reducibility::register(
                                batch.engine.environment(),
                                &definition.base.name,
                                status,
                            )
                        };
                    batch.engine.environment = registered.map_err(|error| {
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
                batch.engine.environment = fln_elab::records::imported::register(
                    batch.engine.environment(),
                    std::slice::from_ref(&record.structure),
                )
                .map_err(|error| {
                    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                        fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::Record(error),
                        ),
                    ))
                })?;
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
                    batch.engine = match batch.engine.register_checked_source_instance(
                        parent,
                        1000,
                        None,
                        false,
                        limits.kernel,
                    )? {
                        Outcome::Complete(engine) => engine,
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    };
                }
                if !record.protected_projections.is_empty() {
                    batch.engine.environment = fln_elab::protected_names::register_module(
                        batch.engine.environment(),
                        &record.protected_projections,
                    )
                    .map_err(|error| {
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::ProtectedJournal(error),
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
        let result = self.finish_source_data_attributes(
            result,
            std::slice::from_ref(syntax),
            options,
            scope,
        )?;
        Ok(result)
    }
}
