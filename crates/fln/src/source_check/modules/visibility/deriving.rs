//! Derived proofs and hidden helpers retain their checked implementations in
//! the full world. Only independently checked interfaces enter public replay.
use super::*;
use crate::source_records::elaboration_outcome;
use fln_elab::source::deriving::{DerivingTarget, ExistingDeriving, HandlerPublication};
use fln_elab::source::scope::SourceScope;
use fln_env::constants::AxiomVal;

pub(super) struct Plan {
    base: Option<fln_parse::ParsedDefinition>,
    request: ExistingDeriving,
    publications: Vec<HandlerPublication>,
}

pub(super) fn prepare(
    parsed: &ScopedCommandSyntax,
    private: &Engine,
    limits: EngineAdmissionLimits,
    scopes: (&SourceScope, &SourceScope),
) -> Result<Outcome<Option<Plan>>, EngineExecutionError> {
    let (public_scope, private_scope) = scopes;
    let (base, mut request) = match parsed {
        ScopedCommandSyntax::Deriving(syntax) => {
            let request = match elaboration_outcome(fln_elab::source::deriving::prepare_existing(
                syntax,
                private.environment(),
                limits.kernel,
                private_scope,
            ))? {
                Outcome::Complete(request) => request,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            if !request.scope.public_declarations {
                return Err(EngineExecutionError::UnexpectedPublication {
                    detail: "a private deriving group entered public publication",
                });
            }
            (None, request)
        }
        ScopedCommandSyntax::Definition(parsed) => {
            let request =
                match elaboration_outcome(fln_elab::source::deriving::prepare(parsed.syntax()))? {
                    Outcome::Complete(Some(request)) if !request.handlers.is_empty() => request,
                    Outcome::Complete(_) => return Ok(Outcome::Complete(None)),
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
            let name = public_scope
                .declaration_name(&request.type_name)
                .map_err(|error| {
                    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                        fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::NameScope(error),
                        ),
                    ))
                })?;
            let base = parsed.clone().with_expanded_syntax(request.syntax).ok_or(
                EngineExecutionError::UnexpectedPublication {
                    detail: "a deriving suffix must retain its named family declaration",
                },
            )?;
            (
                Some(base),
                ExistingDeriving {
                    handlers: request.handlers,
                    targets: vec![DerivingTarget {
                        name,
                        is_record: request.is_record,
                    }],
                    scope: public_scope.clone(),
                },
            )
        }
        _ => return Ok(Outcome::Complete(None)),
    };
    let mut publications = Vec::new();
    for handler in &request.handlers {
        let publication =
            match elaboration_outcome(fln_elab::source::deriving::handler_publication(
                handler,
                private.environment(),
                limits.kernel,
                private_scope,
            ))? {
                Outcome::Complete(publication) => publication,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        publications.push(publication);
    }
    if publications
        .iter()
        .all(|publication| *publication == HandlerPublication::Exposed)
        && !base
            .as_ref()
            .is_some_and(|base| fln_elab::source::is_record(base.syntax()))
        // A standalone deriving command has no base syntax to classify. Keep
        // it in paired publication when an existing target has a private
        // constructor, so it cannot bypass the handler's visibility policy.
        && !request.targets.iter().any(|target| {
            matches!(private.environment().find(&target.name),
                Some(ConstantInfo::Induct(family))
                    if family.ctors.iter().any(SourceScope::is_private_name))
        })
    {
        return Ok(Outcome::Complete(None));
    }
    request.scope = public_scope.clone();
    Ok(Outcome::Complete(Some(Plan {
        base,
        request,
        publications,
    })))
}

struct Staged {
    public: Engine,
    private: Engine,
    admissions: Vec<crate::DeclarationAdmission>,
    declarations: Vec<Declaration>,
}

impl PublicWorld<'_> {
    /// Work only on persistent successors until the entire family and all its
    /// handlers pass. A later failure publishes neither world nor its metadata.
    pub(super) fn admit_deriving_plan(
        &mut self,
        source: &[u8],
        plan: Plan,
        equations: StagedPublicEquations,
        original_private: &Engine,
        checking: (&KVMap, EngineAdmissionLimits),
        scopes: (&SourceScope, &SourceScope),
    ) -> Result<Outcome<(Engine, DeclarationBatchAdmission)>, EngineExecutionError> {
        let (options, limits) = checking;
        let (public_scope, private_scope) = scopes;
        let mut staged = Staged {
            public: equations.public,
            private: equations.private,
            admissions: equations.admissions,
            declarations: equations.declarations,
        };
        let mut body_scope = private_scope.clone();
        body_scope.public_declarations = true;
        if plan.base.is_some() {
            body_scope.expose_definitions = public_scope.expose_definitions;
        }
        if let Some(base) = plan.base {
            if fln_elab::source::is_record(base.syntax()) {
                let checked = match staged.private.admit_public_scoped_command_syntax(
                    &staged.public,
                    source,
                    ScopedCommandSyntax::Definition(base),
                    options,
                    limits,
                    public_scope,
                    private_scope,
                )? {
                    Outcome::Complete(checked) => checked,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                if let Some(private) = checked.private_implementation {
                    if !checked.metadata_complete {
                        return Err(EngineExecutionError::UnexpectedPublication {
                            detail: "a paired record base must finish both metadata worlds before deriving",
                        });
                    }
                    self.meter
                        .work(checked.public.admissions.len())
                        .map_err(execution_error)?;
                    staged.declarations.extend(
                        checked
                            .public
                            .admissions
                            .into_iter()
                            .map(|admitted| admitted.declaration),
                    );
                    staged.public = checked.public.engine;
                    staged.private = private.engine;
                    staged.admissions.extend(private.admissions);
                } else {
                    match self.stage_derived_data(&mut staged, checked.public, options, limits)? {
                        Outcome::Complete(()) => {}
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    }
                }
            } else {
                let checked = match staged.public.admit_scoped_command_syntax_with_base(
                    source,
                    ScopedCommandSyntax::Definition(base),
                    options,
                    limits,
                    public_scope,
                    Some(&self.initial),
                )? {
                    Outcome::Complete(checked) => checked,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                match self.stage_derived_data(&mut staged, checked, options, limits)? {
                    Outcome::Complete(()) => {}
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                }
            }
        }
        for (handler, publication) in plan.request.handlers.iter().zip(plan.publications) {
            for target in &plan.request.targets {
                self.meter.work(1).map_err(execution_error)?;
                if self
                    .cancellation
                    .is_some_and(CancellationProbe::is_cancelled)
                {
                    return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                        "source-module/deriving",
                    )));
                }
                let Some(ConstantInfo::Induct(family)) =
                    staged.private.environment().find(&target.name)
                else {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "derivation requires its admitted inductive target",
                    });
                };
                let has_private_constructor = family.ctors.iter().any(SourceScope::is_private_name);
                if has_private_constructor
                    && publication == HandlerPublication::Inhabited
                    && family.ctors.len() != 1
                {
                    return Err(EngineExecutionError::NotImplemented {
                        feature: "paired Inhabited derivation over mixed private constructor alternatives",
                    });
                }
                if has_private_constructor && publication == HandlerPublication::Exposed {
                    return Err(EngineExecutionError::NotImplemented {
                        feature: "paired public deriving helpers for this private-constructor handler",
                    });
                }
                let exposed = publication == HandlerPublication::Exposed
                    || publication == HandlerPublication::Inhabited && !has_private_constructor;
                let mut selected_scope = if exposed {
                    public_scope.clone()
                } else {
                    body_scope.clone()
                };
                if has_private_constructor && publication == HandlerPublication::Inhabited {
                    // withoutExposeFromCtors removes inherited section exposure
                    // for the private default implementation; its dictionary
                    // still passes an independent ordinary public admission.
                    selected_scope.expose_definitions = false;
                }
                let request = ExistingDeriving {
                    handlers: vec![handler.clone()],
                    targets: vec![target.clone()],
                    scope: selected_scope,
                };
                let outcome = match publication {
                    HandlerPublication::Proof => {
                        self.stage_derived_proof(&mut staged, &request, options, limits)?
                    }
                    HandlerPublication::HiddenHashHelper => self.stage_derived_hidden_helper(
                        &mut staged,
                        &request,
                        "hash",
                        options,
                        limits,
                    )?,
                    HandlerPublication::Inhabited if has_private_constructor => self
                        .stage_derived_hidden_helper(
                            &mut staged,
                            &request,
                            "default",
                            options,
                            limits,
                        )?,
                    HandlerPublication::Exposed | HandlerPublication::Inhabited => {
                        let checked = match staged.public.admit_existing_deriving(
                            &request,
                            Some(staged.private.environment()),
                            options,
                            limits,
                        )? {
                            Outcome::Complete(checked) => checked,
                            Outcome::Inconclusive(reason) => {
                                return Ok(Outcome::Inconclusive(reason));
                            }
                            Outcome::InternalFault(fault) => {
                                return Ok(Outcome::InternalFault(fault));
                            }
                        };
                        self.stage_derived_data(&mut staged, checked, options, limits)?
                    }
                };
                match outcome {
                    Outcome::Complete(()) => {}
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                }
            }
        }
        match self.check_new_names(original_private, &staged.public, public_scope)? {
            Outcome::Complete(()) => {}
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        }
        if self
            .cancellation
            .is_some_and(CancellationProbe::is_cancelled)
        {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-module/deriving-publication",
            )));
        }
        let batch = DeclarationBatchAdmission {
            engine: staged.private.clone(),
            base_logical_root: original_private.logical_root(options),
            result_logical_root: staged.private.logical_root(options),
            admissions: staged.admissions,
            local_instance: None,
            local_symm: Vec::new(),
        };
        self.engine = staged.public;
        self.declarations.extend(staged.declarations);
        Ok(Outcome::Complete((staged.private, batch)))
    }

    fn stage_derived_data(
        &mut self,
        staged: &mut Staged,
        checked: DeclarationBatchAdmission,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<()>, EngineExecutionError> {
        let declarations: Vec<_> = checked
            .admissions
            .iter()
            .map(|admission| admission.declaration.clone())
            .collect();
        self.meter
            .work(declarations.len())
            .map_err(execution_error)?;
        let private = match staged
            .private
            .admit_declarations(&declarations, options, limits)
            .map_err(EngineExecutionError::from)?
        {
            Outcome::Complete(private) => private,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // Replay only this checked public step's journal suffix, retaining the
        // private world's earlier instance order and private declarations.
        let metadata = replay::Export::capture(
            &self.module,
            staged.public.environment(),
            checked.engine.environment(),
            Vec::new(),
            self.meter,
        )
        .map_err(execution_error)?;
        let next = match metadata
            .replay(
                private.engine,
                &self.module,
                options,
                self.meter,
                self.cancellation,
            )
            .map_err(execution_error)?
        {
            Outcome::Complete(next) => next,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        staged.private = next;
        staged.public = checked.engine;
        staged.admissions.extend(private.admissions);
        staged.declarations.extend(declarations);
        Ok(Outcome::Complete(()))
    }

    fn stage_derived_proof(
        &mut self,
        staged: &mut Staged,
        request: &ExistingDeriving,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<()>, EngineExecutionError> {
        let checked = match staged
            .private
            .admit_existing_deriving(request, None, options, limits)?
        {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let [admitted] = checked.admissions.as_slice() else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "a proof deriving handler must admit one complete theorem",
            });
        };
        let Declaration::Thm(theorem) = &admitted.declaration else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "a proof deriving handler must retain its checked theorem kind",
            });
        };
        // This is the header of the actual council-admitted proof, not a
        // caller-supplied axiom. Its independent public check rejects a private
        // dependency in the interface before either world becomes observable.
        let name = theorem.base.name.clone();
        let interface = Declaration::Axiom(AxiomVal {
            base: theorem.base.clone(),
            is_unsafe: false,
        });
        let public = match staged
            .public
            .admit_declaration(interface.clone(), options, limits)
            .map_err(EngineExecutionError::from)?
        {
            Outcome::Complete(public) => public,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let next = match public.engine.register_checked_source_instance(
            &name,
            1000,
            None,
            false,
            limits.kernel,
        )? {
            Outcome::Complete(next) => next,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        staged.public = next;
        staged.private = checked.engine;
        staged.admissions.extend(checked.admissions);
        staged.declarations.push(interface);
        Ok(Outcome::Complete(()))
    }

    fn stage_derived_hidden_helper(
        &mut self,
        staged: &mut Staged,
        request: &ExistingDeriving,
        helper_suffix: &str,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<()>, EngineExecutionError> {
        // Hashable always hides its hash implementation. Inhabited does the
        // same for a private constructor's default. The public dictionary only
        // names that checked helper and must pass both public checking seats.
        let checked = match staged
            .private
            .admit_existing_deriving(request, None, options, limits)?
        {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let [helper, dictionary] = checked.admissions.as_slice() else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "hidden-helper deriving must admit its complete helper and dictionary",
            });
        };
        let (Declaration::Defn(helper), Declaration::Defn(dictionary)) =
            (&helper.declaration, &dictionary.declaration)
        else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "hidden-helper deriving must retain its checked definition kinds",
            });
        };
        if helper.safety != DefinitionSafety::Safe
            || dictionary.safety != DefinitionSafety::Safe
            || helper.base.name != Name::str(dictionary.base.name.clone(), helper_suffix)
        {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "hidden-helper deriving requires its actual safe auxiliary definition",
            });
        }
        let name = dictionary.base.name.clone();
        // Build an interface only from the successful helper admission. Its
        // public check rejects any private dependency in the generated header.
        let interface = Declaration::Axiom(AxiomVal {
            base: helper.base.clone(),
            is_unsafe: false,
        });
        let declarations = [interface, Declaration::Defn(dictionary.clone())];
        self.meter
            .work(declarations.len())
            .map_err(execution_error)?;
        let public = match staged
            .public
            .admit_declarations(&declarations, options, limits)
            .map_err(EngineExecutionError::from)?
        {
            Outcome::Complete(public) => public,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let next = match public.engine.register_checked_source_instance(
            &name,
            1000,
            None,
            false,
            limits.kernel,
        )? {
            Outcome::Complete(next) => next,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // Each world registered its own checked instance exactly once. No
        // replay of the public metadata may duplicate the private journal.
        staged.public = next;
        staged.private = checked.engine;
        staged.admissions.extend(checked.admissions);
        staged.declarations.extend(declarations);
        Ok(Outcome::Complete(()))
    }
}
