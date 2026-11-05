//! Proof-valued deriving keeps the checked implementation in the full world
//! and exposes only the signature obtained from that successful admission.
use super::*;
use crate::source_records::elaboration_outcome;
use fln_elab::source::deriving::{DerivingTarget, ExistingDeriving};
use fln_elab::source::scope::SourceScope;
use fln_env::constants::AxiomVal;

pub(super) struct Plan {
    base: Option<fln_parse::ParsedDefinition>,
    request: ExistingDeriving,
    proofs: Vec<bool>,
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
    let mut proofs = Vec::new();
    for handler in &request.handlers {
        let proof = match elaboration_outcome(fln_elab::source::deriving::is_proof_handler(
            handler,
            private.environment(),
            limits.kernel,
            private_scope,
        ))? {
            Outcome::Complete(proof) => proof,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        proofs.push(proof);
    }
    if !proofs.iter().any(|proof| *proof) {
        return Ok(Outcome::Complete(None));
    }
    request.scope = public_scope.clone();
    Ok(Outcome::Complete(Some(Plan {
        base,
        request,
        proofs,
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
        let mut proof_scope = private_scope.clone();
        proof_scope.public_declarations = true;
        if plan.base.is_some() {
            proof_scope.expose_definitions = public_scope.expose_definitions;
        }
        if let Some(base) = plan.base {
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
        for (handler, proof) in plan.request.handlers.iter().zip(plan.proofs) {
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
                let request = ExistingDeriving {
                    handlers: vec![handler.clone()],
                    targets: vec![target.clone()],
                    scope: if proof {
                        proof_scope.clone()
                    } else {
                        public_scope.clone()
                    },
                };
                let outcome = if proof {
                    self.stage_derived_proof(&mut staged, &request, options, limits)?
                } else {
                    let checked = match staged.public.admit_existing_deriving(
                        &request,
                        Some(staged.private.environment()),
                        options,
                        limits,
                    )? {
                        Outcome::Complete(checked) => checked,
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    };
                    self.stage_derived_data(&mut staged, checked, options, limits)?
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
}
