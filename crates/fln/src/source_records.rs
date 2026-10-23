//! One source command may expand to multiple mutually dependent declarations.
//! Preserve the ordinary per-declaration evidence and publish only a full batch.
use super::*;
use fln_kernel::verdict::Verdict;

mod auxiliaries;
mod elaboration;
mod library;
mod local_functions;
mod public_body;
pub(crate) mod traces;
pub use local_functions::SourceDeclarationAdmission;

pub(crate) use elaboration::{
    apply_admission_effects, apply_batch_effects, apply_execution_effects,
};

/// A candidate publication held off to the side until both module worlds and
/// their extension journals are ready. Only the public module driver consumes it.
pub(crate) struct PublicSourceAdmission {
    pub(crate) public: DeclarationBatchAdmission,
    pub(crate) private_implementation: Option<DeclarationBatchAdmission>,
}

/// Classify a closed declaration header without changing its declaration kind
/// or granting publication authority. Publication of the complete declaration
/// or its metadata still requires ordinary admission by both checkers.
pub(super) fn declaration_is_proposition(
    environment: &Environment,
    base: &ConstantVal,
    kernel: Budget,
) -> Result<Outcome<bool>, EngineExecutionError> {
    let opaque_definitions = BTreeSet::new();
    let outcome = fln_kernel::check_type_with_unfolding(
        environment,
        &base.level_params,
        &base.type_,
        &Expr::sort(Level::zero()),
        kernel,
        fln_kernel::DefEqUnfolding {
            opaque_definitions: &opaque_definitions,
            unfold_theorems: true,
        },
    );
    match outcome {
        Outcome::Complete(Verdict::Accepted { .. }) => Ok(Outcome::Complete(true)),
        Outcome::Complete(Verdict::Rejected {
            class: RejectClass::NotDefEq,
            ..
        }) => Ok(Outcome::Complete(false)),
        Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
        Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
        other => Err(EngineExecutionError::Frontend(
            DefinitionFrontendError::Elaborate(fln_elab::NatDefinitionElabError::Inference(
                fln_elab::source::SourceInferenceError::TypeObligation(Box::new(other)),
            )),
        )),
    }
}

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
    if let NatDefinitionElabError::Inference(
        SourceInferenceError::ArithmeticInconclusive(reason)
        | SourceInferenceError::NativeEvaluationInconclusive(reason),
    ) = &error
    {
        return Ok(Outcome::Inconclusive((**reason).clone()));
    }
    if let NatDefinitionElabError::Inference(SourceInferenceError::NativeEvaluation(
        fln_elab::native::NativeEvaluationError::Fault(fault),
    )) = &error
    {
        return Ok(Outcome::InternalFault(fault.clone()));
    }
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
        library::append_lemmas(engine, limits)
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
    fn admit_partial_result(
        &self,
        partial: &fln_elab::source::partial::ElaboratedPartial,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let mut batch = match self.admit_declarations(partial.declarations(), options, limits)? {
            Outcome::Complete(batch) => batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // The private successor has already passed both checkers in its entirety.
        // Failed dependency analysis or metadata publication drops it wholesale.
        match elaboration_outcome(partial.record_codegen(batch.engine.environment()))? {
            Outcome::Complete(environment) => {
                batch.engine.environment = environment;
                // Mutual well-founded members are `@[irreducible]` at the pin
                // (`addPreDefAttributes`); their `_mutual` auxiliary is not.
                for name in partial.irreducible() {
                    let Some(declaration) = partial.declarations().iter().find(|declaration| {
                        matches!(declaration, Declaration::Defn(definition) if &definition.base.name == name)
                    }) else {
                        return Err(EngineExecutionError::UnexpectedPublication {
                            detail: "an irreducible mutual member must be an admitted definition",
                        });
                    };
                    elaboration::register_irreducible(&mut batch.engine, declaration)?;
                }
                batch.result_logical_root = batch.engine.logical_root(options);
                Ok(Outcome::Complete(batch))
            }
            Outcome::Inconclusive(reason) => Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => Ok(Outcome::InternalFault(fault)),
        }
    }

    /// Build the native source environment with the staged coercion library.
    /// Every class, eliminator, projection and composition instance passes both
    /// checking engines before any of its registrations become observable.
    pub fn with_coercion_seed(
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<Self>, EngineAdmissionError> {
        Self::builder().build_with_coercion_seed(limits)
    }

    /// Admit one definition, theorem, instance, structure, class or inductive command,
    /// including a complete `mutual ... end` inductive or partial-definition group.
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
        let mut scope = scope.clone();
        if scope.source_site.is_none() {
            scope.source_site = Some(source_check::source_site(source)?);
        }
        self.admit_parsed_command_in_scope(
            source,
            parse_scoped_command(source)?,
            options,
            limits,
            &scope,
        )
    }

    fn admit_parsed_command_in_scope(
        &self,
        source: &[u8],
        parsed: ScopedCommandSyntax,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let parsed = match parsed {
            ScopedCommandSyntax::Mutual(members) => {
                // The group admissions below record no compiler attribute. The pin refuses
                // `[macro_inline]` on a member of a recursive group (`isValidMacroInline`);
                // refuse it on any member here rather than drop it.
                for member in &members {
                    if fln_elab::source::scope::simp::macro_inline_requested(member)
                        .map_err(DefinitionFrontendError::Elaborate)
                        .map_err(EngineExecutionError::Frontend)?
                    {
                        return Err(EngineExecutionError::Frontend(
                            DefinitionFrontendError::Elaborate(
                                fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                                    expected: "a `macro_inline` attribute on a non-recursive definition",
                                },
                            ),
                        ));
                    }
                }
                if members.iter().any(|member| {
                    fln_elab::source::partial::is_partial(member)
                        || fln_elab::source::partial::is_unsafe_definition(member)
                }) {
                    let declarations = match elaboration_outcome(
                        fln_elab::source::partial::elaborate_group(
                            &members,
                            self.environment(),
                            limits.kernel,
                            scope,
                        ),
                    )? {
                        Outcome::Complete(declarations) => declarations,
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    };
                    return self.admit_partial_result(&declarations, options, limits);
                }
                if members
                    .iter()
                    .any(fln_elab::source::partial::is_ordinary_group_member)
                {
                    let declarations = match elaboration_outcome(
                        fln_elab::source::partial::elaborate_ordinary_group(
                            &members,
                            self.environment(),
                            limits.kernel,
                            scope,
                        ),
                    )? {
                        Outcome::Complete(declarations) => declarations,
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    };
                    return self.admit_partial_result(&declarations, options, limits);
                }
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
                                local_instance: None,
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

    /// Public proof headers are elaborated in the public predecessor; their
    /// hidden implementations pass both checkers in the full predecessor before
    /// a safe signature is proposed to public admission. An explicitly exposed
    /// proof instance additionally passes both checkers in the public world.
    /// Every proof instance remains a theorem privately and an axiom publicly;
    /// the module driver publishes only after metadata can be replayed atomically.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn admit_public_source_command_in_scope(
        &self,
        public: &Engine,
        source: &[u8],
        options: &KVMap,
        limits: EngineAdmissionLimits,
        public_scope: &fln_elab::source::scope::SourceScope,
        private_scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<PublicSourceAdmission>, EngineExecutionError> {
        let parsed = match parse_scoped_command(source)? {
            ScopedCommandSyntax::Definition(parsed)
                if fln_elab::source::is_definition_body(parsed.syntax())
                    && !public_scope
                        .for_declaration(parsed.syntax())
                        .map_err(DefinitionFrontendError::Elaborate)
                        .map_err(EngineExecutionError::Frontend)?
                        .expose_definitions =>
            {
                return self.admit_hidden_public_definition(
                    public,
                    parsed.syntax(),
                    options,
                    limits,
                    public_scope,
                    private_scope,
                );
            }
            ScopedCommandSyntax::Definition(parsed)
                if fln_elab::source::is_theorem(parsed.syntax())
                    || fln_elab::source::instance_registration(parsed.syntax())
                        .map_err(DefinitionFrontendError::Elaborate)
                        .map_err(EngineExecutionError::Frontend)?
                        .is_some() =>
            {
                parsed
            }
            parsed => {
                return Ok(
                    match public.admit_parsed_command_in_scope(
                        source,
                        parsed,
                        options,
                        limits,
                        public_scope,
                    )? {
                        Outcome::Complete(public) => Outcome::Complete(PublicSourceAdmission {
                            public,
                            private_implementation: None,
                        }),
                        Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                        Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                    },
                );
            }
        };
        let worlds = fln_elab::source::TheoremWorlds {
            public: public.environment(),
            private: self.environment(),
            public_scope,
            private_scope,
        };
        let is_theorem = fln_elab::source::is_theorem(parsed.syntax());
        let candidate = if is_theorem {
            fln_elab::source::elaborate_public_theorem(parsed.syntax(), &worlds, limits.kernel).map(
                |theorem| {
                    (
                        theorem.declaration,
                        true,
                        true,
                        theorem.noncomputable,
                        theorem.local_functions,
                    )
                },
            )
        } else {
            fln_elab::source::elaborate_public_instance(parsed.syntax(), &worlds, limits.kernel)
                .map(|instance| {
                    (
                        instance.declaration,
                        instance.proof_valued,
                        instance.hidden_body,
                        instance.noncomputable,
                        instance.local_functions,
                    )
                })
        };
        let (candidate, proof_valued, hidden_body, inferred_noncomputable, local_functions) =
            match elaboration_outcome(candidate)? {
                Outcome::Complete(candidate) => candidate,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        if !proof_valued {
            if hidden_body {
                return self.admit_hidden_public_candidate(
                    public,
                    parsed.syntax(),
                    fln_elab::source::ElaboratedDeclaration {
                        declaration: candidate,
                        native_axioms: Vec::new(),
                        local_functions,
                        irreducible: false,
                        noncomputable: inferred_noncomputable,
                    },
                    options,
                    limits,
                    public_scope,
                );
            }
            if !matches!(&candidate, Declaration::Defn(definition)
                    if definition.safety == DefinitionSafety::Safe)
            {
                return Err(EngineExecutionError::NotImplemented {
                    feature: "a public data instance requires its exposed safe definition",
                });
            }
            return Ok(
                match public.admit_scoped_candidate(
                    parsed.syntax(),
                    candidate,
                    false,
                    inferred_noncomputable,
                    local_functions,
                    options,
                    limits,
                    public_scope,
                )? {
                    Outcome::Complete(public) => Outcome::Complete(PublicSourceAdmission {
                        public,
                        private_implementation: None,
                    }),
                    Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                    Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
                },
            );
        }
        if !matches!(&candidate, Declaration::Thm(_)) {
            return Err(EngineExecutionError::NotImplemented {
                feature: "a public proof must retain its theorem declaration kind",
            });
        }
        let candidate = if hidden_body {
            candidate
        } else {
            // Expose changes the proof's checking world, not its exported
            // declaration kind (Lean.AddDecl.addDeclCore). Obtain a real
            // public council receipt before re-admitting its exact theorem in
            // the private world. This scratch successor installs no metadata
            // and cannot escape if either later admission fails.
            let checked = match public
                .admit_declarations(&[candidate], options, limits)
                .map_err(EngineExecutionError::from)?
            {
                Outcome::Complete(checked) => checked,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            let [admitted] = checked.admissions.as_slice() else {
                return Err(EngineExecutionError::NotImplemented {
                    feature: "an exposed proof instance must admit exactly one public theorem",
                });
            };
            admitted.declaration.clone()
        };
        let private_implementation = match self
            .admit_declarations(&[candidate], options, limits)
            .map_err(EngineExecutionError::from)?
        {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // Obtain the interface from the actual successful admission, never
        // from an independently supplied or caller-authored signature.
        let [admitted] = private_implementation.admissions.as_slice() else {
            return Err(EngineExecutionError::NotImplemented {
                feature: "a public proof must admit exactly one checked implementation",
            });
        };
        let Declaration::Thm(theorem) = &admitted.declaration else {
            return Err(EngineExecutionError::NotImplemented {
                feature: "a public proof must preserve its checked theorem declaration",
            });
        };
        let interface = Declaration::Axiom(AxiomVal {
            base: theorem.base.clone(),
            is_unsafe: false,
        });
        let private_implementation = match self.finish_local_function_batch(
            private_implementation,
            &local_functions,
            options,
            limits,
        )? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        Ok(
            match public.admit_scoped_candidate(
                parsed.syntax(),
                interface,
                false,
                false,
                Vec::new(),
                options,
                limits,
                public_scope,
            )? {
                Outcome::Complete(public) => Outcome::Complete(PublicSourceAdmission {
                    public,
                    private_implementation: Some(private_implementation),
                }),
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        )
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
        let result = self
            .admit_declarations(&[candidate], options, limits)
            .map_err(EngineExecutionError::from)?;
        self.finish_source_inductive_auxiliaries(result, options, limits)
    }

    /// Admit a scoped candidate before applying its declaration attributes. This
    /// also handles a checked proof's safe public interface: attribute replay
    /// uses the identical name and signature, without exposing its proof.
    #[allow(clippy::too_many_arguments)]
    fn admit_scoped_candidate(
        &self,
        syntax: &fln_syntax::tree::Syntax,
        declaration: Declaration,
        irreducible: bool,
        inferred_noncomputable: bool,
        local_functions: Vec<Declaration>,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let default_priorities = fln_elab::source::default_instance_registration(syntax)
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        let registration = fln_elab::source::instance_registration(syntax)
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        let instance_namespace = fln_elab::source::instance_registration_is_scoped(syntax)
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?
            .then_some(&scope.namespace);
        let local = fln_elab::source::instance_registration_is_local(syntax)
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        let simp = fln_elab::source::scope::simp::registration(syntax)
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        let reducibility = fln_elab::source::scope::simp::reducibility(syntax)
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        let macro_inline = fln_elab::source::scope::simp::macro_inline(syntax)
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        let noncomputable = fln_elab::source::noncomputable_registration(syntax)
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        let protected = fln_elab::source::protected_registration(syntax)
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
        let result = self
            .admit_declarations(&[declaration], options, limits)
            .map_err(EngineExecutionError::from)?;
        Ok(match result {
            Outcome::Complete(mut batch) => {
                apply_batch_effects(&mut batch, irreducible, options)?;
                if fln_elab::source::scope::simp::defeq::direct_rfl(syntax) {
                    for admitted in &batch.admissions {
                        if let Declaration::Thm(theorem) = &admitted.declaration {
                            batch.engine.environment = fln_elab::source::scope::simp::defeq::infer(
                                batch.engine.environment(),
                                &theorem.base.name,
                                limits.kernel,
                            )
                            .map_err(DefinitionFrontendError::Elaborate)
                            .map_err(EngineExecutionError::Frontend)?;
                        }
                    }
                    batch.result_logical_root = batch.engine.logical_root(options);
                }
                if let Some((name, priority)) = registration {
                    // Definitions, proof theorems and exported interfaces all
                    // retain the exact admitted generated instance name.
                    let [admitted] = batch.admissions.as_slice() else {
                        return Err(EngineExecutionError::NotImplemented {
                            feature: "an instance command must admit exactly one declaration",
                        });
                    };
                    let declared = match &admitted.declaration {
                        Declaration::Defn(definition) => &definition.base.name,
                        Declaration::Thm(theorem) => &theorem.base.name,
                        Declaration::Axiom(interface) if !interface.is_unsafe => {
                            &interface.base.name
                        }
                        _ => {
                            return Err(EngineExecutionError::NotImplemented {
                                feature: "an instance command must preserve its checked declaration or proof interface",
                            });
                        }
                    };
                    let name = if name.is_anonymous() {
                        declared.clone()
                    } else {
                        scope.declaration_name(&name).map_err(|error| {
                            EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                                fln_elab::NatDefinitionElabError::Inference(
                                    fln_elab::source::SourceInferenceError::NameScope(error),
                                ),
                            ))
                        })?
                    };
                    if &name != declared {
                        return Err(EngineExecutionError::NotImplemented {
                            feature: "instance metadata must name the completed checked declaration",
                        });
                    }
                    batch.engine = match batch.engine.register_checked_source_instance(
                        &name,
                        priority,
                        instance_namespace,
                        local,
                        limits.kernel,
                    )? {
                        Outcome::Complete(engine) => engine,
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    };
                    batch.local_instance = local.then_some((name, priority));
                    batch.result_logical_root = batch.engine.logical_root(options);
                }
                if !default_priorities.is_empty() {
                    let [admitted] = batch.admissions.as_slice() else {
                        return Err(EngineExecutionError::NotImplemented {
                            feature: "default instance attributes require one checked declaration",
                        });
                    };
                    batch.engine = batch.engine.register_checked_source_defaults(
                        &admitted.declaration,
                        &default_priorities,
                    )?;
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
                if let Some((name, status)) = reducibility {
                    let name = scope.declaration_name(&name).map_err(|error| {
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::NameScope(error),
                            ),
                        ))
                    })?;
                    batch.engine.environment = set_reducibility(&batch.engine, &name, status)?;
                    batch.result_logical_root = batch.engine.logical_root(options);
                }
                if noncomputable.is_some() || inferred_noncomputable {
                    let name = noncomputable.unwrap_or_else(Name::anonymous);
                    let [admitted] = batch.admissions.as_slice() else {
                        return Err(EngineExecutionError::NotImplemented {
                            feature: "noncomputable metadata requires one checked declaration",
                        });
                    };
                    batch.engine.environment =
                        tag_noncomputable(&batch.engine, &admitted.declaration, &name, scope)?;
                    batch.result_logical_root = batch.engine.logical_root(options);
                }
                if let Some(name) = protected {
                    batch.engine.environment = tag_protected(&batch.engine, &name)?;
                    batch.result_logical_root = batch.engine.logical_root(options);
                }
                if macro_inline {
                    let [admitted] = batch.admissions.as_slice() else {
                        return Err(EngineExecutionError::NotImplemented {
                            feature: "macro_inline metadata requires one checked declaration",
                        });
                    };
                    batch.engine.environment =
                        tag_macro_inline(&batch.engine, &admitted.declaration)?;
                    batch.result_logical_root = batch.engine.logical_root(options);
                }
                return self.finish_local_function_batch(batch, &local_functions, options, limits);
            }
            Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        })
    }

    /// Register defaults under the actual checked declaration identity, including
    /// anonymous instances, private names and a public proof's safe interface.
    pub(super) fn register_checked_source_defaults(
        &self,
        declaration: &Declaration,
        priorities: &[u32],
    ) -> Result<Self, EngineExecutionError> {
        let name = match declaration {
            Declaration::Defn(definition) => &definition.base.name,
            Declaration::Thm(theorem) => &theorem.base.name,
            Declaration::Opaque(value) if !value.is_unsafe => &value.base.name,
            Declaration::Axiom(interface) if !interface.is_unsafe => &interface.base.name,
            _ => {
                return Err(EngineExecutionError::NotImplemented {
                    feature: "default instance metadata requires a checked safe declaration",
                });
            }
        };
        let mut next = self.clone();
        for &priority in priorities {
            next.environment =
                fln_elab::instances::defaults::register(next.environment(), name, priority)
                    .map_err(|error| {
                        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                            fln_elab::NatDefinitionElabError::Inference(
                                fln_elab::source::SourceInferenceError::InstanceRegistry(error),
                            ),
                        ))
                    })?;
        }
        Ok(next)
    }

    /// Metadata follows a completed admission. Native instance fallback is
    /// implicitReducible, so proof instances need an explicit semireducible row;
    /// data instances retain the pin's automatic reducibility behavior.
    pub(super) fn register_checked_source_instance(
        &self,
        name: &Name,
        priority: u32,
        namespace: Option<&Name>,
        local: bool,
        kernel: Budget,
    ) -> Result<Outcome<Engine>, EngineExecutionError> {
        if namespace.is_some_and(Name::is_anonymous) {
            return Err(EngineExecutionError::Frontend(
                DefinitionFrontendError::Elaborate(
                    fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                        expected: "scoped instances inside a non-root namespace",
                    },
                ),
            ));
        }
        let base = self
            .environment()
            .find(name)
            .ok_or(EngineExecutionError::NotImplemented {
                feature: "instance metadata requires an already admitted declaration",
            })?
            .constant_val();
        let proof = match declaration_is_proposition(self.environment(), base, kernel)? {
            Outcome::Complete(proof) => proof,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut engine = self.clone();
        let registry_error = |error| {
            EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                fln_elab::NatDefinitionElabError::Inference(
                    fln_elab::source::SourceInferenceError::InstanceRegistry(error),
                ),
            ))
        };
        let registered = if local {
            // The pin rejects uninferable instance parameters at declaration
            // time. Reuse the same bounded telescope/index derivation used by
            // native search; an unsupported model cannot become a local effect.
            let registry = fln_elab::instances::InstanceRegistry::read(engine.environment())
                .map_err(registry_error)?;
            let mut work_left = usize::try_from(kernel.steps)
                .unwrap_or(usize::MAX)
                .min(1_000_000);
            if fln_elab::instances::export::derive_index(
                engine.environment(),
                &registry,
                name,
                &mut work_left,
            )
            .map_err(registry_error)?
            .is_none()
            {
                return Err(EngineExecutionError::NotImplemented {
                    feature: "a local instance requires a supported inferable telescope and index",
                });
            }
            // Validate the same checked class and declaration as a persistent
            // instance, without publishing its selection beyond the scope.
            fln_elab::instances::scoped::ActiveScopes::default()
                .register_local(engine.environment(), name, priority)
                .map(|()| engine.environment().clone())
        } else {
            match namespace {
                Some(namespace) => fln_elab::instances::scoped::register(
                    engine.environment(),
                    namespace,
                    name,
                    priority,
                ),
                None => {
                    fln_elab::instances::register_instance(engine.environment(), name, priority)
                }
            }
        };
        engine.environment = registered.map_err(registry_error)?;
        if proof || local {
            engine.environment = fln_elab::reducibility::register(
                engine.environment(),
                name,
                if proof {
                    fln_elab::reducibility::Reducibility::Semireducible
                } else {
                    // Local data instances have no persistent instance row
                    // from which the usual implicit-reducibility fallback
                    // could be derived. The status belongs to the declaration.
                    fln_elab::reducibility::Reducibility::ImplicitReducible
                },
            )
            .map_err(|error| {
                EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                    fln_elab::NatDefinitionElabError::Inference(
                        fln_elab::source::SourceInferenceError::Unification(Box::new(
                            fln_elab::constraint::unify::UnificationError::Reducibility(error),
                        )),
                    ),
                ))
            })?;
        }
        Ok(Outcome::Complete(engine))
    }

    fn admit_scoped_definition(
        &self,
        source: &[u8],
        parsed: fln_parse::ParsedDefinition,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        if fln_elab::source::partial::is_partial(parsed.syntax()) {
            let declarations = match elaboration_outcome(fln_elab::source::partial::elaborate(
                parsed.syntax(),
                self.environment(),
                limits.kernel,
                scope,
            ))? {
                Outcome::Complete(declarations) => declarations,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            // One ordinary council batch: a failed companion never publishes
            // the logical default as a successful executable definition.
            return self.admit_partial_result(&declarations, options, limits);
        }
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
            let result = self.finish_source_inductive_auxiliaries(result, options, limits)?;
            return self.finish_source_deriving(result, deriving.as_ref(), options, limits, scope);
        }
        if !fln_elab::source::is_record(syntax) {
            if scope != &fln_elab::source::scope::SourceScope::default()
                || fln_elab::source::instance_registration_is_local(parsed.syntax())
                    .map_err(DefinitionFrontendError::Elaborate)
                    .map_err(EngineExecutionError::Frontend)?
            {
                let elaborated = match elaboration_outcome(
                    fln_elab::elaborate_definition_with_effects_in_scope_with_budget(
                        parsed.syntax(),
                        self.environment(),
                        limits.kernel,
                        scope,
                    ),
                )? {
                    Outcome::Complete(declaration) => declaration,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                return self.admit_scoped_candidate(
                    parsed.syntax(),
                    elaborated.declaration,
                    elaborated.irreducible,
                    elaborated.noncomputable,
                    elaborated.local_functions,
                    options,
                    limits,
                    scope,
                );
            }
            return Ok(
                match self.admit_source_declaration(source, options, limits)? {
                    Outcome::Complete(admitted) => Outcome::Complete(admitted.into_batch()),
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
            // Defaults and flat constructors remain ordinary definitions even
            // when they return proofs; consumers must instantiate their bodies.
            let mut predecessor = self;
            let mut proof_projection = false;
            for (index, admission) in batch.admissions.iter().enumerate() {
                if let Declaration::Defn(definition) = &admission.declaration
                    && definition.base.name != record.flat_constructor
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
        // Complete the declaration stream before adding any record journals,
        // so adjacent council receipts retain their exact predecessor roots.
        let result = self.finish_source_inductive_auxiliaries(result, options, limits)?;
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
    /// A complete `mutual` group, including a single supported member.
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
    // Under an entered grammar (`source_check::grammar`), the file's notations are expanded
    // before the elaborator reads the tree.
    let parsed = fln_parse::parse_definition(source)
        .and_then(fln_parse::ParsedDefinition::expanded)
        .map_err(DefinitionFrontendError::Parse)
        .map_err(EngineExecutionError::Frontend)?;
    if fln_elab::source::scope::is_example(parsed.syntax()) {
        let parsed = fln_parse::parse_source_command(source)
            .and_then(fln_parse::ParsedSourceCommand::expanded)
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

/// Bind a source noncomputable request to the declaration that just passed the council.
/// Anonymous instances take their generated name from that admission. Named requests must
/// match it after namespace/private-name expansion; an unrelated existing declaration is
/// never a valid substitute. The journal only removes a runtime binding, not proof authority.
pub(crate) fn tag_noncomputable(
    engine: &Engine,
    declaration: &Declaration,
    requested: &Name,
    scope: &fln_elab::source::scope::SourceScope,
) -> Result<Environment, EngineExecutionError> {
    let declared = match declaration {
        Declaration::Defn(value) => &value.base.name,
        Declaration::Thm(value) => &value.base.name,
        Declaration::Opaque(value) => &value.base.name,
        // Public proof/opaque interfaces retain the checked declaration's exact name.
        Declaration::Axiom(value) if !value.is_unsafe => &value.base.name,
        _ => {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "noncomputable metadata requires one checked declaration",
            });
        }
    };
    let name = if requested.is_anonymous() {
        declared.clone()
    } else {
        scope.declaration_name(requested).map_err(|error| {
            EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                fln_elab::NatDefinitionElabError::Inference(
                    fln_elab::source::SourceInferenceError::NameScope(error),
                ),
            ))
        })?
    };
    if &name != declared {
        return Err(EngineExecutionError::UnexpectedPublication {
            detail: "noncomputable metadata must name the completed checked declaration",
        });
    }
    fln_elab::noncomputable::register(engine.environment(), &name).map_err(|_| {
        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
            fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                expected: "a noncomputable tag on an admitted declaration",
            },
        ))
    })
}

/// Record a `@[reducible]`-style attribute's status for an admitted declaration of this module
/// (`scope::simp::reducibility` validated it), as the pin's `setReducibilityStatus`.
pub(crate) fn set_reducibility(
    engine: &Engine,
    name: &Name,
    status: fln_elab::reducibility::Reducibility,
) -> Result<Environment, EngineExecutionError> {
    fln_elab::reducibility::register(engine.environment(), name, status).map_err(|error| {
        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
            fln_elab::NatDefinitionElabError::Inference(
                fln_elab::source::SourceInferenceError::Unification(Box::new(
                    fln_elab::constraint::unify::UnificationError::Reducibility(error),
                )),
            ),
        ))
    })
}

/// Tag an admitted definition `@[macro_inline]` (`scope::simp::registration` validated the
/// attribute and the elaborator a non-recursive body). The pin's `isValidMacroInline` admits only
/// a definition alone in its group; anything else is the pin's refusal, never a dropped attribute.
pub(crate) fn tag_macro_inline(
    engine: &Engine,
    declaration: &Declaration,
) -> Result<Environment, EngineExecutionError> {
    let refused = || {
        EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
            fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                expected: "a `macro_inline` attribute on a non-recursive definition",
            },
        ))
    };
    let Declaration::Defn(definition) = declaration else {
        return Err(refused());
    };
    fln_elab::macro_inline::register(engine.environment(), &definition.base.name)
        .map_err(|_| refused())
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
