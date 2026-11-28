//! Construct hidden-body interfaces only from an actual successful admission.
//! The caller holds both successors until their metadata replay is atomic.
use super::*;

/// The same auxiliary candidates are checked in the selected body world.
/// Public theorem interfaces come only from successful body admissions.
pub(super) struct PublicAuxiliaries {
    pub(super) public: DeclarationBatchAdmission,
    pub(super) private: DeclarationBatchAdmission,
}

/// Keep owner-specific metadata and helper processing on the owner's batch.
/// Its checked predecessors join the receipt only when the command succeeds.
pub(super) fn prepend_auxiliaries(
    mut owner: DeclarationBatchAdmission,
    prefix: DeclarationBatchAdmission,
) -> DeclarationBatchAdmission {
    owner.base_logical_root = prefix.base_logical_root;
    owner.admissions.splice(0..0, prefix.admissions);
    owner
}

impl Engine {
    /// An absent predecessor is an identity transition, not an empty request
    /// to the public declaration-admission API, which deliberately rejects one.
    fn admit_auxiliary_prefix(
        &self,
        declarations: &[Declaration],
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        if declarations.is_empty() {
            let root = self.logical_root(options);
            return Ok(Outcome::Complete(DeclarationBatchAdmission {
                engine: self.clone(),
                base_logical_root: root,
                result_logical_root: root,
                admissions: Vec::new(),
                local_instance: None,
                local_symm: Vec::new(),
            }));
        }
        self.admit_declarations(declarations, options, limits)
            .map_err(EngineExecutionError::from)
    }

    /// Header quotations are closed Syntax data needed by the public type and
    /// remain fully checked definitions in both worlds, even for hidden owners.
    /// Hidden bodies keep all other auxiliaries private. Exposed bodies first check
    /// ordinary auxiliary proofs in the public predecessor, then admit their
    /// public interfaces as the pin's AddDecl.addDeclCore does. Explicit
    /// `private_decl%` bridge auxiliaries are checked in full in the private
    /// world first and expose only their checked public signature as an Axiom
    /// in the public world (which rejects any leaked private type). Nested
    /// auxiliaries created inside `private_decl%` remain strictly private.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn admit_public_auxiliaries(
        &self,
        public: &Engine,
        declarations: &[Declaration],
        visibility: &fln_elab::source::AuxiliaryVisibility,
        hidden: bool,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<PublicAuxiliaries>, EngineExecutionError> {
        let private = match self.admit_auxiliary_prefix(declarations, options, limits)? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut public_engine = public.clone();
        let base_logical_root = public_engine.logical_root(options);
        let mut public_admissions = Vec::new();
        if !declarations.is_empty() && (!hidden || !visibility.header_quotations.is_empty()) {
            if private.admissions.len() != declarations.len() {
                return Err(EngineExecutionError::UnexpectedPublication {
                    detail: "private auxiliary prefix admission count must match candidate count",
                });
            }
            for (candidate, admitted_private) in declarations.iter().zip(private.admissions.iter())
            {
                let name = match candidate {
                    Declaration::Axiom(val) => Some(&val.base.name),
                    Declaration::Defn(val) => Some(&val.base.name),
                    Declaration::Thm(val) => Some(&val.base.name),
                    Declaration::Opaque(val) => Some(&val.base.name),
                    _ => None,
                };
                let header_quotation =
                    name.is_some_and(|name| visibility.header_quotations.contains(name));
                if header_quotation
                    && name.is_some_and(|name| {
                        visibility.private_only.contains(name)
                            || visibility.private_bridge.contains(name)
                            || visibility.computable_private_bridge.contains(name)
                    })
                {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "a public header quotation cannot be a private body auxiliary",
                    });
                }
                if (hidden && !header_quotation)
                    || name.is_some_and(|name| visibility.private_only.contains(name))
                {
                    continue;
                }
                let interface = if header_quotation {
                    // A visibility marker is not authority. Restrict this path
                    // to the actual closed data shape, then independently check
                    // the full value in the public predecessor below.
                    match &admitted_private.declaration {
                        Declaration::Defn(definition)
                            if definition.safety == DefinitionSafety::Safe
                                && definition.base.level_params.is_empty()
                                && definition.base.type_
                                    == Expr::const_(
                                        Name::from_components(["Lean", "Syntax"]),
                                        Vec::new(),
                                    )
                                && !definition.value.has_fvar()
                                && !definition.value.has_loose_bvars()
                                && !definition.value.has_expr_mvar()
                                && !definition.value.has_level_mvar()
                                && !definition.value.has_level_param() =>
                        {
                            Declaration::Defn(definition.clone())
                        }
                        _ => {
                            return Err(EngineExecutionError::UnexpectedPublication {
                                detail: "a public header quotation must be closed safe Lean.Syntax data",
                            });
                        }
                    }
                } else if name.is_some_and(|name| visibility.private_bridge.contains(name)) {
                    // Already checked in full by K1 + independent checker in `private`.
                    // Expose only its checked signature in `public`; K1 + independent
                    // checker below verify that the signature uses only public constants.
                    match &admitted_private.declaration {
                        Declaration::Thm(theorem) => Declaration::Axiom(AxiomVal {
                            base: theorem.base.clone(),
                            is_unsafe: false,
                        }),
                        Declaration::Defn(definition)
                            if definition.safety == DefinitionSafety::Safe =>
                        {
                            Declaration::Axiom(AxiomVal {
                                base: definition.base.clone(),
                                is_unsafe: false,
                            })
                        }
                        _ => {
                            return Err(EngineExecutionError::UnexpectedPublication {
                                detail: "private_decl% auxiliary must be a checked theorem or safe definition",
                            });
                        }
                    }
                } else {
                    let checked = match public_engine.admit_declarations(
                        std::slice::from_ref(candidate),
                        options,
                        limits,
                    )? {
                        Outcome::Complete(checked) => checked,
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    };
                    let [admitted] = checked.admissions.as_slice() else {
                        return Err(EngineExecutionError::UnexpectedPublication {
                            detail: "ordinary source auxiliary must admit exactly one declaration",
                        });
                    };
                    match &admitted.declaration {
                        Declaration::Thm(theorem) => Declaration::Axiom(AxiomVal {
                            base: theorem.base.clone(),
                            is_unsafe: false,
                        }),
                        Declaration::Axiom(axiom) => Declaration::Axiom(axiom.clone()),
                        _ => {
                            return Err(EngineExecutionError::UnexpectedPublication {
                                detail: "source proof auxiliaries must preserve theorem or native axiom kind",
                            });
                        }
                    }
                };
                let step = match public_engine.admit_declarations(&[interface], options, limits)? {
                    Outcome::Complete(checked) => checked,
                    Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                    Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                };
                public_engine = step.engine;
                public_admissions.extend(step.admissions);
            }
        }
        let result_logical_root = public_engine.logical_root(options);
        let public = DeclarationBatchAdmission {
            engine: public_engine,
            base_logical_root,
            result_logical_root,
            admissions: public_admissions,
            local_instance: None,
            local_symm: Vec::new(),
        };
        Ok(Outcome::Complete(PublicAuxiliaries { public, private }))
    }

    /// Exposed data keeps its checked value in both worlds. Auxiliary theorem
    /// bodies still remain private: the public owner checks against their
    /// admitted signatures, while private replay retains their actual proofs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn admit_exposed_public_candidate(
        &self,
        public: &Engine,
        syntax: &fln_syntax::tree::Syntax,
        candidate: fln_elab::source::ElaboratedDeclaration,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        public_scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<PublicSourceAdmission>, EngineExecutionError> {
        let auxiliaries = match self.admit_public_auxiliaries(
            public,
            &candidate.auxiliary_declarations,
            &candidate.auxiliary_visibility,
            false,
            options,
            limits,
        )? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let public = match auxiliaries.public.engine.admit_scoped_candidate(
            syntax,
            candidate.declaration,
            candidate.irreducible,
            candidate.equation_info,
            candidate.noncomputable,
            candidate.local_functions,
            options,
            limits,
            public_scope,
        )? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let declarations: Vec<_> = public
            .admissions
            .iter()
            .map(|admitted| admitted.declaration.clone())
            .collect();
        let private =
            match auxiliaries
                .private
                .engine
                .admit_declarations(&declarations, options, limits)?
            {
                Outcome::Complete(checked) => checked,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        // PublicWorld replays the owner's metadata after both successors have
        // succeeded. Reapplying it here would duplicate instance/simp histories.
        Ok(Outcome::Complete(PublicSourceAdmission {
            public: prepend_auxiliaries(public, auxiliaries.public),
            private_implementation: Some(prepend_auxiliaries(private, auxiliaries.private)),
            metadata_complete: false,
        }))
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn admit_hidden_public_definition(
        &self,
        public: &Engine,
        syntax: &fln_syntax::tree::Syntax,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        public_scope: &fln_elab::source::scope::SourceScope,
        private_scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<PublicSourceAdmission>, EngineExecutionError> {
        let worlds = fln_elab::source::TheoremWorlds {
            public: public.environment(),
            private: self.environment(),
            public_scope,
            private_scope,
        };
        if fln_elab::source::partial::is_partial(syntax) {
            return self.admit_hidden_public_partial(public, syntax, &worlds, options, limits);
        }
        let candidate = match elaboration_outcome(fln_elab::source::elaborate_public_definition(
            syntax,
            &worlds,
            limits.kernel,
        ))? {
            Outcome::Complete(candidate) => candidate,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        self.admit_hidden_public_candidate(public, syntax, candidate, options, limits, public_scope)
    }

    fn admit_hidden_public_partial(
        &self,
        public: &Engine,
        syntax: &fln_syntax::tree::Syntax,
        worlds: &fln_elab::source::TheoremWorlds<'_>,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<PublicSourceAdmission>, EngineExecutionError> {
        let candidate = match elaboration_outcome(fln_elab::source::partial::elaborate_public(
            syntax,
            worlds,
            limits.kernel,
        ))? {
            Outcome::Complete(candidate) => candidate,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let owner = candidate
            .owner_name()
            .ok_or(EngineExecutionError::UnexpectedPublication {
                detail: "a single public partial command must retain its source owner",
            })?;
        if let [Declaration::Defn(definition)] = candidate.declarations() {
            // A partial command with no surviving self reference is an ordinary
            // safe definition. Keep the existing hidden-body publication path,
            // which defers its owner's metadata to the public world's replay.
            let noncomputable = candidate.noncomputable().contains(&definition.base.name);
            return self.admit_hidden_public_candidate(
                public,
                syntax,
                fln_elab::source::ElaboratedDeclaration {
                    declaration: Declaration::Defn(definition.clone()),
                    auxiliary_declarations: Vec::new(),
                    auxiliary_visibility: Default::default(),
                    equation_info: None,
                    local_functions: Vec::new(),
                    irreducible: false,
                    noncomputable,
                },
                options,
                limits,
                worlds.public_scope,
            );
        }
        // Lifted local functions form ordinary dependency-ordered components.
        // A helper can precede its owner, and a helper-only recursive component
        // can leave the owner a safe definition. Check the complete batch before
        // selecting the source owner's interface; no helper is a public API.
        let private_implementation = match self.admit_partial_result(&candidate, options, limits)? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let logical = private_implementation
            .admissions
            .iter()
            .find_map(|admitted| match &admitted.declaration {
                Declaration::Defn(definition)
                    if &definition.base.name == owner
                        && definition.safety == DefinitionSafety::Safe =>
                {
                    Some(&definition.base)
                }
                Declaration::Opaque(opaque) if &opaque.base.name == owner && !opaque.is_unsafe => {
                    Some(&opaque.base)
                }
                _ => None,
            })
            .ok_or(EngineExecutionError::UnexpectedPublication {
                detail: "a public partial definition must retain its checked safe logical owner",
            })?;
        // Codegen failure can propagate from a helper SCC into an ordinary
        // owner. Read the completed private result, not only the initial set of
        // failed candidates. Recursive opaque witnesses remain untagged.
        let noncomputable =
            fln_elab::noncomputable::read(private_implementation.engine.environment())
                .map_err(|error| {
                    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                        fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::NoncomputableJournal(error),
                        ),
                    ))
                })?
                .contains(owner);
        let interface = Declaration::Axiom(AxiomVal {
            base: logical.clone(),
            is_unsafe: false,
        });
        Ok(
            match public.admit_scoped_candidate(
                syntax,
                interface,
                false,
                None,
                noncomputable,
                Vec::new(),
                options,
                limits,
                worlds.public_scope,
            )? {
                Outcome::Complete(public) => Outcome::Complete(PublicSourceAdmission {
                    public,
                    private_implementation: Some(private_implementation),
                    // Partial syntax admits no independent attributes. Both
                    // worlds now contain the complete owner codegen effects;
                    // replaying them would duplicate a failed safe owner's tag.
                    metadata_complete: true,
                }),
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        )
    }

    /// Shared by definitions, abbreviations, opaques and explicitly hidden
    /// data instances. No successful interface exists without its checked body.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn admit_hidden_public_candidate(
        &self,
        public: &Engine,
        syntax: &fln_syntax::tree::Syntax,
        candidate: fln_elab::source::ElaboratedDeclaration,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        public_scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<PublicSourceAdmission>, EngineExecutionError> {
        let auxiliaries = match self.admit_public_auxiliaries(
            public,
            &candidate.auxiliary_declarations,
            &candidate.auxiliary_visibility,
            true,
            options,
            limits,
        )? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut private_implementation = match auxiliaries
            .private
            .engine
            .admit_declarations(&[candidate.declaration], options, limits)
            .map_err(EngineExecutionError::from)?
        {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        apply_batch_effects(
            &mut private_implementation,
            candidate.irreducible,
            None,
            options,
        )?;
        // PublicWorld replays the public owner's attributes exactly once into
        // this private successor. Installing them here as well would duplicate
        // instance and noncomputable journal entries. Helpers still inherit the
        // owner's noncomputable classification before that atomic replay.
        let noncomputable = candidate.noncomputable
            || fln_elab::source::noncomputable_registration(syntax)
                .map_err(DefinitionFrontendError::Elaborate)
                .map_err(EngineExecutionError::Frontend)?
                .is_some();
        let private_implementation = match self.finish_local_function_batch_with_noncomputable(
            private_implementation,
            &candidate.local_functions,
            options,
            limits,
            noncomputable,
        )? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let equation_scope = public_scope
            .for_declaration(syntax)
            .map_err(DefinitionFrontendError::Elaborate)
            .map_err(EngineExecutionError::Frontend)?;
        let private_implementation = match self.finish_source_simp_batch(
            private_implementation,
            None,
            &equation_scope,
            options,
            limits,
        )? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // The primary implementation is first; each following helper has its
        // own council receipt and remains private. None is an exported axiom.
        let Some(admitted) = private_implementation.admissions.first() else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "a hidden public implementation must admit its primary declaration",
            });
        };
        // Lean.AddDecl.addDeclCore uses precisely the checked constant's base
        // and safety. Never invent a value, weaken safety, or use an unchecked
        // alternative type to make a private implementation exportable.
        let (base, is_unsafe) = match &admitted.declaration {
            Declaration::Defn(definition) if definition.safety != DefinitionSafety::Partial => (
                &definition.base,
                definition.safety == DefinitionSafety::Unsafe,
            ),
            Declaration::Opaque(opaque) => (&opaque.base, opaque.is_unsafe),
            _ => {
                return Err(EngineExecutionError::NotImplemented {
                    feature: "hidden public partial or mutual implementation companions",
                });
            }
        };
        let interface = Declaration::Axiom(AxiomVal {
            base: base.clone(),
            is_unsafe,
        });
        let private_implementation =
            prepend_auxiliaries(private_implementation, auxiliaries.private);
        Ok(
            match auxiliaries.public.engine.admit_scoped_candidate(
                syntax,
                interface,
                false,
                None,
                candidate.noncomputable,
                Vec::new(),
                options,
                limits,
                public_scope,
            )? {
                Outcome::Complete(public) => Outcome::Complete(PublicSourceAdmission {
                    public: prepend_auxiliaries(public, auxiliaries.public),
                    private_implementation: Some(private_implementation),
                    metadata_complete: false,
                }),
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        )
    }
}
