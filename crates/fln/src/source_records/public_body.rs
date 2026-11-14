//! Construct hidden-body interfaces only from an actual successful admission.
//! The caller holds both successors until their metadata replay is atomic.
use super::*;

impl Engine {
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
                    native_axioms: Vec::new(),
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
        if !matches!(
            candidate.declarations(),
            [Declaration::Opaque(_), Declaration::Mutual(_)]
        ) {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "a recursive public partial definition must retain both checked halves",
            });
        }
        // Both candidates cross the ordinary council together. A bad executable
        // companion cannot publish a successful logical default or signature.
        let private_implementation = match self.admit_partial_result(&candidate, options, limits)? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let Some(admitted) = private_implementation.admissions.first() else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "a public partial definition must admit its logical interface",
            });
        };
        let Declaration::Opaque(logical) = &admitted.declaration else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "a public partial definition must preserve its checked opaque interface",
            });
        };
        let interface = Declaration::Axiom(AxiomVal {
            base: logical.base.clone(),
            is_unsafe: logical.is_unsafe,
        });
        Ok(
            match public.admit_scoped_candidate(
                syntax,
                interface,
                false,
                None,
                false,
                Vec::new(),
                options,
                limits,
                worlds.public_scope,
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
        let mut private_implementation = match self
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
        Ok(
            match public.admit_scoped_candidate(
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
                    public,
                    private_implementation: Some(private_implementation),
                }),
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        )
    }
}
