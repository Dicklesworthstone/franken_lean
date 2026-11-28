//! One atomic source publication for computed fields, including the public
//! signatures/private logical bodies boundary and the cached runtime layout.
use super::*;
use fln_elab::computed_fields::ComputedFieldError;
use fln_elab::records::RecordBudget;
use fln_elab::source::SourceInferenceError;
use fln_elab::source::computed_fields::ComputedFieldBlock;

struct ComputedAdmission {
    batch: DeclarationBatchAdmission,
    logical: BTreeSet<Name>,
    irreducible: BTreeSet<Name>,
    implemented_by: Vec<(Name, Name)>,
}

fn frontend(error: SourceInferenceError) -> EngineExecutionError {
    EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
        fln_elab::NatDefinitionElabError::Inference(error),
    ))
}

fn computed_outcome<T>(
    result: Result<T, ComputedFieldError>,
) -> Result<Outcome<T>, EngineExecutionError> {
    elaboration_outcome(result.map_err(|error| {
        fln_elab::NatDefinitionElabError::Inference(match error {
            ComputedFieldError::ResourceLimit => SourceInferenceError::ResourceLimit,
            ComputedFieldError::Reduction(error) => SourceInferenceError::Unification(error),
            other => SourceInferenceError::ComputedField(other),
        })
    }))
}

fn noncomputable(engine: &mut Engine, name: &Name) -> Result<(), EngineExecutionError> {
    engine.environment =
        fln_elab::noncomputable::register(engine.environment(), name).map_err(|error| {
            frontend(match error {
                fln_elab::noncomputable::NoncomputableError::Limit => {
                    SourceInferenceError::ResourceLimit
                }
                other => SourceInferenceError::NoncomputableJournal(other),
            })
        })?;
    Ok(())
}

fn implementation_cases_on_metadata(
    engine: &mut Engine,
    family: &Name,
) -> Result<(), EngineExecutionError> {
    let cases_on = Name::str(Name::str(family.clone(), "_impl"), "casesOn");
    engine.environment = fln_elab::reducibility::register(
        engine.environment(),
        &cases_on,
        fln_elab::reducibility::Reducibility::Reducible,
    )
    .map_err(|error| {
        frontend(SourceInferenceError::Unification(Box::new(
            fln_elab::constraint::unify::UnificationError::Reducibility(error),
        )))
    })?;
    engine.environment =
        fln_elab::aux_recursors::register_module(engine.environment(), &[cases_on])
            .map_err(|error| frontend(SourceInferenceError::AuxiliaryJournal(error)))?;
    Ok(())
}

fn register_edges(engine: &mut Engine, edges: &[(Name, Name)]) -> Result<(), EngineExecutionError> {
    for (original, implementation) in edges {
        engine.environment =
            fln_elab::implemented_by::register(engine.environment(), original, implementation)
                .map_err(|error| {
                    frontend(match error {
                        fln_elab::implemented_by::ImplementedByError::Limit => {
                            SourceInferenceError::ResourceLimit
                        }
                        other => SourceInferenceError::ImplementedByJournal(other),
                    })
                })?;
    }
    Ok(())
}

impl Engine {
    pub(super) fn finish_source_computed_fields(
        &self,
        result: Outcome<DeclarationBatchAdmission>,
        computed: Option<&ComputedFieldBlock>,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationBatchAdmission>, EngineExecutionError> {
        let Some(computed) = computed else {
            return Ok(result);
        };
        let prefix = match result {
            Outcome::Complete(prefix) => prefix,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        Ok(
            match prefix
                .engine
                .admit_computed_fields(computed, options, limits, None)?
            {
                Outcome::Complete(checked) => {
                    Outcome::Complete(public_body::prepend_auxiliaries(checked.batch, prefix))
                }
                Outcome::Inconclusive(reason) => Outcome::Inconclusive(reason),
                Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
            },
        )
    }

    /// The predecessor contains only the original checked family/auxiliaries.
    /// A failure at any later stage drops this entire private successor.
    fn admit_computed_fields(
        &self,
        computed: &ComputedFieldBlock,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        public_body: Option<(&Environment, &fln_elab::source::scope::SourceScope)>,
    ) -> Result<Outcome<ComputedAdmission>, EngineExecutionError> {
        let logical = match elaboration_outcome(match public_body {
            Some((environment, scope)) => {
                computed.elaborate_exported(environment, limits.kernel, scope)
            }
            None => computed.elaborate(self.environment(), limits.kernel),
        })? {
            Outcome::Complete(logical) => logical,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        if !logical.noncomputable().is_empty() {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "computed getters must be explicitly noncomputable, not suppressed compiler failures",
            });
        }
        let mut batch = match self.admit_declarations(logical.declarations(), options, limits)? {
            Outcome::Complete(batch) => batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let mut logical_names = BTreeSet::new();
        for declaration in logical.declarations() {
            let Declaration::Defn(definition) = declaration else {
                return Err(EngineExecutionError::UnexpectedPublication {
                    detail: "computed-field logical elaboration must produce safe definitions",
                });
            };
            if definition.safety != DefinitionSafety::Safe {
                return Err(EngineExecutionError::UnexpectedPublication {
                    detail: "computed-field recursion must be logically terminating",
                });
            }
            logical_names.insert(definition.base.name.clone());
        }
        let budget = RecordBudget::default();
        let implementation =
            match computed_outcome(fln_elab::computed_fields::implementation_family(
                batch.engine.environment(),
                &computed.family,
                &computed.fields,
                limits.kernel,
                budget,
            ))? {
                Outcome::Complete(implementation) => implementation,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        let Declaration::Inductive(implementation_block) = &implementation else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "computed implementation must be an inductive family",
            });
        };
        let implementation_types = implementation_block.types.clone();
        let step = match batch
            .engine
            .admit_declarations(&[implementation], options, limits)?
        {
            Outcome::Complete(step) => step,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        batch = public_body::prepend_auxiliaries(step, batch);
        let [family] = implementation_types.as_slice() else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "one computed implementation family",
            });
        };
        let recursor_name = Name::str(family.base.name.clone(), "rec");
        let Some(ConstantInfo::Rec(recursor)) = batch.engine.environment().find(&recursor_name)
        else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "computed implementation has no admitted recursor",
            });
        };
        let cases_on = fln_elab::inductive::auxiliaries::cases_on_declaration(
            family,
            recursor,
            &implementation_types,
            budget,
        )
        .map_err(|error| {
            frontend(match error {
                fln_elab::inductive::auxiliaries::AuxiliaryError::ResourceLimit => {
                    SourceInferenceError::ResourceLimit
                }
                other => SourceInferenceError::Auxiliary(other),
            })
        })?;
        let step = match batch.engine.admit_declarations(
            &[Declaration::Defn(cases_on)],
            options,
            limits,
        )? {
            Outcome::Complete(step) => step,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        batch = public_body::prepend_auxiliaries(step, batch);
        let replacements = match computed_outcome(fln_elab::computed_fields::replacements(
            batch.engine.environment(),
            &computed.family,
            &computed.fields,
            limits.kernel,
            budget,
        ))? {
            Outcome::Complete(replacements) => replacements,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let step =
            match batch
                .engine
                .admit_declarations(&replacements.declarations, options, limits)?
            {
                Outcome::Complete(step) => step,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        batch = public_body::prepend_auxiliaries(step, batch);
        // Keep the generated declaration admissions contiguous. Their source
        // compilation/auxiliary attributes become durable only after the last
        // override has passed both checking engines.
        for name in &logical_names {
            noncomputable(&mut batch.engine, name)?;
        }
        for name in logical.irreducible() {
            let declaration = logical.declarations().iter().find(|declaration| {
                matches!(declaration, Declaration::Defn(definition) if &definition.base.name == name)
            }).ok_or(EngineExecutionError::UnexpectedPublication {
                detail: "an irreducible computed getter must have its checked logical definition",
            })?;
            elaboration::register_irreducible(&mut batch.engine, declaration)?;
        }
        implementation_cases_on_metadata(&mut batch.engine, &computed.family)?;
        register_edges(&mut batch.engine, &replacements.implemented_by)?;
        for name in &computed.protected_fields {
            batch.engine.environment = tag_protected(&batch.engine, name)?;
        }
        batch.engine.environment = match computed_outcome(fln_elab::computed_fields::register(
            batch.engine.environment(),
            &computed.family,
            &computed.fields,
            &computed.inline_fields,
            limits.kernel,
            budget,
        ))? {
            Outcome::Complete(environment) => environment,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        batch.result_logical_root = batch.engine.logical_root(options);
        Ok(Outcome::Complete(ComputedAdmission {
            batch,
            logical: logical_names,
            irreducible: logical.irreducible().clone(),
            implemented_by: replacements.implemented_by,
        }))
    }

    /// Public data keeps its real cached representation and unsafe runtime
    /// replacements. Only the separately checked logical getter bodies (and
    /// their logical auxiliaries) are projected to safe public signatures.
    pub(super) fn admit_public_computed_inductive(
        &self,
        public: &Engine,
        computed: &ComputedFieldBlock,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        public_scope: &fln_elab::source::scope::SourceScope,
    ) -> Result<Outcome<PublicSourceAdmission>, EngineExecutionError> {
        let public_prefix = match public.admit_scoped_inductives(
            std::slice::from_ref(&computed.syntax),
            options,
            limits,
            public_scope,
        )? {
            Outcome::Complete(batch) => batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let headers = match elaboration_outcome(computed.headers(
            public_prefix.engine.environment(),
            limits.kernel,
            public_scope,
        ))? {
            Outcome::Complete(headers) => headers,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let private_prefix = match self.admit_scoped_inductives(
            std::slice::from_ref(&computed.syntax),
            options,
            limits,
            public_scope,
        )? {
            Outcome::Complete(batch) => batch,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        if !public_prefix
            .admissions
            .iter()
            .map(|row| &row.declaration)
            .eq(private_prefix.admissions.iter().map(|row| &row.declaration))
        {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "computed-field family and auxiliaries must preserve the public declaration bundle",
            });
        }
        let private = match private_prefix.engine.admit_computed_fields(
            computed,
            options,
            limits,
            computed
                .exposes_getters()
                .then_some((public_prefix.engine.environment(), public_scope)),
        )? {
            Outcome::Complete(private) => private,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        for header in &headers {
            let Declaration::Axiom(header) = header else {
                return Err(EngineExecutionError::UnexpectedPublication {
                    detail: "computed-field public signature must be a safe axiom candidate",
                });
            };
            if !matches!(private.batch.engine.environment().find(&header.base.name),
                Some(ConstantInfo::Defn(definition)) if definition.base == header.base)
            {
                return Err(EngineExecutionError::UnexpectedPublication {
                    detail: "computed-field private body must preserve its source public signature",
                });
            }
        }
        let mut candidates = Vec::new();
        for row in &private.batch.admissions {
            let declaration = if let Declaration::Defn(definition) = &row.declaration
                && private.logical.contains(&definition.base.name)
                && !computed.exposes_getters()
            {
                Declaration::Axiom(AxiomVal {
                    base: definition.base.clone(),
                    is_unsafe: false,
                })
            } else {
                row.declaration.clone()
            };
            candidates.push(declaration);
        }
        let mut public =
            match public_prefix
                .engine
                .admit_declarations(&candidates, options, limits)?
            {
                Outcome::Complete(public) => public,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        for name in &private.logical {
            noncomputable(&mut public.engine, name)?;
        }
        for name in &private.irreducible {
            public.engine.environment = fln_elab::reducibility::register(
                public.engine.environment(),
                name,
                fln_elab::reducibility::Reducibility::Irreducible,
            )
            .map_err(|error| {
                frontend(SourceInferenceError::Unification(Box::new(
                    fln_elab::constraint::unify::UnificationError::Reducibility(error),
                )))
            })?;
        }
        implementation_cases_on_metadata(&mut public.engine, &computed.family)?;
        register_edges(&mut public.engine, &private.implemented_by)?;
        for name in &computed.protected_fields {
            public.engine.environment = tag_protected(&public.engine, name)?;
        }
        public.engine.environment =
            match computed_outcome(fln_elab::computed_fields::register_projected(
                public.engine.environment(),
                private.batch.engine.environment(),
                &computed.family,
                &computed.fields,
                &computed.inline_fields,
                limits.kernel,
                RecordBudget::default(),
            ))? {
                Outcome::Complete(environment) => environment,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        public.result_logical_root = public.engine.logical_root(options);
        Ok(Outcome::Complete(PublicSourceAdmission {
            public: public_body::prepend_auxiliaries(public, public_prefix),
            private_implementation: Some(public_body::prepend_auxiliaries(
                private.batch,
                private_prefix,
            )),
            metadata_complete: true,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SOURCE: &[u8] = b"inductive VisibilityCache where\n  | empty\n  | add (n : Nat) (tail : VisibilityCache)\nwith\n  @[computed_field, inline] total : VisibilityCache -> Nat\n    | .empty => 0\n    | .add n tail => Nat.add n tail.total";

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    #[test]
    fn raw_inductive_entry_does_not_publish_a_logical_only_computed_family() {
        let ScopedCommandSyntax::Definition(parsed) = parse_scoped_command(SOURCE).unwrap() else {
            panic!("computed family must parse as an inductive definition");
        };
        let environment = Environment::new();
        let result = fln_elab::source::scope::elaborate_inductive(
            parsed.syntax(),
            &environment,
            Budget::for_stack_bytes(2 * 1024 * 1024),
            RecordBudget::default(),
            &fln_elab::source::scope::SourceScope::default(),
        );
        assert!(
            matches!(
                result,
                Err(fln_elab::NatDefinitionElabError::UnexpectedSyntax {
                    expected: "unsupported computed inductive fields",
                })
            ),
            "{result:?}"
        );
        assert!(!environment.contains(&name("VisibilityCache")));
    }

    #[test]
    fn computed_public_getters_keep_private_bodies_and_export_real_overrides() {
        std::thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(|| {
            use crate::source_check::modules::SourceModuleCheckLimits;
            use crate::source_check::modules::imported::SourceOleanImportLimits;
            let library = std::env::var_os("FLN_REFERENCE_LIB")
                .map(std::path::PathBuf::from)
                .or_else(|| std::env::var_os("HOME").map(|home| std::path::PathBuf::from(home)
                    .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")))
                .filter(|path| path.join("Init/Prelude.olean").is_file());
            let Some(library) = library else {
                assert!(std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(), "computed visibility test requires the pinned Prelude fixture");
                eprintln!("SKIP: pinned Prelude fixture absent");
                return;
            };
            let path = library.join("Init/Prelude.olean");
            let artifacts = [
                std::fs::read(&path).unwrap(),
                std::fs::read(path.with_extension("olean.server")).unwrap(),
                std::fs::read(path.with_extension("olean.private")).unwrap(),
            ];
            let prelude = name("Init.Prelude");
            let imported = Engine::builder().build_empty().import_olean_modules_for_source(
                &[OleanModuleInput {
                    name: &prelude,
                    artifact: &artifacts[0],
                    server_artifact: Some(&artifacts[1]),
                    private_artifact: Some(&artifacts[2]),
                }],
                std::slice::from_ref(&prelude),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    64 * 1024 * 1024,
                    Budget::for_stack_bytes(64 * 1024 * 1024),
                )),
            ).unwrap().into_complete().unwrap();
            let mut source = b"module\nprelude\npublic import Init.Prelude\npublic section\n".to_vec();
            source.extend_from_slice(SOURCE);
            let module = name("ComputedVisibility");
            let kernel = Budget::for_stack_bytes(2 * 1024 * 1024);
            let checked = imported.check_source_modules(
                &[SourceModuleInput { name: &module, source: &source }],
                &module,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(kernel))),
                None,
            ).unwrap().into_complete().unwrap();
            let public = checked.public_environment.as_ref().expect("module public predecessor");
            let private = checked.checked.engine.environment();
            for getter in ["VisibilityCache.total", "VisibilityCache.total._sunfold"] {
                assert!(matches!(public.find(&name(getter)), Some(ConstantInfo::Axiom(header)) if !header.is_unsafe), "{getter} must expose only its signature");
                assert!(matches!(private.find(&name(getter)), Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe), "{getter} must retain its checked private body");
            }
            for generated in ["VisibilityCache.casesOn._override", "VisibilityCache.add._override", "VisibilityCache.total._override"] {
                let public_definition = public.find(&name(generated)).expect("public override");
                assert!(matches!(public_definition, ConstantInfo::Defn(definition) if definition.safety == DefinitionSafety::Unsafe));
                assert_eq!(private.find(&name(generated)), Some(public_definition));
            }
            assert!(matches!(public.find(&name("VisibilityCache._impl.casesOn")), Some(ConstantInfo::Defn(_))));
            assert!(!private.contains(&name("VisibilityCache.total._unsafe_rec")));
            assert!(fln_elab::computed_fields::families(public, RecordBudget::default()).unwrap().contains(&name("VisibilityCache")));
            assert!(fln_elab::computed_fields::validated_family(public, &name("VisibilityCache"), kernel, RecordBudget::default()).is_err(), "public getter headers cannot authorize cache execution");
            let model = fln_elab::computed_fields::validated_family(private, &name("VisibilityCache"), kernel, RecordBudget::default()).unwrap().unwrap();
            assert_eq!(model.inline_fields, vec![name("VisibilityCache.total")]);
        }).unwrap().join().unwrap();
    }
}
