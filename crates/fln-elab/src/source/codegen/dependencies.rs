//! The compiler's noncomputable boundary, after erasing proofs and type formers.
//! A successful table is private to one check in one immutable environment.
//! Explicit implementation selection comes before the noncomputable test; extern
//! metadata exempts a declaration but never authorizes execution of native code.
use super::*;
use crate::externs::{ExternReadError, ExternTable};
use crate::implemented_by::{ImplementedByReadError, ImplementedByTable};

#[cfg(test)]
mod computability_tests;
mod well_founded;

#[derive(Default)]
pub(super) struct Dependencies {
    environment: fln_env::environment::Environment,
    names: BTreeSet<Name>,
    implemented_by: ImplementedByTable,
    externs: ExternTable,
    macro_inline: BTreeSet<Name>,
    well_founded: well_founded::Cache,
}

impl Dependencies {
    pub(super) fn read(context: &mut Context) -> Result<Self, NatDefinitionElabError> {
        // Hold the same immutable snapshot across the journal reads. Charge row
        // visits and payload bytes before the decoder can allocate their names.
        let logical = context.txn.env.clone();
        let provider = context.source_scope.computability.clone();
        let mut charge = |amount| {
            for _ in 0..amount {
                context.tick()?;
            }
            Ok(())
        };
        // Exported axioms can have independently checked imported code. The
        // compiler's isolated view includes those bodies and the current local
        // metadata suffix; typing, erasure and name resolution still use the
        // unchanged logical transaction. Refresh on every read, including the
        // admitted successor of a deferred partial-definition group.
        let env = match provider {
            Some(provider) => provider.0.environment(&logical, &mut charge)?,
            None => logical,
        };
        if let Some(extension) = env.extension(&crate::noncomputable::journal_name()) {
            charge(extension.len())?;
            for entry in extension.entries() {
                charge(entry.payload.len())?;
            }
        }
        let names = crate::noncomputable::read(&env).map_err(|error| match error {
            crate::noncomputable::NoncomputableError::Limit => {
                failure(SourceInferenceError::ResourceLimit)
            }
            other => failure(SourceInferenceError::NoncomputableJournal(other)),
        })?;
        // An empty tag journal does not make an axiom executable. Read the
        // implementation intentions as well, including their failure/budget
        // checks, even when no definition has failed compilation yet.
        let implemented_by =
            ImplementedByTable::read_metered(&env, &mut charge).map_err(|error| match error {
                ImplementedByReadError::Budget(error) => error,
                ImplementedByReadError::Registry(
                    crate::implemented_by::ImplementedByError::Limit,
                ) => failure(SourceInferenceError::ResourceLimit),
                ImplementedByReadError::Registry(error) => {
                    failure(SourceInferenceError::ImplementedByJournal(error))
                }
            })?;
        let externs =
            ExternTable::read_metered(&env, &mut charge).map_err(|error| match error {
                ExternReadError::Budget(error) => error,
                ExternReadError::Registry(crate::externs::ExternError::Limit) => {
                    failure(SourceInferenceError::ResourceLimit)
                }
                ExternReadError::Registry(error) => {
                    failure(SourceInferenceError::ExternJournal(error))
                }
            })?;
        if let Some(extension) = env.extension(&crate::macro_inline::journal_name()) {
            charge(extension.len())?;
            for entry in extension.entries() {
                charge(entry.payload.len())?;
            }
        }
        let macro_inline = crate::macro_inline::read(&env).map_err(|error| match error {
            crate::macro_inline::MacroInlineError::Limit => {
                failure(SourceInferenceError::ResourceLimit)
            }
            error => failure(SourceInferenceError::MacroInlineJournal(error)),
        })?;
        Ok(Self {
            environment: env,
            names,
            implemented_by,
            externs,
            macro_inline,
            well_founded: well_founded::Cache::default(),
        })
    }

    /// LCNF.macroInline precedes executable dependency checking: instantiate
    /// the tagged body's universes and beta-reduce its unevaluated arguments.
    /// This grants no unfolding to an ordinary definition or logical reducer.
    pub(super) fn expand_macro_inline(
        &self,
        context: &mut Context,
        declaration: &Name,
        levels: &[Level],
        arguments: &[Expr],
        named: &[Name],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        if !self.macro_inline.contains(declaration) {
            return Ok(None);
        }
        let Some(ConstantInfo::Defn(definition)) = self.environment.find(declaration) else {
            return Err(failure(SourceInferenceError::MacroInlineJournal(
                crate::macro_inline::MacroInlineError::NotADefinition(declaration.clone()),
            )));
        };
        if definition.base.level_params.len() != levels.len() {
            return Err(failure(SourceInferenceError::Scope));
        }
        let mut body =
            context.instantiate_params(&definition.value, &definition.base.level_params, levels)?;
        let mut rest = arguments.iter();
        for argument in rest.by_ref() {
            context.tick()?;
            let argument = context.mark_source_recursors(argument, named)?;
            while let ExprNode::MData { data, expr } = body.node() {
                if context.has_source_rec_provenance(data)? {
                    break;
                }
                context.tick()?;
                body = expr.clone();
            }
            let ExprNode::Lam { body: next, .. } = body.node() else {
                body = Expr::app(body, argument);
                break;
            };
            body = context.substitute(next, &argument)?;
        }
        for argument in rest {
            context.tick()?;
            body = Expr::app(body, context.mark_source_recursors(argument, named)?);
        }
        Ok(Some(body))
    }

    /// Check the terminal executable dependency without rewriting the checked term.
    /// Ordinary heads retain their existing fast path and metadata semantics.
    pub(super) fn check_compiled(
        &mut self,
        context: &mut Context,
        declaration: &Name,
    ) -> Result<(), NatDefinitionElabError> {
        let requested = self
            .implemented_by
            .implementation(declaration)
            .unwrap_or(declaration);
        if !well_founded::recognizes(requested) {
            return self.check(declaration);
        }
        let (selected, staged) = self.well_founded.resolve(
            context,
            &self.environment,
            &self.implemented_by,
            &self.externs,
            requested,
        )?;
        self.check(&selected)?;
        self.well_founded = staged;
        Ok(())
    }

    /// Projection erasure cannot borrow a logical field body's semantics when
    /// another executable implementation (including a companion) was selected.
    pub(super) fn has_runtime_override(&self, declaration: &Name) -> bool {
        self.implemented_by.get(declaration).is_some()
            || self.externs.get(declaration).is_some()
            || self
                .environment
                .contains(&Name::str(declaration.clone(), "_unsafe_rec"))
    }

    pub(super) fn check(&self, declaration: &Name) -> Result<(), NatDefinitionElabError> {
        let selected = self
            .implemented_by
            .implementation(declaration)
            .unwrap_or(declaration);
        // ToLCNF.checkComputable also inspects the recursive executable sibling:
        // a tolerated compiler failure can tag only that implementation, not
        // the logical declaration. This is an exact Name child, never a display
        // string suffix (mkUnsafeRecName in the pinned Compiler/Old.lean).
        let implementation = Name::str(selected.clone(), "_unsafe_rec");
        if self.externs.get(selected).is_some() {
            return Ok(());
        }
        if self.names.contains(selected) || self.names.contains(&implementation) {
            return Err(failure(SourceInferenceError::NoncomputableDependency(
                selected.clone(),
            )));
        }
        let unavailable = match self.environment.find(selected) {
            Some(ConstantInfo::Axiom(actual)) => {
                // The bounded source seed represents some native intrinsics
                // as axioms. Reuse its exact candidate, not a name or a type
                // shape allowlist. Native ABI authorization still belongs to
                // the existing runtime bridge, not this compiler check.
                let candidate = crate::seed::source_intrinsic_seed_declaration(selected)
                    .or_else(|| crate::seed::float_intrinsic_seed_declaration(selected));
                !matches!(candidate, Some(Declaration::Axiom(expected)) if actual == &expected)
            }
            Some(ConstantInfo::Quot(value)) => !matches!(
                value.kind,
                fln_env::constants::QuotKind::Ctor | fln_env::constants::QuotKind::Lift
            ),
            Some(ConstantInfo::Induct(_) | ConstantInfo::Thm(_)) => true,
            _ => false,
        };
        if unavailable {
            return Err(failure(SourceInferenceError::NoncomputableDependency(
                selected.clone(),
            )));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};

    fn n(s: &str) -> Name {
        Name::from_components(s.split('.'))
    }
    pub(super) fn environment() -> fln_env::environment::Environment {
        let mut env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
        for name in ["hidden", "usable", "alternate"] {
            env = env
                .add_decl(ConstantInfo::Defn(DefinitionVal {
                    base: ConstantVal {
                        name: n(name),
                        level_params: vec![],
                        type_: Expr::const_(n("Nat"), vec![]),
                    },
                    value: Expr::lit(fln_core::expr::Literal::Nat(
                        fln_core::expr::NatLit::from_u64(7),
                    )),
                    hints: ReducibilityHints::Abbrev,
                    safety: DefinitionSafety::Safe,
                    all: vec![],
                }))
                .unwrap();
        }
        crate::noncomputable::register(&env, &n("hidden")).unwrap()
    }
    pub(super) fn term(name: &str) -> Typed {
        Typed {
            type_: Expr::const_(n("Nat"), vec![]),
            value: Expr::const_(n(name), vec![]),
        }
    }

    pub(super) fn axiom_environment() -> fln_env::environment::Environment {
        let env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
        env.add_decl(ConstantInfo::Axiom(fln_env::constants::AxiomVal {
            base: ConstantVal {
                name: n("bodyless"),
                level_params: vec![],
                type_: Expr::const_(n("Nat"), vec![]),
            },
            is_unsafe: false,
        }))
        .unwrap()
    }

    fn definition(
        env: &fln_env::environment::Environment,
        label: &str,
        type_: Expr,
        value: Expr,
    ) -> fln_env::environment::Environment {
        env.add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: n(label),
                level_params: vec![],
                type_,
            },
            value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![n(label)],
        }))
        .unwrap()
    }

    #[test]
    fn macro_inline_expansion_checks_bodies_and_only_surviving_arguments() {
        let nat = Expr::const_(n("Nat"), vec![]);
        let bodyless = Expr::const_(n("bodyless"), vec![]);
        let base = axiom_environment();
        let bare = definition(&base, "inlineValue", nat.clone(), bodyless.clone());
        let bare = crate::macro_inline::register(&bare, &n("inlineValue")).unwrap();
        assert!(matches!(
            Context::new(&bare, Budget::DEFAULT)
                .check_definition_codegen(&term("inlineValue")),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::NoncomputableDependency(name)
            )) if name == n("bodyless")
        ));

        let type_ = Expr::forall_e(n("unused"), nat.clone(), nat.clone(), BinderInfo::Default);
        let value = Expr::lam(
            n("unused"),
            nat.clone(),
            Expr::lit(fln_core::expr::Literal::Nat(
                fln_core::expr::NatLit::from_u64(7),
            )),
            BinderInfo::Default,
        );
        let ordinary = definition(&base, "discard", type_, value);
        let tagged = crate::macro_inline::register(&ordinary, &n("discard")).unwrap();
        let application = Typed {
            type_: nat,
            value: Expr::app(Expr::const_(n("discard"), vec![]), bodyless),
        };
        assert_eq!(
            Context::new(&tagged, Budget::DEFAULT).check_definition_codegen(&application),
            Ok(false)
        );
        assert!(matches!(
            Context::new(&ordinary, Budget::DEFAULT).check_definition_codegen(&application),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::NoncomputableDependency(name)
            )) if name == n("bodyless")
        ));
    }

    #[test]
    fn macro_inline_metadata_and_cyclic_expansion_never_become_success() {
        let nat = Expr::const_(n("Nat"), vec![]);
        let body = Expr::let_e(
            n("unused"),
            nat.clone(),
            Expr::const_(n("Nat.zero"), vec![]),
            Expr::const_(n("inlineCycle"), vec![]),
            false,
        );
        // Source admission forbids recursive macro-inline definitions. This
        // deliberately forged table still cannot pass by revisiting a seen let.
        let env = definition(&axiom_environment(), "inlineCycle", nat, body);
        let env = crate::macro_inline::register(&env, &n("inlineCycle")).unwrap();
        let mut context = Context::new(&env, Budget::DEFAULT);
        context.txn.budget.max_heartbeats = 512;
        context.source_scope.noncomputable_section = true;
        let locals = context.txn.lctx.clone();
        assert!(matches!(
            context.check_definition_codegen(&term("inlineCycle")),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert_eq!(context.txn.lctx, locals);
        assert_eq!(context.txn.env, env);

        let broken = env
            .push_extension_entry(&crate::macro_inline::journal_name(), b"bad".to_vec())
            .unwrap();
        let mut context = Context::new(&broken, Budget::DEFAULT);
        context.source_scope.noncomputable_section = true;
        assert!(matches!(
            context.check_definition_codegen(&term("inlineCycle")),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::MacroInlineJournal(_)
            ))
        ));
    }

    #[test]
    fn bodyless_axioms_require_code_even_without_a_tag_journal() {
        let env = axiom_environment();
        assert!(
            env.extension(&crate::noncomputable::journal_name())
                .is_none()
        );
        let mut context = Context::new(&env, Budget::DEFAULT);
        assert!(
            matches!(context.check_definition_codegen(&term("bodyless")),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::NoncomputableDependency(name)))
            if name == n("bodyless"))
        );
        context.source_scope.noncomputable_section = true;
        assert_eq!(
            context.check_definition_codegen(&term("bodyless")),
            Ok(true)
        );
        assert_eq!(context.txn.env, env);
    }

    #[test]
    fn untagged_axiom_implementations_and_externs_are_validated_before_exemption() {
        let base = axiom_environment();
        let extern_ = crate::externs::register(
            &base,
            &n("bodyless"),
            vec![crate::externs::ExternEntry::Opaque],
        )
        .unwrap();
        assert_eq!(
            Context::new(&extern_, Budget::DEFAULT).check_definition_codegen(&term("bodyless")),
            Ok(false)
        );
        let actual = base
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n("actual"),
                    level_params: vec![],
                    type_: Expr::const_(n("Nat"), vec![]),
                },
                value: Expr::lit(fln_core::expr::Literal::Nat(
                    fln_core::expr::NatLit::from_u64(7),
                )),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![n("actual")],
            }))
            .unwrap();
        let replaced =
            crate::implemented_by::register(&actual, &n("bodyless"), &n("actual")).unwrap();
        assert_eq!(
            Context::new(&replaced, Budget::DEFAULT).check_definition_codegen(&term("bodyless")),
            Ok(false)
        );
        for (env, journal) in [
            (extern_, crate::externs::journal_name()),
            (replaced, crate::implemented_by::journal_name()),
        ] {
            assert!(
                env.extension(&crate::noncomputable::journal_name())
                    .is_none()
            );
            let damaged = env.push_extension_entry(&journal, b"bad".to_vec()).unwrap();
            let mut context = Context::new(&damaged, Budget::DEFAULT);
            context.source_scope.noncomputable_section = true;
            assert!(matches!(
                context.check_definition_codegen(&term("bodyless")),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ExternJournal(_)
                        | SourceInferenceError::ImplementedByJournal(_)
                ))
            ));
            assert_eq!(context.txn.env, damaged);
        }
    }

    #[test]
    fn native_seed_exceptions_require_exact_declarations_and_do_not_override_tags() {
        for name in [n("Nat.beq"), n("String.length"), n("Float.sqrt")] {
            let Some(Declaration::Axiom(candidate)) =
                crate::seed::source_intrinsic_seed_declaration(&name)
                    .or_else(|| crate::seed::float_intrinsic_seed_declaration(&name))
            else {
                panic!("seed axiom")
            };
            let original = ConstantInfo::Axiom(candidate.clone());
            let env = fln_env::environment::Environment::new()
                .add_decl(original)
                .unwrap();
            let table = Dependencies::read(&mut Context::new(&env, Budget::DEFAULT)).unwrap();
            table.check(&name).unwrap();
            // Full equality includes safety and the complete telescope. A
            // same-name declaration with another type is no native primitive.
            let mut altered = candidate;
            altered.base.type_ = Expr::sort(Level::one());
            let changed = fln_env::environment::Environment::new()
                .add_decl(ConstantInfo::Axiom(altered))
                .unwrap();
            assert!(
                Dependencies::read(&mut Context::new(&changed, Budget::DEFAULT))
                    .unwrap()
                    .check(&name)
                    .is_err()
            );
            table.check(&name).unwrap(); // Another snapshot cannot change this view.
            let tagged = crate::noncomputable::register(&env, &name).unwrap();
            assert!(
                Dependencies::read(&mut Context::new(&tagged, Budget::DEFAULT))
                    .unwrap()
                    .check(&name)
                    .is_err()
            );
        }
    }

    #[test]
    fn bodyless_analysis_restores_context_at_every_budget_boundary() {
        let env = axiom_environment();
        let mut full = Context::new(&env, Budget::DEFAULT);
        full.source_scope.noncomputable_section = true;
        assert_eq!(full.check_definition_codegen(&term("bodyless")), Ok(true));
        for allowance in 1..full.txn.budget.heartbeats_consumed {
            let mut context = Context::new(&env, Budget::DEFAULT);
            context.source_scope.noncomputable_section = true;
            context.txn.budget.max_heartbeats = allowance;
            let locals = context.txn.lctx.clone();
            assert!(matches!(
                context.check_definition_codegen(&term("bodyless")),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ResourceLimit
                ))
            ));
            assert_eq!(context.txn.env, env);
            assert_eq!(context.txn.lctx, locals);
        }
    }

    #[test]
    fn replacement_chains_select_the_terminal_before_testing_noncomputability() {
        let env = environment();
        let safe = crate::implemented_by::register(&env, &n("hidden"), &n("usable")).unwrap();
        let dependencies = Dependencies::read(&mut Context::new(&safe, Budget::DEFAULT)).unwrap();
        dependencies.check(&n("hidden")).unwrap();
        let chain = crate::implemented_by::register(&env, &n("usable"), &n("alternate")).unwrap();
        let chain = crate::implemented_by::register(&chain, &n("alternate"), &n("hidden")).unwrap();
        let mut context = Context::new(&chain, Budget::DEFAULT);
        assert!(matches!(context.check_definition_codegen(&term("usable")),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::NoncomputableDependency(name))) if name == n("hidden")));
        context.source_scope.noncomputable_section = true;
        assert_eq!(context.check_definition_codegen(&term("usable")), Ok(true));
    }

    #[test]
    fn explicit_extern_intention_exempts_only_its_exact_selected_declaration() {
        let env = environment();
        let env = crate::externs::register(
            &env,
            &n("hidden"),
            vec![crate::externs::ExternEntry::Opaque],
        )
        .unwrap();
        let mut context = Context::new(&env, Budget::DEFAULT);
        assert_eq!(context.check_definition_codegen(&term("hidden")), Ok(false));
        // This check has no VM/catalog capability and grants none: it leaves
        // both the logical value and its noncomputable metadata unchanged.
        assert_eq!(context.txn.env, env);
        assert!(
            crate::noncomputable::read(&env)
                .unwrap()
                .contains(&n("hidden"))
        );
        let other = crate::noncomputable::register(&env, &n("alternate")).unwrap();
        assert!(
            matches!(Context::new(&other, Budget::DEFAULT).check_definition_codegen(&term("alternate")),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::NoncomputableDependency(name))) if name == n("alternate"))
        );
    }

    #[test]
    fn malformed_noncomputable_extern_and_replacement_journals_never_become_suppressed_failures() {
        let env = environment();
        let with_extern = crate::externs::register(
            &env,
            &n("hidden"),
            vec![crate::externs::ExternEntry::Opaque],
        )
        .unwrap();
        let with_replacement =
            crate::implemented_by::register(&env, &n("hidden"), &n("usable")).unwrap();
        let fixtures = [
            (env.clone(), crate::noncomputable::journal_name()),
            (with_extern, crate::externs::journal_name()),
            (with_replacement, crate::implemented_by::journal_name()),
        ];
        for (env, journal) in fixtures {
            let env = env
                .push_extension_entry(&journal, b"broken".to_vec())
                .unwrap();
            let mut context = Context::new(&env, Budget::DEFAULT);
            context.source_scope.noncomputable_section = true;
            for _ in 0..2 {
                assert!(matches!(
                    context.check_definition_codegen(&term("usable")),
                    Err(NatDefinitionElabError::Inference(
                        SourceInferenceError::NoncomputableJournal(_)
                            | SourceInferenceError::ExternJournal(_)
                            | SourceInferenceError::ImplementedByJournal(_)
                    ))
                ));
                assert_eq!(context.txn.env, env);
            }
        }
    }

    #[test]
    fn every_metadata_and_traversal_budget_stop_remains_a_nonanswer_in_a_section() {
        let env = environment();
        let make_context = || {
            let mut context = Context::new(&env, Budget::DEFAULT);
            context.source_scope.noncomputable_section = true;
            context
        };
        let mut full = make_context();
        assert_eq!(full.check_definition_codegen(&term("hidden")), Ok(true));
        let consumed = full.txn.budget.heartbeats_consumed;
        assert!(consumed > 10);
        for allowance in 1..consumed {
            let mut context = make_context();
            let saved = context.txn.lctx.clone();
            context.txn.budget.max_heartbeats = allowance;
            assert!(
                matches!(
                    context.check_definition_codegen(&term("hidden")),
                    Err(NatDefinitionElabError::Inference(
                        SourceInferenceError::ResourceLimit
                    ))
                ),
                "{allowance}"
            );
            assert_eq!(context.txn.env, env);
            assert_eq!(context.txn.lctx, saved);
        }
    }

    #[test]
    fn native_registry_capacity_limits_remain_resource_stops_in_sections() {
        let env = environment();
        let with_extern = crate::externs::register(
            &env,
            &n("hidden"),
            vec![crate::externs::ExternEntry::Opaque],
        )
        .unwrap();
        let with_replacement =
            crate::implemented_by::register(&env, &n("hidden"), &n("usable")).unwrap();
        for (env, journal) in [
            (env, crate::noncomputable::journal_name()),
            (with_extern, crate::externs::journal_name()),
            (with_replacement, crate::implemented_by::journal_name()),
        ] {
            let env = env.push_extension_entry(&journal, vec![0; 65_537]).unwrap();
            let mut context = Context::new(&env, Budget::DEFAULT);
            context.source_scope.noncomputable_section = true;
            assert!(matches!(
                context.check_definition_codegen(&term("usable")),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ResourceLimit
                ))
            ));
            assert_eq!(context.txn.env, env);
        }
    }

    #[test]
    fn recursive_implementation_tags_bind_structural_names_not_display_suffixes() {
        let env = environment();
        let value = env.find(&n("usable")).unwrap();
        let ConstantInfo::Defn(value) = value else {
            panic!("fixture definition")
        };
        let with_name = |name: Name| {
            let mut value = value.clone();
            value.base.name = name.clone();
            crate::noncomputable::register(&env.add_decl(ConstantInfo::Defn(value)).unwrap(), &name)
                .unwrap()
        };
        let lookalike = with_name(Name::from_components(["usable._unsafe_rec"]));
        assert_eq!(
            Context::new(&lookalike, Budget::DEFAULT).check_definition_codegen(&term("usable")),
            Ok(false)
        );
        let actual = with_name(Name::str(n("usable"), "_unsafe_rec"));
        let mut context = Context::new(&actual, Budget::DEFAULT);
        assert!(matches!(context.check_definition_codegen(&term("usable")),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::NoncomputableDependency(name))) if name == n("usable")));
        context.source_scope.noncomputable_section = true;
        assert_eq!(context.check_definition_codegen(&term("usable")), Ok(true));
    }
}
