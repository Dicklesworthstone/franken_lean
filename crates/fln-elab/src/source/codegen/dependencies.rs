//! The compiler's noncomputable boundary, after erasing proofs and type formers.
//! A successful table is private to one check in one immutable environment.
//! Explicit implementation selection comes before the noncomputable test; extern
//! metadata exempts a declaration but never authorizes execution of native code.
use super::*;
use crate::externs::{ExternReadError, ExternTable};
use crate::implemented_by::{ImplementedByReadError, ImplementedByTable};

#[derive(Default)]
pub(super) struct Dependencies {
    names: BTreeSet<Name>,
    implemented_by: ImplementedByTable,
    externs: ExternTable,
}

impl Dependencies {
    pub(super) fn read(context: &mut Context) -> Result<Self, NatDefinitionElabError> {
        // Hold the same immutable snapshot across all three reads. Charge row
        // visits and payload bytes before the decoder can allocate their names.
        let env = context.txn.env.clone();
        let Some(extension) = env.extension(&crate::noncomputable::journal_name()) else {
            return Ok(Self::default());
        };
        let mut charge = |amount| {
            for _ in 0..amount {
                context.tick()?;
            }
            Ok(())
        };
        charge(extension.len())?;
        for entry in extension.entries() {
            charge(entry.payload.len())?;
        }
        let names = crate::noncomputable::read(&env).map_err(|error| match error {
            crate::noncomputable::NoncomputableError::Limit => {
                failure(SourceInferenceError::ResourceLimit)
            }
            other => failure(SourceInferenceError::NoncomputableJournal(other)),
        })?;
        if names.is_empty() {
            return Ok(Self::default());
        }
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
        Ok(Self {
            names,
            implemented_by,
            externs,
        })
    }

    pub(super) fn is_empty(&self) -> bool {
        self.names.is_empty()
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
        if (self.names.contains(selected) || self.names.contains(&implementation))
            && self.externs.get(selected).is_none()
        {
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
    fn environment() -> fln_env::environment::Environment {
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
    fn term(name: &str) -> Typed {
        Typed {
            type_: Expr::const_(n("Nat"), vec![]),
            value: Expr::const_(n(name), vec![]),
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
