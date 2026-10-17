//! Ordered, bounded logical witness search (the pin's MkInhabitant.lean).
//! A named function result may have its own inhabitant even when its codomain
//! does not. Try that result before opening binders hidden by a type alias.
use super::*;

impl Context {
    /// Synthesize WITHOUT the recursive local. Only the closed candidate and
    /// spent work escape this search; its providers and trial assignments do not.
    pub(super) fn partial_inhabitant(
        &mut self,
        type_: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let saved = self.clone();
        let result = self.partial_inhabitant_inner(type_);
        self.restore_inhabitant_trial(saved);
        result
    }

    fn restore_inhabitant_trial(&mut self, saved: Self) {
        let spent = self.txn.budget.heartbeats_consumed;
        let next = self.next;
        *self = saved;
        self.txn.budget.heartbeats_consumed = spent;
        // Trial-local names are never reused, including at a resource stop.
        self.next = next;
    }

    fn partial_inhabitant_inner(&mut self, type_: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let original_locals = self.txn.lctx.decls().len();
        // Like forallTelescope, not forallTelescopeReducing: the declaration's
        // syntactic binders are parameters, but a named result remains a target.
        let remaining = self.open_inhabitant_telescope(type_.clone())?;
        let strategy_start = self.clone();
        for components in [&["default"][..], &["Classical", "ofNonempty"][..]] {
            // Nonempty starts at the original result and providers, NOT at the
            // last codomain reached by a failed Inhabited search.
            self.restore_inhabitant_trial(strategy_start.clone());
            if !self
                .txn
                .env
                .contains(&Name::from_components(components.iter().copied()))
            {
                continue;
            }
            let syntax = Syntax::Ident {
                info: fln_syntax::source::SourceInfo::None,
                raw_val: fln_syntax::source::ByteSpan::default(),
                // A user's local or namespace named default cannot redirect an
                // elaborator support operation to a different declaration.
                val: Name::from_components(
                    std::iter::once("_root_").chain(components.iter().copied()),
                ),
                preresolved: Vec::new(),
            };
            let mut target = remaining.clone();
            loop {
                self.tick()?;
                let snapshot = self.clone();
                let attempt = self
                    .term(&syntax, Some(target.clone()))
                    .and_then(|term| self.finish(term));
                match attempt {
                    Ok(term) => return self.close_inhabitant_locals(term.value, original_locals),
                    Err(error)
                        if instances::nonmatch(&error)
                            || matches!(
                                error,
                                NatDefinitionElabError::Inference(
                                    SourceInferenceError::InstanceSynthesisRequired
                                        | SourceInferenceError::UnresolvedHoles { .. }
                                )
                            ) =>
                    {
                        self.restore_inhabitant_trial(snapshot)
                    }
                    // Exhaustion, broken metadata and kernel nonanswers are not
                    // proof that a different instance strategy should be tried.
                    Err(error) => return Err(error),
                }
                let reduced =
                    self.whnf_with_transparency(&target, UnificationTransparency::None, true)?;
                if matches!(reduced.node(), ExprNode::ForallE { .. }) {
                    target = self.open_inhabitant_telescope(reduced)?;
                } else if let Some(unfolded) = self.unfold_head_definition(&reduced)? {
                    // One alias per step retains intermediate instance targets.
                    // This existing reducer preserves opaque/irreducible and
                    // unsafe/partial barriers; it does not execute user code.
                    target = unfolded;
                } else {
                    break;
                }
            }
        }
        Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "an inhabited result type for partial def",
        })
    }

    /// Open one visible telescope and make its parameters Inhabited providers.
    /// Further aliases are deliberately left for the ordered strategy loop.
    fn open_inhabitant_telescope(
        &mut self,
        mut target: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut parameters = Vec::new();
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = target.node()
        {
            let id = FVarId(self.fresh_name()?);
            self.txn.lctx.add_param(
                id.clone(),
                binder_name.clone(),
                binder_type.clone(),
                *binder_info,
            );
            parameters.push(self.txn.lctx.find(&id).expect("inserted parameter").clone());
            target = self.substitute(body, &Expr::fvar(id))?;
        }
        for parameter in parameters {
            self.tick()?;
            let type_of_type = self
                .known_type(&parameter.type_)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let level = self.sort_level(&Typed {
                value: parameter.type_.clone(),
                type_: type_of_type,
            })?;
            let instance_type = Expr::app(
                Expr::const_(Name::from_components(["Inhabited"]), vec![level.clone()]),
                parameter.type_.clone(),
            );
            let instance_value = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_components(["Inhabited", "mk"]), vec![level]),
                    parameter.type_.clone(),
                ),
                Expr::fvar(parameter.id.clone()),
            );
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_let(id.clone(), id.0.clone(), instance_type, instance_value);
        }
        Ok(target)
    }

    fn close_inhabitant_locals(
        &mut self,
        mut value: Expr,
        original_locals: usize,
    ) -> Result<Expr, NatDefinitionElabError> {
        // Opening a hidden telescope interleaves new parameters with earlier
        // providers. Close in actual scope order, not as two disjoint lists.
        let locals = self.txn.lctx.decls()[original_locals..].to_vec();
        for local in locals.into_iter().rev() {
            self.tick()?;
            value = value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            let type_ = self.instantiate(&local.type_)?;
            value = match local.value {
                Some(provider) => Expr::let_e(
                    local.user_name,
                    type_,
                    self.instantiate(&provider)?,
                    value,
                    false,
                ),
                None => Expr::lam(local.user_name, type_, value, local.binder_info),
            };
        }
        self.require_resolved(&[value.clone()])?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::outcome::Outcome;
    use fln_kernel::verdict::Verdict;

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn fixture() -> Environment {
        use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
        use fln_env::pmap::CollisionBudget;
        use fln_kernel::capability::{Published, admit};
        use fln_kernel::council::{Council, CouncilOutcome, convene};
        use std::sync::OnceLock;

        static BASE: OnceLock<Environment> = OnceLock::new();
        BASE.get_or_init(|| {
            let mut env = Environment::new();
            // Ordinary K1 admission supplies the unit fixture. The separate
            // source integration tests exercise the complete dual-checker door.
            for declaration in crate::seed::source_seed_declarations() {
                let Outcome::Complete(admitted) = admit(&env, declaration, Budget::DEFAULT) else {
                    panic!("seed admission must complete")
                };
                let CouncilOutcome::Agreed(checked) =
                    convene(&Council::nobody_was_asked(), admitted)
                else {
                    panic!("the seed declaration must be accepted")
                };
                env = match checked.publish(
                    DeclarationBudget::default(),
                    CollisionBudget::default(),
                    None,
                ) {
                    Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                        publication,
                    ))) => publication.environment,
                    Outcome::Complete(Published::BlockCommitted(publication)) => {
                        publication.environment
                    }
                    other => panic!("seed publication: {other:?}"),
                };
            }
            crate::instances::register_class(&env, &n("Inhabited")).unwrap()
        })
        .clone()
    }

    fn polymorphic_identity() -> Expr {
        Expr::forall_e(
            n("A"),
            Expr::sort(Level::one()),
            Expr::forall_e(
                n("x"),
                Expr::bvar(0).unwrap(),
                Expr::bvar(1).unwrap(),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        )
    }

    fn context(env: &Environment) -> Context {
        let mut context = Context::new(env, Budget::DEFAULT);
        context.txn.lctx.add_param(
            FVarId(n("outer")),
            n("outer"),
            Expr::const_(n("Nat"), vec![]),
            BinderInfo::Default,
        );
        context
    }

    #[test]
    fn every_inhabitant_budget_stop_restores_the_original_transaction() {
        let env = fixture();
        let type_ = polymorphic_identity();
        let mut complete = context(&env);
        let mut saved = complete.txn.clone();
        let value = complete.partial_inhabitant(&type_).unwrap();
        let spent = complete.txn.budget.heartbeats_consumed;
        assert!(
            spent > 10,
            "the parameter providers must actually be checked"
        );
        saved.budget.heartbeats_consumed = spent;
        assert_eq!(complete.txn, saved);
        assert!(complete.next > 0);
        assert!(matches!(
            fln_kernel::check(
                &env,
                &Declaration::Opaque(fln_env::constants::OpaqueVal {
                    base: ConstantVal {
                        name: n("checkedWitness"),
                        level_params: vec![],
                        type_,
                    },
                    value,
                    is_unsafe: false,
                    all: vec![n("checkedWitness")],
                }),
                Budget::DEFAULT,
            ),
            Outcome::Complete(Verdict::Accepted { .. })
        ));
        for allowance in 1..spent {
            let mut limited = context(&env);
            limited.txn.budget.max_heartbeats = allowance;
            let mut saved = limited.txn.clone();
            let result = limited.partial_inhabitant(&polymorphic_identity());
            let stopped = matches!(
                &result,
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ResourceLimit
                ))
            ) || matches!(
                &result,
                Err(NatDefinitionElabError::Inference(SourceInferenceError::Unification(error)))
                    if matches!(error.as_ref(), UnificationError::HeartbeatLimit)
            );
            assert!(stopped, "allowance {allowance}: {result:?}");
            saved.budget.heartbeats_consumed = limited.txn.budget.heartbeats_consumed;
            assert_eq!(limited.txn, saved, "allowance {allowance}");
            assert!(limited.txn.budget.heartbeats_consumed >= allowance);
        }
    }

    #[test]
    fn an_uninhabited_result_does_not_leak_trial_providers_into_the_next_search() {
        let env = fixture();
        let mut context = context(&env);
        let mut saved = context.txn.clone();
        let impossible = Expr::forall_e(
            n("n"),
            Expr::const_(n("Nat"), vec![]),
            Expr::const_(n("False"), vec![]),
            BinderInfo::Default,
        );
        assert!(matches!(
            context.partial_inhabitant(&impossible),
            Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "an inhabited result type for partial def"
            })
        ));
        saved.budget.heartbeats_consumed = context.txn.budget.heartbeats_consumed;
        assert_eq!(context.txn, saved);
        let prior_next = context.next;
        let prior_spent = context.txn.budget.heartbeats_consumed;
        let value = context.partial_inhabitant(&polymorphic_identity()).unwrap();
        assert!(!value.has_fvar());
        assert!(!value.has_loose_bvars());
        assert!(context.next > prior_next);
        assert!(context.txn.budget.heartbeats_consumed > prior_spent);
        saved.budget.heartbeats_consumed = context.txn.budget.heartbeats_consumed;
        assert_eq!(context.txn, saved);
    }
}
