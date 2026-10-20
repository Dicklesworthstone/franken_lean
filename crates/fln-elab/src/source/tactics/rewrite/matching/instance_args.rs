//! Simp theorem parameters are matched before instance search (the pinned
//! Lean.Meta.Tactic.Simp.Rewrite.synthesizeArgs). A failed dictionary search
//! rejects only this rule trial; interruption and faults remain terminal.
use super::*;
use crate::instances::{InstanceRegistry, result_head};
use crate::source::instances::{SearchResult, registry_error};

impl Context {
    pub(super) fn synthesize_simp_rule_instances(
        &mut self,
        holes: &[MVarId],
        instances: &[MVarId],
    ) -> Result<bool, NatDefinitionElabError> {
        let skip_assigned = self.txn.options.get_bool(
            &Name::from_components(["tactic", "skipAssignedInstances"]),
            true,
        );
        let mut registry = None;
        for id in holes {
            self.tick()?;
            // Caller-owned synthetic obligations retain their original owner
            // and opacity. Only this theorem's fresh parameters are patterns.
            if self.instance_goals.contains(id) {
                continue;
            }
            let recheck = !skip_assigned && instances.contains(id);
            let argument = self.instantiate(&Expr::mvar(id.clone()))?;
            if !matches!(argument.node(), ExprNode::MVar { .. }) && !recheck {
                continue;
            }
            let declaration = self
                .txn
                .mvars
                .get_decl(id)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let raw = declaration.type_.clone();
            let type_ = self.instantiate(&raw)?;
            let type_ =
                self.whnf_with_transparency(&type_, UnificationTransparency::Abbreviations, false)?;
            if registry.is_none() {
                registry = Some(
                    self.registry_cache
                        .read_with_scopes(&self.txn.env, &self.source_scope.instance_scopes)
                        .map_err(registry_error)?,
                );
            }
            let registry = registry.as_ref().expect("registry initialized above");
            if !result_head(&type_).is_some_and(|class| registry.is_class(&class)) {
                if recheck {
                    return Ok(false);
                }
                continue;
            }
            let solved = self.synthesize_simp_dictionary(id, type_, registry)?;
            if !solved && recheck {
                return Ok(false);
            }
            // Unsolved proof-valued classes still reach simp's discharger.
            // Ordinary data holes must remain unassigned and cannot be guessed.
        }
        Ok(true)
    }

    fn synthesize_simp_dictionary(
        &mut self,
        id: &MVarId,
        type_: Expr,
        registry: &InstanceRegistry,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut trial = self.rewrite_trial();
        let result = (|| {
            let locals = trial.txn.lctx.clone();
            let suspended = std::mem::take(&mut trial.equations);
            // Search a fresh goal even for an assigned parameter. Searching the
            // old goal would validate itself and ignore skipAssignedInstances.
            let fresh = trial.hole(type_)?;
            let ExprNode::MVar { id: goal } = fresh.node() else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if trial.search_instance(goal.clone(), registry)? != SearchResult::Solved {
                return Ok(false);
            }
            let value = trial.instantiate(&fresh)?;
            trial.txn.lctx = locals;
            trial.equations = suspended;
            let target = trial.instantiate(&Expr::mvar(id.clone()))?;
            let mut budget = UnificationBudget::new(trial.kernel);
            budget.transparency = UnificationTransparency::Instances;
            trial
                .txn
                .unify_many_with(&[(target, value)], budget, &|| false)
                .map_err(|error| failure(SourceInferenceError::Unification(Box::new(error))))?;
            Ok(true)
        })();
        self.charge_rewrite_trial(&trial);
        match result {
            Ok(true) => {
                *self = trial;
                Ok(true)
            }
            Ok(false) => Ok(false),
            Err(error) if crate::source::instances::nonmatch(&error) => Ok(false),
            Err(error) => Err(error),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};

    fn name(label: &str) -> Name {
        Name::from_components([label])
    }
    fn context() -> Context {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let mut env = Environment::new();
        for declaration in crate::records::record_declarations(
            &crate::records::RecordSpec {
                name: name("Dictionary"),
                level_params: vec![],
                parameters: vec![],
                fields: vec![],
                result_level: Level::one(),
                is_class: true,
            },
            Default::default(),
        )
        .unwrap()
        {
            let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
                panic!("admission stopped");
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("class rejected");
            };
            env = match checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) {
                Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
                    p.environment
                }
                Outcome::Complete(Published::BlockCommitted(p)) => p.environment,
                other => panic!("publication {other:?}"),
            };
        }
        env = crate::instances::register_class(&env, &name("Dictionary")).unwrap();
        Context::new(&env, budget)
    }
    fn class() -> Expr {
        Expr::const_(name("Dictionary"), vec![])
    }
    fn local(ctx: &mut Context) -> Expr {
        let id = FVarId(name("available"));
        ctx.txn
            .lctx
            .add_param(id.clone(), id.0.clone(), class(), BinderInfo::InstImplicit);
        Expr::fvar(id)
    }
    fn hole(ctx: &mut Context) -> (MVarId, Expr) {
        let expression = ctx.hole(class()).unwrap();
        let ExprNode::MVar { id } = expression.node() else {
            panic!("hole");
        };
        (id.clone(), expression)
    }
    fn unchanged(ctx: &Context, before: &Context) {
        assert_eq!(ctx.txn.mvars, before.txn.mvars);
        assert_eq!(ctx.txn.universes, before.txn.universes);
        assert_eq!(ctx.txn.lctx, before.txn.lctx);
        assert_eq!(ctx.txn.env, before.txn.env);
        assert_eq!(ctx.instance_goals, before.instance_goals);
        assert_eq!(ctx.equations.len(), before.equations.len());
        for (actual, expected) in ctx.equations.iter().zip(&before.equations) {
            assert_eq!(actual.sides, expected.sides);
        }
    }
    #[test]
    fn failed_instance_search_retains_cost_but_no_speculative_state() {
        let mut ctx = context();
        let (id, _) = hole(&mut ctx);
        let before = ctx.clone();
        let registry = InstanceRegistry::read(&ctx.txn.env).unwrap();
        assert!(
            !ctx.synthesize_simp_dictionary(&id, class(), &registry)
                .unwrap()
        );
        unchanged(&ctx, &before);
        assert!(ctx.txn.budget.heartbeats_consumed > before.txn.budget.heartbeats_consumed);
    }
    #[test]
    fn dictionary_matching_does_not_thaw_caller_synthetic_goals_or_drop_equations() {
        let mut ctx = context();
        let expected = local(&mut ctx);
        let (id, expression) = hole(&mut ctx);
        let caller = ctx.instance_hole(class()).unwrap();
        let ExprNode::MVar { id: caller_id } = caller.node() else {
            panic!("caller hole");
        };
        let saved_locals = ctx.txn.lctx.clone();
        let equation = (Expr::sort(Level::one()), Expr::sort(Level::one()));
        ctx.equations.push(SourceEquation::inference(
            equation.0.clone(),
            equation.1.clone(),
        ));
        assert!(
            ctx.synthesize_simp_rule_instances(&[id.clone(), caller_id.clone()], &[id])
                .unwrap()
        );
        assert_eq!(ctx.instantiate(&expression).unwrap(), expected);
        assert_eq!(ctx.txn.lctx, saved_locals);
        assert_eq!(ctx.equations.len(), 1);
        assert_eq!(ctx.equations[0].sides, equation);
        assert!(!ctx.txn.mvars.is_assigned(caller_id));
        assert_eq!(
            ctx.txn.mvars.get_decl(caller_id).unwrap().kind,
            MetavarKind::SyntheticOpaque
        );
    }
    #[test]
    fn aliases_to_unsolved_metavariables_still_require_synthesis() {
        let mut ctx = context();
        let expected = local(&mut ctx);
        let (id, expression) = hole(&mut ctx);
        let (_, alias) = hole(&mut ctx);
        ctx.txn
            .assign_mvar(
                id.clone(),
                alias,
                AssignmentJustification::InstanceSearch {
                    class_name: name("Dictionary"),
                },
            )
            .unwrap();
        assert!(ctx.txn.mvars.is_assigned(&id));
        assert!(matches!(
            ctx.instantiate(&expression).unwrap().node(),
            ExprNode::MVar { .. }
        ));
        assert!(
            ctx.synthesize_simp_rule_instances(
                std::slice::from_ref(&id),
                std::slice::from_ref(&id)
            )
            .unwrap()
        );
        assert_eq!(ctx.instantiate(&expression).unwrap(), expected);
    }
    #[test]
    fn interrupted_dictionary_search_rolls_back_and_a_fresh_retry_is_identical() {
        let mut initial = context();
        local(&mut initial);
        let (id, expression) = hole(&mut initial);
        let registry = InstanceRegistry::read(&initial.txn.env).unwrap();
        let mut control = initial.clone();
        assert!(
            control
                .synthesize_simp_dictionary(&id, class(), &registry)
                .unwrap()
        );
        let used = control.txn.budget.heartbeats_consumed;
        assert!(used > initial.txn.budget.heartbeats_consumed + 1);
        for maximum in [initial.txn.budget.heartbeats_consumed + 1, used - 1] {
            let mut limited = initial.clone();
            limited.txn.budget.max_heartbeats = maximum;
            assert!(
                limited
                    .synthesize_simp_dictionary(&id, class(), &registry)
                    .is_err()
            );
            unchanged(&limited, &initial);
        }
        let mut retry = initial;
        assert!(
            retry
                .synthesize_simp_dictionary(&id, class(), &registry)
                .unwrap()
        );
        assert_eq!(
            retry.instantiate(&expression).unwrap(),
            control.instantiate(&expression).unwrap()
        );
        assert_eq!(
            retry.txn.budget.heartbeats_consumed,
            control.txn.budget.heartbeats_consumed
        );
    }
}
