//! Simplify the goal and evidence independently, then require actual closure.
//! Evidence enters through the outer heap term driver; attempts retain work.
use super::*;

impl Context {
    pub(in crate::source) fn simpa_proof_term(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
        using: Option<Typed>,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        // Freeze selection before adding private evidence, so `[*]` cannot
        // acquire a synthetic assumption or use it as its own rewrite rule.
        let rules = self.simp_rules(args)?;
        if let Some(term) = using {
            return self.simpa_candidate(proof, goal, &rules, term);
        }
        // The pin's bare `simpa` simplifies the GOAL and then closes with a
        // plain `assumption` against the UNSIMPLIFIED hypotheses — measured at
        // v4.32.0, where its failure is "Tactic `assumption` failed". Evidence
        // types are never simplified here; that is the `using` form's job, and
        // trying each hypothesis as implicit `using` evidence accepted goals
        // the pin rejects (reference_differential.tsv, native_simpa Reference
        // 16). A goal simp closes outright still succeeds.
        let start = proof.work.len();
        match self.simplify_goal_with_rules(proof, goal.clone(), &rules, 0, None) {
            Ok(()) => {}
            Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                TacticError::SimplificationNoProgress,
            ))) => {
                // The pin's bare `simpa` still closes by assumption when simp
                // makes no progress — measured at v4.32.0: `simpa only []`
                // with `h : P` proves `P`. The no-progress path commits
                // nothing, so the original goal is intact for assumption.
                let value = self
                    .matching_assumption(&goal)?
                    .ok_or_else(|| error(TacticError::NoMatchingAssumption))?;
                return self.close_proof_goal(goal, value);
            }
            Err(other) => return Err(other),
        }
        let mut index = start;
        while index < proof.work.len() {
            self.tick()?;
            if let Work::Goal(child) = &proof.work[index] {
                let child = child.clone();
                if self.txn.mvars.is_assigned(&child.id) {
                    index += 1;
                    continue;
                }
                let value = self
                    .matching_assumption(&child)?
                    .ok_or_else(|| error(TacticError::NoMatchingAssumption))?;
                self.close_proof_goal(child, value)?;
            }
            index += 1;
        }
        Ok(())
    }

    /// Validate an unreduced term before choosing a successful alternative.
    /// Unifying a hole directly with the term could normalize away invalid
    /// annotations or unused arguments before assignment checking sees them.
    /// A non-unfoldable reference forces K1's existing assignment guard to
    /// check the original typed let in its captured local telescope instead.
    fn validate_simpa_evidence(&mut self, term: &Typed) -> Result<(), NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let name = self.fresh_name()?;
        let id = FVarId(name.clone());
        self.txn
            .lctx
            .add_let(id.clone(), name, term.type_.clone(), term.value.clone());
        let result = (|| {
            let check = self.hole(term.type_.clone())?;
            let mut budget = UnificationBudget::new(self.kernel);
            budget.transparency = UnificationTransparency::SafeDefinitions;
            budget.zeta_delta = false;
            let report = self
                .txn
                .unify(&check, &Expr::fvar(id), budget)
                .map_err(|error| failure(SourceInferenceError::Unification(Box::new(error))))?;
            assert!(report.awakened.is_empty(), "private source queue");
            Ok(())
        })();
        self.txn.lctx = saved;
        result
    }

    fn simpa_candidate(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        rules: &[SimpRule<'_>],
        term: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.resolve_instances(false)?;
        self.flush(false)?;
        let term = Typed {
            type_: self.instantiate(&term.type_)?,
            value: self.instantiate(&term.value)?,
        };
        self.validate_simpa_evidence(&term)?;
        let name = self.fresh_name()?;
        self.bind_proof_value(proof, goal, name.clone(), term, true)?;
        let Some(Work::Goal(bound)) = proof.work.pop() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        goal = bound;
        let mut history = Vec::new();
        let mut steps = 0;
        loop {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            let local = goal
                .lctx
                .find_by_user_name(&name)
                .cloned()
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            let target = self.instantiate(&local.type_)?;
            for old in &history {
                self.tick()?;
                if self.rewrite_same(old, &target)? {
                    return Err(error(TacticError::SimplificationCycle));
                }
            }
            history.push(target);
            let mut changed = false;
            for rule in rules {
                self.tick()?;
                let original = self.rewrite_trial();
                let Some(replacement) = self.simp_hypothesis_step(&local, rule, rules)? else {
                    self.restore_simp_trial(original);
                    continue;
                };
                if steps >= MAX_SIMPLIFICATION_STEPS {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let (next, parent, value) =
                    self.replace_rewritten_hypothesis(goal, &local, replacement)?;
                proof.work.push(Work::Close(parent, value));
                goal = next;
                steps += 1;
                changed = true;
                break;
            }
            if !changed {
                let completion = Typed {
                    value: Expr::fvar(local.id),
                    type_: local.type_,
                };
                return self.simplify_goal_with_rules(proof, goal, rules, steps, Some(&completion));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> (Context, Expr) {
        use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
        use fln_env::pmap::CollisionBudget;
        use fln_kernel::capability::{Published, admit};
        use fln_kernel::council::{Council, CouncilOutcome, convene};
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let mut env = Environment::new();
        for declaration in crate::seed::source_seed_declarations() {
            let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
                panic!("seed nonanswer");
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("seed rejected");
            };
            env = match checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) {
                Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                    result,
                ))) => result.environment,
                Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
                other => panic!("seed publication {other:?}"),
            };
        }
        let mut ctx = Context::new(&env, budget);
        let mut target = None;
        for name in ["P", "Q"] {
            let id = FVarId(Name::from_components([name]));
            ctx.txn.lctx.add_param(
                id.clone(),
                id.0.clone(),
                Expr::sort(Level::zero()),
                BinderInfo::Default,
            );
            let type_ = Expr::fvar(id);
            if name == "P" {
                target = Some(type_.clone());
            }
            let id = FVarId(Name::from_components([if name == "P" { "p" } else { "q" }]));
            ctx.txn
                .lctx
                .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
        }
        (ctx, target.unwrap())
    }

    #[test]
    fn exhausted_completion_attempts_are_nonanswers_not_successful_fallbacks() {
        for body in [
            "simpa only []",
            "simpa only [] using p",
            "simpa only [*] using p",
            "first | simpa only [] using q | exact p",
        ] {
            let parsed = fln_parse::parse_definition(
                format!("theorem test (P Q : Prop) (p : P) (q : Q) : P := by {body}").as_bytes(),
            )
            .unwrap();
            let mut pending = vec![parsed.syntax()];
            let syntax = loop {
                let node = pending.pop().expect("by proof");
                if node.kind() == Some(&parser_kind(&["Term", "byTactic"])) {
                    break node;
                }
                if let Syntax::Node { args, .. } = node {
                    pending.extend(args);
                }
            };
            let (mut completed, target) = context();
            completed.term(syntax, Some(target.clone())).unwrap();
            let total = completed.txn.budget.heartbeats_consumed;
            assert!(total > 4);
            for limit in [1, total / 4, total / 2] {
                let (mut ctx, _) = context();
                let environment = ctx.txn.env.clone();
                ctx.txn.budget.max_heartbeats = limit;
                let error = ctx
                    .term(syntax, Some(target.clone()))
                    .err()
                    .expect("budget stop");
                let stopped = match &error {
                    NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit) => true,
                    NatDefinitionElabError::Inference(SourceInferenceError::Unification(
                        reason,
                    )) => {
                        matches!(reason.as_ref(), UnificationError::HeartbeatLimit)
                    }
                    _ => false,
                };
                assert!(stopped, "{body} at {limit}: {error:?}");
                assert!(!crate::source::tactics::backtrack::recoverable(&error));
                assert!(ctx.txn.budget.heartbeats_consumed >= limit);
                assert_eq!(ctx.txn.env, environment);
            }
        }
    }
}
