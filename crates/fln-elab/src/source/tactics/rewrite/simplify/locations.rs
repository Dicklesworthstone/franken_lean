//! Explicit-set simplification of local types, retaining each actual proof and
//! selected definition. Progress in a hypothesis is not proof of the main goal.
use super::*;

impl Context {
    fn simp_hypothesis_step(
        &mut self,
        local: &LocalDecl,
        rule: &RewriteRule<'_>,
        rules: &[RewriteRule<'_>],
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let target = self.instantiate(&local.type_)?;
        match self.unfold_simp_term(rule.syntax, rule.reverse, &target)? {
            UnfoldResult::Unchanged => Ok(None),
            UnfoldResult::Changed(type_) => Ok(Some(Typed {
                value: Expr::fvar(local.id.clone()),
                type_,
            })),
            UnfoldResult::NotDefinition => {
                let mut term = self.simp_rule_term(rule.syntax)?;
                term.type_ = self.simp_premise_target(&term.type_, rules)?;
                let Some(RewriteMatch {
                    rule: term,
                    occurrence,
                    premises,
                }) = self.instantiate_rewrite_rule(term, &target, rule.reverse, true, rules)?
                else {
                    return Ok(None);
                };
                assert!(premises.is_empty(), "simp discharges its own premises");
                self.rewrite_hypothesis_value(local, term, &occurrence, rule.reverse)
                    .map(Some)
            }
        }
    }

    pub(super) fn simplify_at_locations(
        &mut self,
        proof: &mut ProofState<'_>,
        initial: &ProofGoal,
        args: &[Syntax],
    ) -> Result<bool, NatDefinitionElabError> {
        let [_, _, _, _, _, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        let Some(locations) = self.rewrite_locations(location)? else {
            return Ok(false);
        };
        let rules = self.simp_rules(args)?;
        for name in &locations {
            self.tick()?;
            if initial.lctx.find_by_user_name(name).is_none() {
                return Err(error(TacticError::RewriteLocation));
            }
        }
        let mut goal = initial.clone();
        let mut steps = 0;
        for name in locations {
            self.txn.lctx = goal.lctx.clone();
            let local = goal
                .lctx
                .find_by_user_name(&name)
                .cloned()
                .ok_or_else(|| error(TacticError::RewriteLocation))?;
            let mut history = vec![self.instantiate(&local.type_)?];
            loop {
                self.tick()?;
                self.txn.lctx = goal.lctx.clone();
                let local = goal
                    .lctx
                    .find_by_user_name(&name)
                    .cloned()
                    .ok_or_else(|| error(TacticError::RewriteLocation))?;
                let mut advanced = false;
                for rule in &rules {
                    self.tick()?;
                    let original = self.rewrite_trial();
                    let Some(replacement) = self.simp_hypothesis_step(&local, rule, &rules)? else {
                        self.restore_simp_trial(original);
                        continue;
                    };
                    if steps >= MAX_SIMPLIFICATION_STEPS {
                        return Err(failure(SourceInferenceError::ResourceLimit));
                    }
                    let target = self.instantiate(&replacement.type_)?;
                    for previous in &history {
                        self.tick()?;
                        if self.rewrite_same(previous, &target)? {
                            return Err(error(TacticError::SimplificationCycle));
                        }
                    }
                    history.push(target);
                    let (next, parent, value) =
                        self.replace_rewritten_hypothesis(goal, &local, replacement)?;
                    proof.work.push(Work::Close(parent, value));
                    goal = next;
                    steps += 1;
                    advanced = true;
                    break;
                }
                if !advanced {
                    break;
                }
            }
        }
        if steps == 0 {
            return Err(error(TacticError::SimplificationNoProgress));
        }
        proof.work.push(Work::Goal(goal));
        Ok(true)
    }
}
