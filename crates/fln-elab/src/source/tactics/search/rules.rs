//! Non-backtracking application shares checked terms, not search's success rule.
//! The pin uses repeat1': each attempted live goal costs one iteration, a stuck
//! goal is retained, and at least one application must have made progress.
use super::rules_config::Config;
use super::*;

impl Context {
    pub(in crate::source::tactics) fn apply_rule_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
        single: bool,
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, config, only, arguments, using] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(
            keyword,
            if single {
                "apply_assumption"
            } else {
                "apply_rules"
            },
            "rule application tactic",
        )?;
        self.require_declared_tactic(&[
            "Lean",
            "Parser",
            "Tactic",
            if single {
                "applyAssumption"
            } else {
                "applyRules"
            },
        ])?;
        let mut config = Config::read(self, config)?;
        if single {
            config.max_steps = 1;
        }
        let selection = selection::selected_arguments(false, only, arguments, using)?;
        let snapshot = Box::new(self.clone());
        // Validate even an unused explicit argument, before a default or a
        // matching local can make it disappear. No probe commits assignments.
        let validated = self.selected_search_candidates(&goal, &selection);
        restore(self, &snapshot);
        validated?;
        let result =
            self.repeat_rule_applications(vec![Work::Goal(goal.clone())], &selection, config);
        let result = match result {
            Err(problem) if config.exfalso && backtrack::recoverable(&problem) => {
                restore(self, &snapshot);
                self.rule_exfalso(&goal)
                    .and_then(|work| self.repeat_rule_applications(work, &selection, config))
            }
            other => other,
        };
        match result {
            Ok(work) => {
                // Never select or remove a sibling suspended in the caller.
                proof.work.extend(work);
                Ok(())
            }
            Err(problem) => {
                restore(self, &snapshot);
                Err(problem)
            }
        }
    }

    fn repeat_rule_applications(
        &mut self,
        mut pending: Vec<Work<'static>>,
        selection: &Selection<'_>,
        config: Config,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        let mut remaining = config.max_steps;
        let mut progressed = false;
        let mut goals = Vec::new();
        let mut closes = Vec::new();
        while let Some(work) = pending.pop() {
            self.tick()?;
            match work {
                Work::Goal(mut goal) => {
                    if self.txn.mvars.is_assigned(&goal.id) {
                        continue;
                    }
                    self.txn.lctx = goal.lctx.clone();
                    goal.target = self.instantiate(&goal.target)?;
                    if remaining == 0 {
                        goals.push(goal);
                        continue;
                    }
                    remaining -= 1;
                    let snapshot = self.clone();
                    match self.first_rule_application(&goal, selection, config.symm) {
                        Ok(work) => {
                            progressed = true;
                            pending.extend(work);
                        }
                        Err(problem) if backtrack::recoverable(&problem) => {
                            restore(self, &snapshot);
                            goals.push(goal);
                        }
                        Err(problem) => return Err(problem),
                    }
                }
                Work::Close(goal, value) => {
                    let value = self.instantiate(&value)?;
                    if value.has_expr_mvar() {
                        // Do not abstract introduced locals around an open
                        // child hole. It must first be solved in its own scope.
                        closes.push(Work::Close(goal, value));
                    } else {
                        self.close_proof_goal(goal, value)?;
                    }
                }
                _ => return Err(error(TacticError::MalformedScript)),
            }
        }
        if !progressed {
            return Err(error(TacticError::NoMatchingAssumption));
        }
        // Closures were visited child-before-parent. Reverse them for the
        // caller's LIFO worklist, below every still-live goal in source order.
        let mut work: Vec<_> = closes.into_iter().rev().collect();
        for goal in goals.into_iter().rev() {
            self.tick()?;
            if !self.txn.mvars.is_assigned(&goal.id) {
                work.push(Work::Goal(goal));
            }
        }
        Ok(work)
    }

    fn first_rule_application(
        &mut self,
        goal: &ProofGoal,
        selection: &Selection<'_>,
        symm: bool,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        let candidates = self.selected_search_candidates(goal, selection)?;
        let mut locals = Vec::new();
        let mut explicit = Vec::new();
        for candidate in candidates {
            match candidate {
                Candidate::Local(_) => locals.push(candidate),
                Candidate::Explicit(_) => explicit.push(candidate),
            }
        }
        // getLocalHyps visits the local context in declaration order. Search's
        // heuristic newest-first order is not greedy rule-selection authority.
        locals.reverse();
        let attempts = locals
            .iter()
            .cloned()
            .map(|c| (c, false))
            .chain(locals.iter().cloned().filter(|_| symm).map(|c| (c, true)))
            .chain(explicit.into_iter().map(|c| (c, false)));
        let snapshot = self.clone();
        for (candidate, reverse) in attempts {
            restore(self, &snapshot);
            self.tick()?;
            let result = if reverse {
                self.search_symmetric_candidate(goal, candidate, true)
            } else {
                self.search_candidate(goal, candidate, true)
            };
            match result {
                Ok(work) => return Ok(work),
                Err(problem) if backtrack::recoverable(&problem) => {}
                Err(problem) => {
                    restore(self, &snapshot);
                    return Err(problem);
                }
            }
        }
        restore(self, &snapshot);
        if selection.defaults {
            // Defaults are last, after the selected context and explicit rules.
            // This helper builds ordinary Eq/HEq/True evidence, never a verdict.
            let result = self.search_default_candidate(goal);
            if result.is_ok() {
                return result;
            }
            restore(self, &snapshot);
            if let Err(problem) = result
                && !backtrack::recoverable(&problem)
            {
                return Err(problem);
            }
        }
        Err(error(TacticError::NoMatchingAssumption))
    }

    pub(super) fn rule_exfalso(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let false_type = Expr::const_(Name::from_components(["False"]), Vec::new());
        if self.whnf(&goal.target)? == false_type {
            return Err(error(TacticError::NoMatchingAssumption));
        }
        let (value, child) = self.proof_goal(false_type.clone())?;
        let value = self
            .empty_evidence(
                &Typed {
                    value,
                    type_: false_type,
                },
                &goal.target,
            )?
            .ok_or_else(|| error(TacticError::NoMatchingAssumption))?;
        Ok(vec![Work::Close(goal.clone(), value), Work::Goal(child)])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_syntax::source::SourceInfo;

    fn local(context: &mut Context, name: &str, type_: Expr) -> Expr {
        let name = Name::from_components([name]);
        let id = FVarId(name.clone());
        context
            .txn
            .lctx
            .add_param(id.clone(), name, type_, BinderInfo::Default);
        Expr::fvar(id)
    }

    fn arguments() -> Vec<Syntax> {
        let null = || Syntax::node(Name::from_components(["null"]), Vec::new());
        vec![
            Syntax::atom(SourceInfo::None, "apply_rules"),
            Syntax::node(parser_kind(&["Tactic", "optConfig"]), vec![null()]),
            null(),
            null(),
            null(),
        ]
    }

    #[test]
    fn every_greedy_budget_stop_rolls_back_assignments_and_the_callers_frontier() {
        let mut original = Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        );
        let p = local(&mut original, "P", Expr::sort(Level::zero()));
        let q = local(&mut original, "Q", Expr::sort(Level::zero()));
        local(
            &mut original,
            "f",
            Expr::forall_e(Name::anonymous(), p.clone(), q.clone(), BinderInfo::Default),
        );
        let (root, goal) = original.proof_goal(q.clone()).unwrap();
        let (_, sibling) = original.proof_goal(p).unwrap();
        let proof = ProofState {
            extent: None,
            saved: original.txn.lctx.clone(),
            target: q,
            root,
            instructions: Vec::new(),
            cursor: 0,
            work: vec![Work::Goal(sibling.clone())],
            controls: Vec::new(),
        };
        let args = arguments();
        let before = original.txn.budget.heartbeats_consumed;
        let mut complete = original.clone();
        let mut completed_proof = proof.clone();
        complete
            .apply_rule_proof_goal(&mut completed_proof, goal.clone(), &args, false)
            .unwrap();
        // One new premise, with its parent close, above the untouched sibling.
        assert_eq!(completed_proof.work.len(), 3);
        assert!(!complete.txn.mvars.is_assigned(&goal.id));
        assert!(!complete.txn.mvars.is_assigned(&sibling.id));
        let work = complete.txn.budget.heartbeats_consumed - before;
        for allowance in 0..work {
            let mut limited = original.clone();
            limited.txn.budget.max_heartbeats = before + allowance;
            let mut pending = proof.clone();
            let error = limited
                .apply_rule_proof_goal(&mut pending, goal.clone(), &args, false)
                .expect_err("an incomplete budget is not a successful partial application");
            assert!(!backtrack::recoverable(&error), "{allowance}: {error:?}");
            assert_eq!(limited.txn.mvars.len(), original.txn.mvars.len());
            assert_eq!(
                limited.txn.mvars.assignments(),
                original.txn.mvars.assignments()
            );
            assert_eq!(limited.txn.lctx.decls(), original.txn.lctx.decls());
            assert_eq!(limited.instance_goals, original.instance_goals);
            assert!(limited.txn.budget.heartbeats_consumed >= before + allowance);
            assert!(matches!(pending.work.as_slice(), [Work::Goal(g)] if g.id == sibling.id));
        }
    }

    #[test]
    fn a_stuck_premise_is_retained_but_a_no_progress_call_is_failure_atomic() {
        let mut context = Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        );
        let p = local(&mut context, "P", Expr::sort(Level::zero()));
        let (_, goal) = context.proof_goal(p.clone()).unwrap();
        let before = context.clone();
        let mut proof = ProofState {
            extent: None,
            saved: context.txn.lctx.clone(),
            target: p,
            root: Expr::mvar(goal.id.clone()),
            instructions: Vec::new(),
            cursor: 0,
            work: Vec::new(),
            controls: Vec::new(),
        };
        let error = context
            .apply_rule_proof_goal(&mut proof, goal.clone(), &arguments(), false)
            .unwrap_err();
        // A missing False declaration may itself be unsupported in this tiny
        // environment; neither that nor ordinary no-progress may publish state.
        assert!(!context.txn.mvars.is_assigned(&goal.id), "{error:?}");
        assert_eq!(context.txn.mvars.len(), before.txn.mvars.len());
        assert_eq!(context.txn.lctx.decls(), before.txn.lctx.decls());
        assert!(context.txn.budget.heartbeats_consumed > before.txn.budget.heartbeats_consumed);
        assert!(proof.work.is_empty());
    }
}
