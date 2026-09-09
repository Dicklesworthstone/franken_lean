//! Explicit-set, proof-producing simplification. There is no ambient simp set.
//! Rules are tried deterministically and re-instantiated for every application.
//! An unsuccessful alternative restores its complete elaboration state while
//! retaining spent work. Every productive step is ordinary Eq.rec transport.

mod unfold;

use super::*;
use unfold::UnfoldResult;

const MAX_SIMPLIFICATION_STEPS: usize = 256;

impl Context {
    fn simp_rules<'a>(
        &mut self,
        args: &'a [Syntax],
    ) -> Result<Vec<RewriteRule<'a>>, NatDefinitionElabError> {
        let [keyword, config, discharger, only, arguments, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "simp", "simplification keyword")?;
        expect_empty_null(config, "default simplification configuration")?;
        expect_empty_null(discharger, "default simplification discharger")?;
        expect_empty_null(location, "goal-only simplification")?;
        let [only] = expect_null_args(only, "explicit simp set")? else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(only, "only", "explicit-set simplification")?;
        let arguments = expect_null_args(arguments, "optional simp rule list")?;
        if arguments.is_empty() {
            return Ok(Vec::new());
        }
        let [open, rows, close] = arguments else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(open, "[", "simp rule opener")?;
        expect_atom(close, "]", "simp rule closer")?;
        let rows = expect_null_args(rows, "simp rules")?;
        let mut rules = Vec::new();
        for (index, row) in rows.iter().enumerate() {
            self.tick()?;
            if index % 2 == 1 {
                expect_atom(row, ",", "simp rule separator")?;
                continue;
            }
            let parts = expect_node(row, &parser_kind(&["Tactic", "simpLemma"]), 3, "simp lemma")?;
            expect_empty_null(&parts[0], "default post-order simp rule")?;
            let reverse = match expect_null_args(&parts[1], "simp direction")? {
                [] => false,
                [Syntax::Atom { val, .. }] if val == "←" || val == "<-" => true,
                _ => return Err(error(TacticError::MalformedScript)),
            };
            // `term` below runs the normal heap-driven elaborator. The source
            // parser already forbids nested proof scripts, but a caller can
            // supply Syntax directly: enforce the same boundary here so this
            // one level of re-entry can never grow with source-controlled depth.
            let mut pending = vec![&parts[2]];
            while let Some(term) = pending.pop() {
                self.tick()?;
                if let Syntax::Node { kind, args, .. } = term {
                    if kind == &parser_kind(&["Term", "byTactic"]) {
                        return Err(error(TacticError::MalformedScript));
                    }
                    pending.extend(args);
                }
            }
            rules.push(RewriteRule {
                syntax: &parts[2],
                reverse,
            });
        }
        Ok(rules)
    }

    fn restore_simp_trial(&mut self, mut original: Self) {
        original.txn.budget.heartbeats_consumed = self.txn.budget.heartbeats_consumed;
        *self = original;
    }

    /// Only selected definitions participate in conversion of a side condition.
    fn simp_premise_target(
        &mut self,
        target: &Expr,
        rules: &[RewriteRule<'_>],
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut target = target.clone();
        for _ in 0..MAX_SIMPLIFICATION_STEPS {
            let mut changed = false;
            for rule in rules {
                self.tick()?;
                if let UnfoldResult::Changed(next) =
                    self.unfold_simp_term(rule.syntax, rule.reverse, &target)?
                {
                    target = next;
                    changed = true;
                }
            }
            if !changed {
                return Ok(target);
            }
        }
        Err(failure(SourceInferenceError::ResourceLimit))
    }

    fn simp_selected_proof(
        &mut self,
        target: &Expr,
        rules: &[RewriteRule<'_>],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        for rule in rules {
            self.tick()?;
            let selected = self.term(rule.syntax, None)?;
            let type_ = self.simp_premise_target(&selected.type_, rules)?;
            let Some(universe) = self.known_type(&type_)? else {
                continue;
            };
            let universe = self.whnf(&universe)?;
            if !matches!(universe.node(), ExprNode::Sort { level } if level.is_zero()) {
                continue;
            }
            let mut budget = UnificationBudget::new(self.kernel);
            budget.zeta_delta = false;
            if self.proof_types_match_with_budget(&type_, target, budget)? {
                let value = self.instantiate(&selected.value)?;
                if !value.has_expr_mvar() && !value.has_level_mvar() {
                    return Ok(Some(value));
                }
            }
        }
        Ok(None)
    }

    pub(super) fn simp_discharge_premise(
        &mut self,
        id: &MVarId,
        target: &Expr,
        rules: &[RewriteRule<'_>],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let target = self.simp_premise_target(target, rules)?;
        if let Some(value) = self.simp_selected_proof(&target, rules)? {
            return Ok(Some(value));
        }
        let goal = ProofGoal {
            id: id.clone(),
            target,
            lctx: self.txn.lctx.clone(),
            introduced: Vec::new(),
        };
        if let Some(value) = self.automatic_reflexivity_candidate(&goal, false)? {
            return Ok(Some(value));
        }
        if rules.is_empty() {
            return Ok(None);
        }
        let original = self.rewrite_trial();
        let value = self.rewrite_simp_premise(&goal.target, rules)?;
        if value.is_none() {
            self.restore_simp_trial(original);
        }
        Ok(value)
    }

    /// Construct a premise proof using the selected equalities and definitions.
    /// Parents live on the heap; rewriting a premise never recursively invokes
    /// the same selected set. Inner rules may discharge reflexive premises only.
    fn rewrite_simp_premise(
        &mut self,
        target: &Expr,
        rules: &[RewriteRule<'_>],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (root, mut goal) = self.proof_goal(target.clone())?;
        let mut parents = Vec::new();
        let mut history = vec![target.clone()];
        loop {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            let mut advanced = false;
            for rule in rules {
                self.tick()?;
                let original = self.rewrite_trial();
                let Some((next_goal, value)) = self.simp_step(&goal, rule, &[])? else {
                    self.restore_simp_trial(original);
                    continue;
                };
                if parents.len() >= MAX_SIMPLIFICATION_STEPS {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let next_target = self.instantiate(&next_goal.target)?;
                for previous in &history {
                    self.tick()?;
                    if self.rewrite_same(previous, &next_target)? {
                        return Err(error(TacticError::SimplificationCycle));
                    }
                }
                history.push(next_target);
                parents.push((goal, value));
                goal = next_goal;
                advanced = true;
                break;
            }
            if advanced {
                continue;
            }
            let value = match self.simp_selected_proof(&goal.target, rules)? {
                Some(value) => Some(value),
                None => self.simp_reflexivity(&goal)?,
            };
            let Some(value) = value else {
                return Ok(None);
            };
            self.close_proof_goal(goal, value)?;
            while let Some((parent, value)) = parents.pop() {
                self.tick()?;
                self.close_proof_goal(parent, value)?;
            }
            return Ok(Some(self.instantiate(&root)?));
        }
    }

    fn simp_step(
        &mut self,
        goal: &ProofGoal,
        rule: &RewriteRule<'_>,
        premise_rules: &[RewriteRule<'_>],
    ) -> Result<Option<(ProofGoal, Expr)>, NatDefinitionElabError> {
        let target = self.instantiate(&goal.target)?;
        match self.unfold_simp_term(rule.syntax, rule.reverse, &target)? {
            UnfoldResult::Unchanged => Ok(None),
            UnfoldResult::Changed(next_target) => {
                let (child, next_goal) = self.proof_goal(next_target)?;
                Ok(Some((next_goal, child)))
            }
            UnfoldResult::NotDefinition => {
                // Re-elaboration gives each polymorphic use fresh universes.
                let term = self.term(rule.syntax, None)?;
                let Some(RewriteMatch {
                    rule: term,
                    occurrence,
                    premises,
                }) = self.instantiate_rewrite_rule(
                    term,
                    &target,
                    rule.reverse,
                    true,
                    premise_rules,
                )?
                else {
                    return Ok(None);
                };
                assert!(premises.is_empty(), "simp discharges its own premises");
                Ok(Some(self.rewrite_transport(
                    goal,
                    term,
                    &occurrence,
                    rule.reverse,
                )?))
            }
        }
    }

    /// Check a candidate only after the shared automatic-closure policy admits
    /// it. Full K1 assignment conversion alone would unfold ordinary definitions
    /// that are absent from this tactic's explicit rule set.
    fn simp_reflexivity(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let Some(candidate) = self.automatic_reflexivity_candidate(goal, false)? else {
            return Ok(None);
        };
        let target = self.instantiate(&goal.target)?;
        let mut trial = self.rewrite_trial();
        let hole = trial.hole(target)?;
        let result = trial
            .txn
            .unify(&hole, &candidate, UnificationBudget::new(trial.kernel));
        self.charge_rewrite_trial(&trial);
        match result {
            Ok(report) => {
                assert!(report.awakened.is_empty(), "private source queue");
                let candidate = trial.instantiate(&candidate)?;
                *self = trial;
                Ok(Some(candidate))
            }
            Err(error) => {
                let error = failure(SourceInferenceError::Unification(Box::new(error)));
                if Self::rewrite_nonmatch(&error) {
                    Ok(None)
                } else {
                    Err(error)
                }
            }
        }
    }

    pub(in crate::source) fn simplify_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let rules = self.simp_rules(args)?;
        let mut history = vec![self.instantiate(&goal.target)?];
        let mut steps = 0;
        loop {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            let mut advanced = false;
            for rule in &rules {
                self.tick()?;
                let original = self.rewrite_trial();
                let transition = self.simp_step(&goal, rule, &rules)?;
                let Some((next_goal, value)) = transition else {
                    self.restore_simp_trial(original);
                    continue;
                };
                if steps >= MAX_SIMPLIFICATION_STEPS {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let next_target = self.instantiate(&next_goal.target)?;
                for previous in &history {
                    self.tick()?;
                    if self.rewrite_same(previous, &next_target)? {
                        return Err(error(TacticError::SimplificationCycle));
                    }
                }
                history.push(next_target);
                proof.work.push(Work::Close(goal, value));
                goal = next_goal;
                steps += 1;
                advanced = true;
                break;
            }
            if advanced {
                continue;
            }
            if let Some(value) = self.simp_selected_proof(&goal.target, &rules)? {
                self.close_proof_goal(goal, value)?;
            } else if let Some(value) = self.simp_reflexivity(&goal)? {
                self.close_proof_goal(goal, value)?;
            } else if steps > 0 {
                // Simplification can expose a non-reflexive remaining goal.
                // Later instructions must solve it; progress is not completion.
                proof.work.push(Work::Goal(goal));
            } else {
                return Err(error(TacticError::SimplificationNoProgress));
            }
            return Ok(());
        }
    }
}
