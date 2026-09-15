//! Constructive proof control over ordinary admitted Decidable dictionaries.
//! Case branches are checked functions; an evaluated dictionary never permits
//! an unselected source branch or written annotation to disappear.
use super::*;

fn constant(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_components(name.split('.')), levels)
}
fn apps(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

impl Context {
    pub(super) fn decide_proof_goal(
        &mut self,
        goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let sort = self
            .known_type(&goal.target)?
            .ok_or_else(|| error(TacticError::ExpectedProposition))?;
        if !self.proof_types_match(&sort, &Expr::sort(Level::zero()))? {
            return Err(error(TacticError::ExpectedProposition));
        }
        let proposition = self.instantiate(&goal.target)?;
        self.require_resolved(std::slice::from_ref(&proposition))?;
        let dictionary = self.decision_dictionary(&proposition)?;
        let computation = apps(
            constant("decide", vec![]),
            [proposition.clone(), dictionary.clone()],
        );
        if !self.decision_computes_true(computation)? {
            return Err(error(TacticError::DecisionNotTrue));
        }
        let reflexive = apps(
            constant("Eq.refl", vec![Level::one()]),
            [constant("Bool", vec![]), constant("Bool.true", vec![])],
        );
        let value = apps(
            constant("of_decide_eq_true", vec![]),
            [proposition, dictionary, reflexive],
        );
        // Both checkers must justify the Boolean conversion independently.
        // In particular the actual dictionary and its arguments are retained;
        // successful tactic conversion is not an admission certificate.
        self.close_proof_goal(goal, value)
    }

    /// Source WHNF and the pattern unifier intentionally do not implement the
    /// complete kernel evaluator. Close the relevant local telescope and ask
    /// the existing K1 conversion query; this is tactic selection, not admission.
    /// Final admission retains the unmodified dictionary and checks both seats.
    fn decision_computes_true(
        &mut self,
        mut computation: Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut truth = constant("Bool.true", vec![]);
        let mut needed = self.elimination_reads(&computation)?;
        for mut local in self.txn.lctx.decls().to_vec().into_iter().rev() {
            self.tick()?;
            if !needed.remove(&local.id) {
                continue;
            }
            local.type_ = self.instantiate(&local.type_)?;
            needed.extend(self.elimination_reads(&local.type_)?);
            if let Some(value) = &local.value {
                let value = self.instantiate(value)?;
                needed.extend(self.elimination_reads(&value)?);
                local.value = Some(value);
            }
            computation = self.close_equality_binder(&local, computation, true)?;
            truth = self.close_equality_binder(&local, truth, true)?;
        }
        if !needed.is_empty() || computation.has_fvar() || truth.has_fvar() {
            return Err(failure(SourceInferenceError::Scope));
        }
        self.require_resolved(&[computation.clone(), truth.clone()])?;
        let budget = &self.txn.budget;
        let remaining = if budget.max_heartbeats == 0 {
            u64::MAX
        } else {
            budget
                .max_heartbeats
                .saturating_sub(budget.heartbeats_consumed)
        };
        let kernel = self
            .kernel
            .narrowed(self.kernel.steps.min(remaining), self.kernel.depth);
        match fln_kernel::check_def_eq(&self.txn.env, &[], &computation, &truth, kernel) {
            Outcome::Complete(verdict) => {
                let consumed = match &verdict {
                    Verdict::Accepted { consumption } | Verdict::Rejected { consumption, .. } => {
                        consumption.steps_used
                    }
                };
                self.txn.budget.heartbeats_consumed = self
                    .txn
                    .budget
                    .heartbeats_consumed
                    .checked_add(consumed)
                    .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                // Charge successful and failed conversions alike. Backtracking
                // may restore proof state but must not refund evaluation work.
                self.tick()?;
                Ok(verdict.is_accepted())
            }
            outcome => Err(failure(SourceInferenceError::TypeObligation(Box::new(
                outcome,
            )))),
        }
    }

    fn decision_dictionary(&mut self, proposition: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let domain = Expr::app(constant("Decidable", vec![]), proposition.clone());
        let dictionary = self.instance_hole(domain)?;
        self.resolve_instances(false)?;
        let dictionary = self.instantiate(&dictionary)?;
        // Resolve this tactic's dictionary only. Unrelated outer instance goals
        // may still depend on later fields or explicitly unsolved proof holes.
        if dictionary.has_expr_mvar() || dictionary.has_level_mvar() {
            return Err(failure(SourceInferenceError::InstanceSynthesisRequired));
        }
        Ok(dictionary)
    }

    fn decision_branch(
        &mut self,
        name: &Name,
        domain: Expr,
        target: &Expr,
    ) -> Result<(Expr, ProofGoal), NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let function_type = Expr::forall_e(
            name.clone(),
            domain.clone(),
            target.clone(),
            BinderInfo::Default,
        );
        let (value, mut goal) = self.proof_goal(function_type)?;
        let id = FVarId(self.fresh_name()?);
        self.txn
            .lctx
            .add_param(id.clone(), name.clone(), domain, BinderInfo::Default);
        goal.target = target.clone();
        goal.introduced
            .push(self.txn.lctx.find(&id).expect("case evidence").clone());
        goal.lctx = self.txn.lctx.clone();
        self.txn.lctx = saved;
        Ok((value, goal))
    }

    pub(in crate::source) fn split_decision_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        name: Name,
        proposition: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        if !self.proof_types_match(&proposition.type_, &Expr::sort(Level::zero()))? {
            return Err(error(TacticError::ExpectedProposition));
        }
        let proposition = self.instantiate(&proposition.value)?;
        let dictionary = self.decision_dictionary(&proposition)?;
        let target_type = self
            .known_type(&goal.target)?
            .ok_or_else(|| error(TacticError::ExpectedGoal))?;
        let universe = self.sort_level(&Typed {
            value: goal.target.clone(),
            type_: target_type,
        })?;
        let (yes, yes_goal) = self.decision_branch(&name, proposition.clone(), &goal.target)?;
        let negative = Expr::app(constant("Not", vec![]), proposition.clone());
        let (no, no_goal) = self.decision_branch(&name, negative, &goal.target)?;
        let value = apps(
            constant("dite", vec![universe]),
            [goal.target.clone(), proposition, dictionary, yes, no],
        );
        // The parent closes only after both branches, retaining even unused
        // branch obligations. LIFO publication exposes the positive case first.
        proof.work.push(Work::Close(goal, value));
        proof.work.push(Work::Goal(no_goal));
        proof.work.push(Work::Goal(yes_goal));
        Ok(())
    }
}
