//! Transactional instantiation of quantified equality rules at goal occurrences.
//! Failed candidates cannot assign another goal's metavariables or consume an
//! unresolved premise. All successful rule applications retain their proof term.

use super::*;
use std::collections::HashSet;

impl Context {
    fn rewrite_trial(&self) -> Self {
        Self {
            txn: self.txn.clone(),
            kernel: self.kernel,
            next: self.next,
            equations: self.equations.clone(),
        }
    }

    /// Retain the cost of unsuccessful alternatives without retaining their
    /// semantic state. Every trial begins at the already charged parent budget.
    fn charge_rewrite_trial(&mut self, trial: &Self) {
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
    }

    fn rewrite_nonmatch(error: &NatDefinitionElabError) -> bool {
        let NatDefinitionElabError::Inference(SourceInferenceError::Unification(error)) = error
        else {
            return false;
        };
        match error.as_ref() {
            UnificationError::Deferred(_)
            | UnificationError::Metavariable(MetavarError::OccursCheckFailed { .. }) => true,
            UnificationError::AssignmentCheck { outcome, .. } => {
                matches!(
                    outcome.as_ref(),
                    Outcome::Complete(Verdict::Rejected { .. })
                )
            }
            _ => false,
        }
    }

    /// Match both the term and its type. `constrain` contributes universe
    /// equations, while the explicit equations also check closed mismatches
    /// (ordinary source elaboration leaves those to final declaration checking).
    fn match_rewrite_occurrence(
        &mut self,
        pattern: &Expr,
        alpha: &Expr,
        occurrence: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(type_) = self.known_type(occurrence)? else {
            return Ok(false);
        };
        self.constrain(&type_, alpha)?;
        self.constrain(occurrence, pattern)?;
        self.equations.push((type_, alpha.clone()));
        self.equations.push((occurrence.clone(), pattern.clone()));
        self.flush(true)?;
        Ok(true)
    }

    fn discharge_rewrite_premises(
        &mut self,
        holes: &[MVarId],
    ) -> Result<bool, NatDefinitionElabError> {
        loop {
            let before = self.txn.mvars.assignments().len();
            for id in holes {
                self.tick()?;
                if self.txn.mvars.is_assigned(id) {
                    continue;
                }
                let raw = self
                    .txn
                    .mvars
                    .get_decl(id)
                    .expect("rule parameter was declared")
                    .type_
                    .clone();
                let target = self.instantiate(&raw)?;
                let Some(universe) = self.known_type(&target)? else {
                    continue;
                };
                let universe = self.whnf(&universe)?;
                // Data parameters are inferred by matching, not guessed from
                // local values. A later propositional premise may determine one.
                if !matches!(universe.node(), ExprNode::Sort { level } if level.is_zero()) {
                    continue;
                }
                let locals = self.txn.lctx.decls().to_vec();
                let mut value = None;
                for local in locals.iter().rev() {
                    self.tick()?;
                    if self.proof_types_match(&local.type_, &target)? {
                        value = Some(Expr::fvar(local.id.clone()));
                        break;
                    }
                }
                if value.is_none() {
                    let target = self.whnf(&target)?;
                    if let Some((u, alpha, lhs, rhs)) = equality_target(&target)
                        && self.proof_types_match(&lhs, &rhs)?
                    {
                        value = Some(app(
                            Expr::const_(Name::from_components(["Eq", "refl"]), vec![u]),
                            [alpha, lhs],
                        ));
                    }
                }
                if let Some(value) = value {
                    self.txn
                        .assign_mvar(
                            id.clone(),
                            value,
                            AssignmentJustification::Tactic {
                                tactic_name: Name::from_components(["rewrite", "discharge"]),
                            },
                        )
                        .map_err(|e| {
                            failure(SourceInferenceError::Unification(Box::new(
                                UnificationError::Metavariable(e),
                            )))
                        })?;
                }
            }
            if holes.iter().all(|id| self.txn.mvars.is_assigned(id)) {
                return Ok(true);
            }
            if self.txn.mvars.assignments().len() == before {
                return Ok(false);
            }
        }
    }

    /// Instantiate a rule afresh at the first eligible occurrence. Traversal
    /// order is explicit: rewriting searches outside-in, simplification inside-out.
    /// Bound-variable occurrences needing a newly opened binder are not guessed.
    pub(in crate::source) fn instantiate_rewrite_rule(
        &mut self,
        mut rule: Typed,
        target: &Expr,
        reverse: bool,
        inside_out: bool,
    ) -> Result<Option<(Typed, Expr)>, NatDefinitionElabError> {
        self.flush(false)?;
        let mut template = self.rewrite_trial();
        let mut holes = Vec::new();
        loop {
            template.tick()?;
            rule.type_ = template.whnf(&rule.type_)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = rule.type_.node()
            else {
                break;
            };
            if *binder_info == BinderInfo::InstImplicit {
                return Err(failure(SourceInferenceError::InstanceSynthesisRequired));
            }
            let domain = binder_type.clone();
            let body = body.clone();
            let argument = template.hole(domain)?;
            if let ExprNode::MVar { id } = argument.node() {
                holes.push(id.clone());
            }
            rule.type_ = template.substitute(&body, &argument)?;
            rule.value = Expr::app(rule.value, argument);
        }
        let (_, alpha, lhs, rhs) =
            equality_target(&rule.type_).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let pattern = if reverse { rhs } else { lhs };
        self.charge_rewrite_trial(&template);
        let mut pending = vec![(target, false)];
        let mut visited = HashSet::new();
        while let Some((term, exit)) = pending.pop() {
            self.tick()?;
            if !exit {
                if !visited.insert(term.allocation_identity()) {
                    continue;
                }
                if inside_out {
                    pending.push((term, true));
                    pending.extend(
                        children(term)
                            .into_iter()
                            .rev()
                            .flatten()
                            .map(|child| (child, false)),
                    );
                    continue;
                }
                pending.extend(
                    children(term)
                        .into_iter()
                        .rev()
                        .flatten()
                        .map(|child| (child, false)),
                );
            }
            if term.has_loose_bvars() {
                continue;
            }
            let mut trial = template.rewrite_trial();
            trial.txn.budget = self.txn.budget.clone();
            let attempt = (|| {
                if !trial.match_rewrite_occurrence(&pattern, &alpha, term)?
                    || !trial.discharge_rewrite_premises(&holes)?
                {
                    return Ok(None);
                }
                let value = trial.instantiate(&rule.value)?;
                let type_ = trial.instantiate(&rule.type_)?;
                if value.has_expr_mvar()
                    || value.has_level_mvar()
                    || type_.has_expr_mvar()
                    || type_.has_level_mvar()
                {
                    return Ok(None);
                }
                Ok(Some((Typed { value, type_ }, trial.instantiate(term)?)))
            })();
            self.charge_rewrite_trial(&trial);
            match attempt {
                Ok(Some(rule)) => {
                    self.txn = trial.txn;
                    self.next = trial.next;
                    self.equations = trial.equations;
                    return Ok(Some(rule));
                }
                Ok(None) => {}
                Err(error) if Self::rewrite_nonmatch(&error) => {}
                Err(error) => return Err(error),
            }
        }
        Ok(None)
    }
}
