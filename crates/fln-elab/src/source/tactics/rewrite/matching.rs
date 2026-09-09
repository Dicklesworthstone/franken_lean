//! Transactional instantiation of quantified equality rules at goal occurrences.
//! Failed candidates cannot assign another goal's metavariables or consume an
//! unresolved premise. All successful rule applications retain their proof term.

use super::*;
use std::collections::HashSet;

impl Context {
    pub(super) fn rewrite_trial(&self) -> Self {
        self.clone()
    }

    /// Retain the cost of unsuccessful alternatives without retaining their
    /// semantic state. Every trial begins at the already charged parent budget.
    pub(super) fn charge_rewrite_trial(&mut self, trial: &Self) {
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
    }

    pub(super) fn rewrite_nonmatch(error: &NatDefinitionElabError) -> bool {
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
        selected_rules: &[RewriteRule<'_>],
    ) -> Result<bool, NatDefinitionElabError> {
        loop {
            let before = self.txn.mvars.assignments().len();
            for id in holes {
                self.tick()?;
                if self.txn.mvars.is_assigned(id) || self.instance_goals.contains(id) {
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
                // Simp may discharge a proposition fixed by the match, but may
                // not guess a remaining data parameter from a selected proof.
                if target.has_expr_mvar() || target.has_level_mvar() {
                    continue;
                }
                let Some(universe) = self.known_type(&target)? else {
                    continue;
                };
                let universe = self.whnf(&universe)?;
                // Data parameters are inferred by the occurrence match, never
                // guessed from a value mentioned in the selected simp set.
                if !matches!(universe.node(), ExprNode::Sort { level } if level.is_zero()) {
                    continue;
                }
                let value = self.simp_discharge_premise(id, &target, selected_rules)?;
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
        selected_rules: &[RewriteRule<'_>],
    ) -> Result<Option<RewriteMatch>, NatDefinitionElabError> {
        self.flush(false)?;
        let mut template = self.rewrite_trial();
        let mut implicit_holes = Vec::new();
        // Rule elaboration has already inserted implicit arguments. They are
        // obligations too, even when equality transport later erases the rule.
        rule.value = template.instantiate(&rule.value)?;
        let mut pending = vec![&rule.value];
        let mut visited = HashSet::new();
        while let Some(term) = pending.pop() {
            template.tick()?;
            if !visited.insert(term.allocation_identity()) {
                continue;
            }
            if let ExprNode::MVar { id } = term.node()
                && !implicit_holes.contains(id)
            {
                implicit_holes.push(id.clone());
            }
            pending.extend(children(term).into_iter().rev().flatten());
        }
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
            let domain = binder_type.clone();
            let body = body.clone();
            let argument = if *binder_info == BinderInfo::InstImplicit {
                template.instance_hole(domain)?
            } else {
                template.hole(domain)?
            };
            if let ExprNode::MVar { id } = argument.node() {
                holes.push(id.clone());
            }
            rule.type_ = template.substitute(&body, &argument)?;
            rule.value = Expr::app(rule.value, argument);
        }
        // Rewrite's newly applied parameters precede the unresolved implicit
        // arguments inserted while elaborating the selected rule expression.
        holes.extend(implicit_holes);
        let Some((_, alpha, lhs, rhs)) = equality_target(&rule.type_) else {
            // An explicitly selected proposition proof can discharge another
            // rule's premise without itself being an equality rewrite.
            if inside_out && let Some(universe) = template.known_type(&rule.type_)? {
                let universe = template.whnf(&universe)?;
                if matches!(universe.node(), ExprNode::Sort { level } if level.is_zero()) {
                    self.charge_rewrite_trial(&template);
                    return Ok(None);
                }
            }
            return Err(error(TacticError::ExpectedEquality));
        };
        let pattern = if reverse { rhs } else { lhs };
        self.charge_rewrite_trial(&template);
        if !inside_out {
            let pattern = template.instantiate(&pattern)?;
            self.charge_rewrite_trial(&template);
            let mut head = &pattern;
            loop {
                self.tick()?;
                match head.node() {
                    ExprNode::App { f, .. } => head = f,
                    ExprNode::MData { expr, .. } => head = expr,
                    ExprNode::MVar { .. } => {
                        return Err(error(TacticError::RewriteMetavariablePattern));
                    }
                    _ => break,
                }
            }
        }
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
                if !trial.match_rewrite_occurrence(&pattern, &alpha, term)? {
                    return Ok(None);
                }
                trial.resolve_instances(false)?;
                if holes
                    .iter()
                    .any(|id| trial.instance_goals.contains(id) && !trial.txn.mvars.is_assigned(id))
                {
                    return Ok(None);
                }
                if inside_out && !trial.discharge_rewrite_premises(&holes, selected_rules)? {
                    return Ok(None);
                }
                let value = trial.instantiate(&rule.value)?;
                let type_ = trial.instantiate(&rule.type_)?;
                if value.has_level_mvar()
                    || type_.has_level_mvar()
                    || inside_out && (value.has_expr_mvar() || type_.has_expr_mvar())
                {
                    return Ok(None);
                }
                let occurrence = trial.instantiate(term)?;
                if inside_out {
                    let (_, _, from, to) =
                        equality_target(&type_).expect("instantiated equality retains its shape");
                    let replacement = if reverse { from } else { to };
                    if trial.rewrite_same(&occurrence, &replacement)? {
                        return Ok(None);
                    }
                }
                let mut premises = Vec::new();
                if !inside_out {
                    for id in &holes {
                        trial.tick()?;
                        if trial.txn.mvars.is_assigned(id) {
                            continue;
                        }
                        let declaration = trial
                            .txn
                            .mvars
                            .get_decl(id)
                            .expect("rule parameter was declared")
                            .clone();
                        let target = trial.instantiate(&declaration.type_)?;
                        if let Some(universe) = trial.known_type(&target)? {
                            let universe = trial.whnf(&universe)?;
                            if matches!(universe.node(), ExprNode::Sort { level } if level.is_zero())
                            {
                                trial
                                    .txn
                                    .mvars
                                    .set_kind(id, MetavarKind::SyntheticOpaque)
                                    .map_err(|e| {
                                        failure(SourceInferenceError::Unification(Box::new(
                                            UnificationError::Metavariable(e),
                                        )))
                                    })?;
                            }
                        }
                        premises.push(ProofGoal {
                            id: id.clone(),
                            target,
                            lctx: declaration.lctx,
                            introduced: Vec::new(),
                        });
                    }
                }
                Ok(Some(RewriteMatch {
                    rule: Typed { value, type_ },
                    occurrence,
                    premises,
                }))
            })();
            self.charge_rewrite_trial(&trial);
            match attempt {
                Ok(Some(rule)) => {
                    *self = trial;
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
