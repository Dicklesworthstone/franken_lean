//! Reflexivity classification is structural, never proof-irrelevance conversion.
use super::*;

impl Context {
    pub(super) fn dsimp_set<'a>(
        &mut self,
        args: &'a [Syntax],
    ) -> Result<DsimpSet<'a>, NatDefinitionElabError> {
        let environment = self.txn.env.clone();
        let tagged = scope::simp::defeq::read(&environment, || self.tick())?;
        let mut set = DsimpSet {
            definitions: Vec::new(),
            rewrites: Vec::new(),
            tagged,
        };
        for rule in self.simp_rules(args)? {
            // A registered theorem is classified only when a node admits its key.
            if matches!(rule, SimpRule::Global(_)) && !self.simp_rule_may_unfold(&rule) {
                set.rewrites.push((rule, std::cell::Cell::new(None)));
                continue;
            }
            self.tick()?;
            // Eligibility probes are not instance-synthesis/admission effects.
            // Resolve fully and charge each candidate without keeping its holes.
            let mut trial = self.rewrite_trial();
            let classified = (|| {
                if let Some(selection) = trial.simp_unfold_selection_for_rule(&rule)? {
                    return Ok((Some(selection), false));
                }
                Ok((None, trial.dsimp_reflexive_rule(&rule, &set.tagged)?))
            })();
            self.charge_rewrite_trial(&trial);
            let (selection, reflexive) = classified?;
            if let Some(selection) = selection {
                set.definitions.push(selection);
            }
            if reflexive {
                set.rewrites.push((rule, std::cell::Cell::new(Some(true))));
            }
        }
        Ok(set)
    }

    /// Whether a theorem rule is structurally reflexive: a proposition whose proof is
    /// `rfl` (or carries the pin's `rfl` tag). A non-proposition is a malformed rule.
    fn dsimp_reflexive_rule(
        &mut self,
        rule: &SimpRule<'_>,
        tagged: &std::collections::BTreeSet<Name>,
    ) -> Result<bool, NatDefinitionElabError> {
        let term = self.selected_simp_term(rule)?;
        if !self.dsimp_is_proposition(&term.type_)? {
            return Err(error(TacticError::InvalidSimpTheorem));
        }
        self.dsimp_rfl_proof(term, tagged)
    }

    pub(super) fn dsimp_spine(
        &mut self,
        term: &Expr,
    ) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = term.clone();
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                _ => break,
            }
        }
        arguments.reverse();
        Ok((head, arguments))
    }

    /// Constant proofs are classified by source metadata, not by unfolding
    /// theorem bodies. Parenthesized/tactic proofs do not implicitly acquire the
    /// pin's automatic `:= rfl` tag. Nonconstant reflexivity proofs retain the
    /// structural Eq.refl / rfl / Eq.symm cases from the pinned implementation.
    pub(in crate::source) fn dsimp_rfl_proof(
        &mut self,
        mut term: Typed,
        tagged: &std::collections::BTreeSet<Name>,
    ) -> Result<bool, NatDefinitionElabError> {
        loop {
            self.tick()?;
            if let ExprNode::Const { name, .. } = term.value.node() {
                return Ok(tagged.contains(name));
            }
            while let ExprNode::ForallE {
                body: type_body, ..
            } = term.type_.node()
            {
                self.tick()?;
                let ExprNode::Lam { body, .. } = term.value.node() else {
                    return Ok(false);
                };
                term = Typed {
                    value: body.clone(),
                    type_: type_body.clone(),
                };
            }
            if equality_target(&term.type_).is_none() {
                return Ok(false);
            }
            let (head, arguments) = self.dsimp_spine(&term.value)?;
            let ExprNode::Const { name, .. } = head.node() else {
                return Ok(false);
            };
            if arguments.len() == 2
                && (name == &Name::from_components(["Eq", "refl"])
                    || name == &Name::from_components(["rfl"]))
            {
                return Ok(true);
            }
            if name == &Name::from_components(["Eq", "symm"]) && arguments.len() == 4 {
                term.value = arguments[3].clone();
                continue;
            }
            return Ok(tagged.contains(name));
        }
    }

    /// Validate the whole user theorem with rigid parameters, never a lucky
    /// use-site specialization. Naked source `:= rfl` prepends the explicit
    /// defeq attribute in the pin; that validator allows safe delta, including
    /// irreducible definitions. Generated-equation inference is a different API.
    /// Arbitrary local equality evidence does not enter this metadata path.
    pub(in crate::source) fn dsimp_generic_defeq(
        &mut self,
        type_: &Expr,
        levels: &[Name],
    ) -> Result<bool, NatDefinitionElabError> {
        let mut trial = self.rewrite_trial();
        let result = (|| {
            for level in levels {
                trial.tick()?;
                if !trial.level_params.contains(level) {
                    trial.level_params.push(level.clone());
                }
            }
            let mut target = type_.clone();
            loop {
                trial.tick()?;
                target = trial.whnf_with_transparency(
                    &target,
                    UnificationTransparency::SafeDefinitions,
                    false,
                )?;
                let ExprNode::ForallE {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } = target.node()
                else {
                    break;
                };
                let mut local = trial.equality_local(binder_type.clone())?;
                local.binder_info = *binder_info;
                eliminate::add_local(&mut trial.txn.lctx, &local);
                target = trial.substitute(body, &Expr::fvar(local.id))?;
            }
            let Some((_, _, left, right)) = equality_target(&target) else {
                return Ok(false);
            };
            let mut budget = UnificationBudget::new(trial.kernel);
            budget.transparency = UnificationTransparency::SafeDefinitions;
            budget.zeta_delta = false;
            trial.proof_types_match_with_budget(&left, &right, budget)
        })();
        self.charge_rewrite_trial(&trial);
        result
    }

    /// Try at this exact node. The caller has already selected which children
    /// are eligible; a recursive rule search would violate that decision.
    pub(super) fn dsimp_rewrite(
        &mut self,
        target: &Expr,
        set: &DsimpSet<'_>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let index = self.simp_root_index(target)?;
        for (rule, reflexive) in &set.rewrites {
            if !self.simp_rule_admitted(rule, index.as_ref(), SimpKeySide::Rewrite) {
                continue;
            }
            if reflexive.get().is_none() {
                self.tick()?;
                let mut trial = self.rewrite_trial();
                let classified = trial.dsimp_reflexive_rule(rule, &set.tagged);
                self.charge_rewrite_trial(&trial);
                reflexive.set(Some(classified?));
            }
            if reflexive.get() != Some(true) {
                continue;
            }
            self.tick()?;
            let mut trial = self.rewrite_trial();
            let attempt = (|| {
                let term = trial.selected_simp_term(rule)?;
                let Some(found) = trial.instantiate_dsimp_rule(term, target, rule.reverse())?
                else {
                    return Ok(None);
                };
                if !found.premises.is_empty() || !trial.rewrite_same(target, &found.occurrence)? {
                    return Err(error(TacticError::MalformedScript));
                }
                let (_, _, left, right) = equality_target(&found.rule.type_)
                    .ok_or_else(|| error(TacticError::ExpectedEquality))?;
                let replacement = if rule.reverse() { left } else { right };
                // Matching remains at the selected-rule policy. Only after a
                // tagged, admitted reflexivity rule matches may its replacement
                // use the attribute validator's stronger conversion policy.
                let mut budget = UnificationBudget::new(trial.kernel);
                budget.transparency = UnificationTransparency::SafeDefinitions;
                budget.zeta_delta = false;
                if !trial.proof_types_match_with_budget(target, &replacement, budget)? {
                    return Ok(None);
                }
                let replacement = trial.instantiate(&replacement)?;
                if trial.rewrite_same(target, &replacement)? {
                    return Ok(None);
                }
                Ok(Some(replacement))
            })();
            self.charge_rewrite_trial(&trial);
            match attempt? {
                Some(next) => {
                    *self = trial;
                    return Ok(next);
                }
                None => continue,
            }
        }
        Ok(target.clone())
    }
}
