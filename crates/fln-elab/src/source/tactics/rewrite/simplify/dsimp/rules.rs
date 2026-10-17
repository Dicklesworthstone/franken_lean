//! Recover reflexive-rule eligibility from admitted bodies, not theorem names.
//! The pin's inferred defeq attribute additionally requires the GENERIC equation
//! to hold at instances transparency. A particular lucky instantiation is not
//! enough to turn an arbitrary simp theorem into a dsimp theorem.
use super::*;

impl Context {
    pub(super) fn dsimp_rules<'a>(
        &mut self,
        selected: Vec<SimpRule<'a>>,
    ) -> Result<Rules<'a>, NatDefinitionElabError> {
        let mut rules = Rules::default();
        for rule in selected {
            self.tick()?;
            let mut trial = self.rewrite_trial();
            let classified = (|| {
                let term = trial.selected_simp_term(&rule)?;
                let bare = match &rule {
                    SimpRule::Explicit(rule) => matches!(rule.syntax, Syntax::Ident { .. }),
                    SimpRule::Global(entry) => entry.proof.is_none(),
                    SimpRule::Local(_) => false,
                };
                if bare && !trial.dsimp_is_proposition(&term.type_)? {
                    match term.value.node() {
                        ExprNode::Const { name, .. } => {
                            if let Some(ConstantInfo::Defn(definition)) = trial.txn.env.find(name)
                                && definition.safety == DefinitionSafety::Safe
                            {
                                if rule.reverse() { return Err(error(TacticError::MalformedScript)); }
                                rules.definitions.insert(name.clone(), definition.clone());
                                return Ok(());
                            }
                        }
                        ExprNode::FVar { id } => {
                            if let Some(local) = trial.txn.lctx.find(id)
                                && let Some(value) = &local.value
                            {
                                if rule.reverse() { return Err(error(TacticError::MalformedScript)); }
                                rules.lets.insert(id.clone(), value.clone());
                                return Ok(());
                            }
                        }
                        _ => {}
                    }
                    return Err(error(TacticError::InvalidSimpTheorem));
                }
                if !trial.dsimp_is_proposition(&term.type_)? {
                    return Err(error(TacticError::InvalidSimpTheorem));
                }
                if trial.dsimp_rfl_eligible(&term)? {
                    rules.reflexive.push(rule);
                }
                Ok(())
            })();
            self.charge_rewrite_trial(&trial);
            classified?;
        }
        Ok(rules)
    }

    fn dsimp_rfl_eligible(&mut self, term: &Typed) -> Result<bool, NatDefinitionElabError> {
        let mut type_ = term.type_.clone();
        let mut proof = term.value.clone();
        let mut seen = HashSet::new();
        loop {
            self.tick()?;
            // A reference to a theorem is checked at its full generic telescope,
            // including implicit binders that this application already filled.
            let mut head = &proof;
            let mut arguments = Vec::new();
            loop {
                self.tick()?;
                match head.node() {
                    ExprNode::App { f, a } => { arguments.push(a.clone()); head = f; }
                    ExprNode::MData { expr, .. } => head = expr,
                    _ => break,
                }
            }
            if let ExprNode::Const { name, .. } = head.node() {
                if (name == &Name::from_components(["Eq", "refl"])
                    || name == &Name::from_components(["rfl"])) && arguments.len() == 2
                {
                    return self.dsimp_generic_equation(&type_);
                }
                if name == &Name::from_components(["Eq", "symm"]) && arguments.len() == 4 {
                    proof = arguments[0].clone();
                    continue;
                }
                let Some(ConstantInfo::Thm(theorem)) = self.txn.env.find(name).cloned() else {
                    return Ok(false);
                };
                if !seen.insert(name.clone()) || !self.dsimp_generic_equation(&theorem.base.type_)? {
                    return Ok(false);
                }
                type_ = theorem.base.type_;
                proof = theorem.value;
                continue;
            }
            match (type_.node(), proof.node()) {
                (ExprNode::ForallE { body: type_body, .. }, ExprNode::Lam { body, .. }) => {
                    if !self.dsimp_generic_equation(&type_)? { return Ok(false); }
                    type_ = type_body.clone();
                    proof = body.clone();
                    // Structural descent deliberately leaves bound variables
                    // closed. The generic conversion was checked before descent.
                    // Once the body is Eq.refl, no loose-variable query is needed.
                    loop {
                        self.tick()?;
                        match (type_.node(), proof.node()) {
                            (ExprNode::ForallE { body: ty, .. }, ExprNode::Lam { body, .. }) => {
                                type_ = ty.clone(); proof = body.clone();
                            }
                            _ => break,
                        }
                    }
                    return self.dsimp_rfl_body(&proof, &mut seen);
                }
                _ => return Ok(false),
            }
        }
    }

    fn dsimp_rfl_body(
        &mut self,
        proof: &Expr,
        seen: &mut HashSet<Name>,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut current = proof.clone();
        loop {
            self.tick()?;
            let mut head = &current;
            let mut arguments = Vec::new();
            loop {
                self.tick()?;
                match head.node() {
                    ExprNode::App { f, a } => { arguments.push(a.clone()); head = f; }
                    ExprNode::MData { expr, .. } => head = expr,
                    // A referenced theorem's full value may have a telescope.
                    ExprNode::Lam { body, .. } if arguments.is_empty() => head = body,
                    _ => break,
                }
            }
            let ExprNode::Const { name, .. } = head.node() else { return Ok(false); };
            if (name == &Name::from_components(["Eq", "refl"])
                || name == &Name::from_components(["rfl"])) && arguments.len() == 2
            { return Ok(true); }
            if name == &Name::from_components(["Eq", "symm"]) && arguments.len() == 4 {
                current = arguments[0].clone();
                continue;
            }
            let Some(ConstantInfo::Thm(theorem)) = self.txn.env.find(name).cloned() else {
                return Ok(false);
            };
            if !seen.insert(name.clone()) || !self.dsimp_generic_equation(&theorem.base.type_)? {
                return Ok(false);
            }
            current = theorem.value;
        }
    }

    fn dsimp_generic_equation(&mut self, type_: &Expr) -> Result<bool, NatDefinitionElabError> {
        let mut trial = self.rewrite_trial();
        let result = (|| {
            let mut body = type_.clone();
            while let ExprNode::ForallE { binder_type, body: rest, .. } = body.node() {
                trial.tick()?;
                let local = trial.equality_local(binder_type.clone())?;
                let next = trial.substitute(rest, &Expr::fvar(local.id.clone()))?;
                eliminate::add_local(&mut trial.txn.lctx, &local);
                body = next;
            }
            let Some((_, _, left, right)) = equality_target(&body) else { return Ok(false); };
            let mut budget = UnificationBudget::new(trial.kernel);
            budget.transparency = UnificationTransparency::Instances;
            trial.proof_types_match_with_budget(&left, &right, budget)
        })();
        self.charge_rewrite_trial(&trial);
        result
    }

    pub(super) fn dsimp_rewrite_head(
        &mut self,
        expr: &Expr,
        rules: &Rules<'_>,
    ) -> Result<Expr, NatDefinitionElabError> {
        for rule in &rules.reflexive {
            self.tick()?;
            let mut trial = self.rewrite_trial();
            let result = (|| {
                let term = trial.selected_simp_term(rule)?;
                let Some(found) = trial.instantiate_rewrite_rule(term, expr, rule.reverse(), false, &[])? else {
                    return Ok(None);
                };
                // Traversal owns descent and proof exclusion. Never let the
                // rewrite matcher's search rewrite a hidden child or proof.
                if !found.premises.is_empty() || !trial.rewrite_same(expr, &found.occurrence)? {
                    return Ok(None);
                }
                let Some((_, _, left, right)) = equality_target(&found.rule.type_) else {
                    return Ok(None);
                };
                let next = trial.instantiate(if rule.reverse() { &left } else { &right })?;
                if next.has_expr_mvar() || next.has_level_mvar() || trial.rewrite_same(expr, &next)? {
                    return Ok(None);
                }
                let mut budget = UnificationBudget::new(trial.kernel);
                budget.transparency = UnificationTransparency::Instances;
                Ok(trial.proof_types_match_with_budget(expr, &next, budget)?.then_some(next))
            })();
            self.charge_rewrite_trial(&trial);
            if let Some(next) = result? { return Ok(next); }
        }
        Ok(expr.clone())
    }
}
