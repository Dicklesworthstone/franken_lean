//! Native definitional simplification, without equality-proof transport.
//!
//! Selection shares `simp`'s immutable rule set and lexical resolution. Only
//! selected safe definitions and structurally reflexive theorem rules reduce
//! expressions. A rule's replacement must also pass an independent conversion
//! probe; neither proof irrelevance nor an arbitrary equality grants permission
//! to change a type. The completed declaration still goes through both seats.
use super::unfold::Selection;
use super::*;

mod reduce;
mod rules;
#[cfg(test)]
mod tests;

#[derive(Default)]
struct DsimpSet<'a> {
    definitions: Vec<Selection>,
    /// Theorem rules in the set's order, each with whether it is structurally reflexive.
    /// A registered rule is classified the first time a node admits its key
    /// (`dsimp_rewrite`), as the pin retrieves candidates per node; classifying all of
    /// `Init`'s ~10,000 rules on every call exhausted the budget. The answer is kept for
    /// the rest of this call.
    rewrites: Vec<(SimpRule<'a>, std::cell::Cell<Option<bool>>)>,
    /// The `rfl`-tagged declarations a classification reads.
    tagged: std::collections::BTreeSet<Name>,
}

impl DsimpSet<'_> {
    fn unfolds(&self, name: &Name) -> bool {
        self.definitions.iter().any(|selection| {
            matches!(selection, Selection::Global(definition) if &definition.base.name == name)
        })
    }
}

impl Context {
    pub(in crate::source) fn dsimplify_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        // A bad late location or a resource stop must not expose a partially
        // changed context. The caller's work stack is touched only on success.
        let mut trial = self.rewrite_trial();
        let result = trial.dsimp_goal(goal, args);
        self.charge_rewrite_trial(&trial);
        if matches!(
            &result,
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ObservationComplete
            ))
        ) {
            // Preserve the read-only observation, never speculative assignments.
            self.inspection = trial.inspection.clone();
        }
        let next = result?;
        *self = trial;
        if let Some(goal) = next {
            proof.work.push(Work::Goal(goal));
        }
        Ok(())
    }

    fn dsimp_goal(
        &mut self,
        mut goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<Option<ProofGoal>, NatDefinitionElabError> {
        let [keyword, _, _, _, _, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "dsimp", "definitional simplification")?;
        self.txn.lctx = goal.lctx.clone();
        let set = self.dsimp_set(args)?;
        let locations = self.rewrite_locations(location)?;
        let (hypotheses, target) = match locations {
            None => (Vec::new(), true),
            Some(locations) if locations.all => (self.dsimp_nondependent_hypotheses(&goal)?, true),
            Some(locations) => {
                let mut ids = Vec::new();
                for name in locations.hypotheses {
                    self.tick()?;
                    let local = self
                        .txn
                        .lctx
                        .find_by_user_name(&name)
                        .ok_or_else(|| error(TacticError::RewriteLocation))?;
                    if !ids.contains(&local.id) {
                        ids.push(local.id.clone());
                    }
                }
                (ids, locations.target)
            }
        };
        let mut changed = false;
        for id in hypotheses {
            self.tick()?;
            let local = self
                .txn
                .lctx
                .find(&id)
                .cloned()
                .ok_or_else(|| error(TacticError::RewriteLocation))?;
            let original = self.instantiate(&local.type_)?;
            let next = self.dsimp_expression(&original, &set)?;
            if !self.simp_same_up_to_ascriptions(&original, &next)? {
                // Identity is preserved only for definitional equality. In
                // particular, this path never calls replace_rewritten_local.
                let mut context = LocalContext::new();
                for declaration in self.txn.lctx.decls().to_vec() {
                    self.tick()?;
                    let mut declaration = declaration;
                    if declaration.id == id {
                        declaration.type_ = next.clone();
                    }
                    eliminate::add_local(&mut context, &declaration);
                }
                self.txn.lctx = context.clone();
                goal.lctx = context;
                changed = true;
            }
            if matches!(next.node(), ExprNode::Const { name, levels }
                if name == &Name::from_components(["False"]) && levels.is_empty())
            {
                let sort = self
                    .known_type(&goal.target)?
                    .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                let level = self.sort_level(&Typed {
                    value: goal.target.clone(),
                    type_: sort,
                })?;
                // Resolve first, so an absent eliminator is a typed refusal.
                self.constant(&Name::from_components(["False", "elim"]))?;
                let value = app(
                    Expr::const_(Name::from_components(["False", "elim"]), vec![level]),
                    [goal.target.clone(), Expr::fvar(id)],
                );
                self.close_proof_goal(goal, value)?;
                return Ok(None);
            }
        }
        if target {
            let original = self.instantiate(&goal.target)?;
            let next = self.dsimp_expression(&original, &set)?;
            changed |= !self.simp_same_up_to_ascriptions(&original, &next)?;
            goal.target = next;
            if let Some(value) = self.dsimp_reflexivity(&goal.target)? {
                self.close_proof_goal(goal, value)?;
                return Ok(None);
            }
        }
        if !changed {
            return Err(error(TacticError::DefinitionalSimplificationNoProgress));
        }
        Ok(Some(goal))
    }

    /// The pin's wildcard selects non-let, nondependent proposition hypotheses,
    /// not every data variable and not proofs referenced by later declarations.
    fn dsimp_nondependent_hypotheses(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Vec<FVarId>, NatDefinitionElabError> {
        let mut candidates = HashSet::new();
        for local in goal.lctx.decls() {
            self.tick()?;
            if self.is_matrix_hypothesis(local) {
                continue;
            }
            let type_ = self.instantiate(&local.type_)?;
            for id in self.elimination_reads(&type_)? {
                candidates.remove(&id);
            }
            if let Some(value) = &local.value {
                let value = self.instantiate(value)?;
                for id in self.elimination_reads(&value)? {
                    candidates.remove(&id);
                }
            } else if self.dsimp_is_proposition(&type_)? {
                candidates.insert(local.id.clone());
            }
        }
        let target = self.instantiate(&goal.target)?;
        for id in self.elimination_reads(&target)? {
            candidates.remove(&id);
        }
        Ok(goal
            .lctx
            .decls()
            .iter()
            .filter(|local| candidates.contains(&local.id))
            .map(|local| local.id.clone())
            .collect())
    }

    fn dsimp_is_proposition(&mut self, type_: &Expr) -> Result<bool, NatDefinitionElabError> {
        let Some(sort) = self.known_type(type_)? else {
            return Ok(false);
        };
        let sort = self.whnf(&sort)?;
        Ok(matches!(sort.node(), ExprNode::Sort { level } if level.normalize().is_zero()))
    }

    /// dsimp closes True and homogeneous reflexive equality, not Iff/HEq,
    /// arbitrary assumptions, arithmetic procedures, or full-delta conversion.
    fn dsimp_reflexivity(&mut self, target: &Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
        if matches!(target.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(["True"]) && levels.is_empty())
        {
            return Ok(Some(
                self.constant(&Name::from_components(["True", "intro"]))?
                    .value,
            ));
        }
        let Some((level, domain, left, right)) = equality_target(target) else {
            return Ok(None);
        };
        let mut trial = self.rewrite_trial();
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::Abbreviations;
        budget.zeta_delta = false;
        let result = (|| {
            // Eta may establish reflexivity, but it must not rewrite a record
            // argument elsewhere in the goal or claim dsimp made progress.
            let compared_left = trial.dsimp_eta_comparison(&left)?;
            let compared_right = trial.dsimp_eta_comparison(&right)?;
            if !trial.proof_types_match_with_budget(&compared_left, &compared_right, budget)? {
                return Ok(None);
            }
            trial.constant(&Name::from_components(["Eq", "refl"]))?;
            let candidate = app(
                Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]),
                [domain, left],
            );
            Ok(Some(trial.instantiate(&candidate)?))
        })();
        self.charge_rewrite_trial(&trial);
        match result? {
            Some(candidate) => {
                *self = trial;
                Ok(Some(candidate))
            }
            None => Ok(None),
        }
    }
}
