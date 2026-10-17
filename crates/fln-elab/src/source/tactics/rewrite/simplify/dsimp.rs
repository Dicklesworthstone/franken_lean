//! Definitional simplification is not propositional rewriting.
//!
//! The default syntax shares simp's immutable rule selection, but only selected
//! definitions/lets and reflexive equality rules can change an expression. No
//! Eq.rec/propext wrapper is manufactured. Final declaration admission still
//! checks the resulting proof against its original telescope in both seats.
mod reduce;
mod rules;
#[cfg(test)]
mod tests;

use super::*;
use fln_env::constants::DefinitionVal;

#[derive(Default)]
struct Rules<'a> {
    definitions: HashMap<Name, DefinitionVal>,
    lets: HashMap<FVarId, Expr>,
    reflexive: Vec<SimpRule<'a>>,
}

impl Context {
    pub(in crate::source) fn dsimplify_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, _, _, _, _, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "dsimp", "definitional simplification")?;
        self.txn.lctx = goal.lctx.clone();
        let selected = self.simp_rules(args)?;
        let rules = self.dsimp_rules(selected)?;
        let locations = self.rewrite_locations(location)?;
        let (hypotheses, target, all) = match locations {
            None => (Vec::new(), true, false),
            Some(locations) => (locations.hypotheses, locations.target, locations.all),
        };
        let eligible = if all {
            self.dsimp_nondependent_hypotheses(&goal)?
        } else {
            HashSet::new()
        };
        let mut changed = false;
        for name in hypotheses {
            self.tick()?;
            let local = goal.lctx.find_by_user_name(&name).cloned()
                .ok_or_else(|| error(TacticError::RewriteLocation))?;
            if all && !eligible.contains(&local.id) {
                continue;
            }
            let old = self.instantiate(&local.type_)?;
            let next = self.dsimp_expression(&old, &rules)?;
            // False elimination is permitted even when the selected hypothesis
            // was already False, including goals whose sort is not Prop.
            if matches!(next.node(), ExprNode::Const { name, levels }
                if name == &Name::from_components(["False"]) && levels.is_empty())
            {
                let sort = self.known_type(&goal.target)?
                    .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                let universe = self.sort_level(&Typed { value: goal.target.clone(), type_: sort })?;
                let binder = self.equality_local(next)?;
                let motive = self.close_equality_binder(&binder, goal.target.clone(), true)?;
                let value = app(
                    Expr::const_(Name::from_components(["False", "rec"]), vec![universe]),
                    [motive, Expr::fvar(local.id)],
                );
                return self.close_proof_goal(goal, value);
            }
            if !self.rewrite_same(&old, &next)? {
                // A defeq replacement preserves the local's identity, value,
                // binder information and every later dependent declaration.
                let mut context = LocalContext::new();
                for decl in goal.lctx.decls() {
                    self.tick()?;
                    let mut decl = decl.clone();
                    if decl.id == local.id { decl.type_ = next.clone(); }
                    eliminate::add_local(&mut context, &decl);
                }
                goal.lctx = context.clone();
                self.txn.lctx = context;
                changed = true;
            }
        }
        if target {
            let old = self.instantiate(&goal.target)?;
            let next = self.dsimp_expression(&old, &rules)?;
            changed |= !self.rewrite_same(&old, &next)?;
            goal.target = next;
            if matches!(goal.target.node(), ExprNode::Const { name, levels }
                if name == &Name::from_components(["True"]) && levels.is_empty())
            {
                let value = self.constant(&Name::from_components(["True", "intro"]))?.value;
                return self.close_proof_goal(goal, value);
            }
            // The pin's dsimpGoal closes Eq, not HEq or arbitrary assumptions.
            // Compare the original sides at reducible transparency; never use
            // the kernel's wider delta policy as an automatic tactic success.
            if let Some((level, domain, left, right)) = equality_target(&goal.target) {
                let mut trial = self.rewrite_trial();
                let mut budget = UnificationBudget::new(self.kernel);
                budget.transparency = UnificationTransparency::Abbreviations;
                let equal = trial.proof_types_match_with_budget(&left, &right, budget);
                self.charge_rewrite_trial(&trial);
                if equal? {
                    let value = app(
                        Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]),
                        [trial.instantiate(&domain)?, trial.instantiate(&left)?],
                    );
                    *self = trial;
                    return self.close_proof_goal(goal, value);
                }
            }
        }
        if !changed {
            return Err(error(TacticError::DefinitionalSimplificationNoProgress));
        }
        proof.work.push(Work::Goal(goal));
        Ok(())
    }

    fn dsimp_is_proposition(&mut self, type_: &Expr) -> Result<bool, NatDefinitionElabError> {
        let Some(sort) = self.known_type(type_)? else { return Ok(false); };
        let sort = self.whnf_with_transparency(&sort, UnificationTransparency::Abbreviations, true)?;
        Ok(matches!(sort.node(), ExprNode::Sort { level } if level.normalize().is_zero()))
    }

    // MVarId.getNondepPropHyps: later types AND let values, followed by the
    // target, remove candidates. Local lets themselves are never candidates.
    fn dsimp_nondependent_hypotheses(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<HashSet<FVarId>, NatDefinitionElabError> {
        let mut candidates = HashSet::new();
        for local in goal.lctx.decls() {
            self.tick()?;
            if self.is_matrix_hypothesis(local) { continue; }
            self.dsimp_remove_dependencies(&local.type_, &mut candidates)?;
            if let Some(value) = &local.value {
                self.dsimp_remove_dependencies(value, &mut candidates)?;
            } else if self.dsimp_is_proposition(&local.type_)? {
                candidates.insert(local.id.clone());
            }
        }
        self.dsimp_remove_dependencies(&goal.target, &mut candidates)?;
        Ok(candidates)
    }

    fn dsimp_remove_dependencies(
        &mut self,
        expr: &Expr,
        candidates: &mut HashSet<FVarId>,
    ) -> Result<(), NatDefinitionElabError> {
        let expr = self.instantiate(expr)?;
        let mut work = vec![&expr];
        let mut seen = HashSet::new();
        while let Some(expr) = work.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) { continue; }
            if let ExprNode::FVar { id } = expr.node() { candidates.remove(id); }
            work.extend(children(expr).into_iter().flatten());
        }
        Ok(())
    }
}
