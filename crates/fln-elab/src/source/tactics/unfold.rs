//! Explicit delta/zeta unfolding at proof-state locations.
//!
//! The selected reducer is shared with `simp only [name]`, but `unfold` changes
//! the goal/local types by definitional equality instead of manufacturing an
//! equality theorem. The final proof is still checked against the original
//! declaration telescope by both ordinary admission checkers.
use super::*;

impl Context {
    pub(super) fn unfold_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, names, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "unfold", "unfold tactic")?;
        let names = expect_null_args(names, "unfold declarations")?;
        if names.is_empty()
            || names
                .iter()
                .any(|name| !matches!(name, Syntax::Ident { val, .. } if !val.is_anonymous()))
        {
            return Err(error(TacticError::MalformedScript));
        }

        self.txn.lctx = goal.lctx.clone();
        let locations = self.rewrite_locations(location)?;
        let (hypotheses, target) = match locations {
            None => (Vec::new(), true),
            Some(locations) => (locations.hypotheses, locations.target),
        };

        let mut changed = false;
        if !hypotheses.is_empty() {
            let original = self.txn.lctx.clone();
            let mut updates = std::collections::HashMap::new();
            for name in hypotheses {
                self.tick()?;
                let local = original
                    .find_by_user_name(&name)
                    .cloned()
                    .ok_or_else(|| error(TacticError::RewriteLocation))?;
                let (type_, did_change) = self.unfold_tactic_expression(names, &local.type_)?;
                if did_change {
                    updates.insert(local.id.clone(), type_);
                    changed = true;
                }
            }
            if !updates.is_empty() {
                let mut context = LocalContext::new();
                for local in original.decls() {
                    self.tick()?;
                    let mut local = local.clone();
                    if let Some(type_) = updates.get(&local.id) {
                        local.type_ = type_.clone();
                    }
                    eliminate::add_local(&mut context, &local);
                }
                self.txn.lctx = context.clone();
                goal.lctx = context;
            }
        }

        if target {
            let (next, did_change) = self.unfold_tactic_expression(names, &goal.target)?;
            if did_change {
                goal.target = next;
                changed = true;
            }
        }

        if !changed {
            let name = match &names[0] {
                Syntax::Ident { val, .. } => val.clone(),
                _ => unreachable!("validated unfold name"),
            };
            return Err(error(TacticError::UnfoldFailed(name)));
        }
        proof.work.push(Work::Goal(goal));
        Ok(())
    }
}
