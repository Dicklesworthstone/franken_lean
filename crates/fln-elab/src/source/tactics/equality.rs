//! Proof-producing equality substitution. Context changes are justified by an
//! ordinary Eq.rec term, never by assigning a free variable in the live context.
//! The entire dependency cone is abstracted before substitution and reintroduced
//! under fresh identities, including proof-dependent hypotheses and let values.
use super::*;
use std::collections::HashSet;

fn app<const N: usize>(head: Expr, args: [Expr; N]) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

pub(super) fn equation(level: Level, alpha: Expr, left: Expr, right: Expr) -> Expr {
    app(
        Expr::const_(Name::from_components(["Eq"]), vec![level]),
        [alpha, left, right],
    )
}
pub(super) fn reflexivity(level: Level, alpha: Expr, value: Expr) -> Expr {
    app(
        Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]),
        [alpha, value],
    )
}

impl Context {
    pub(super) fn close_equality_binder(
        &mut self,
        local: &LocalDecl,
        body: Expr,
        lambda: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        let body = body
            .abstract_fvar(&local.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let domain = self.instantiate(&local.type_)?;
        Ok(if let Some(value) = &local.value {
            Expr::let_e(
                local.user_name.clone(),
                domain,
                self.instantiate(value)?,
                body,
                false,
            )
        } else if lambda {
            Expr::lam(local.user_name.clone(), domain, body, local.binder_info)
        } else {
            Expr::forall_e(local.user_name.clone(), domain, body, local.binder_info)
        })
    }

    pub(super) fn equality_local(
        &mut self,
        type_: Expr,
    ) -> Result<LocalDecl, NatDefinitionElabError> {
        let name = self.fresh_name()?;
        Ok(LocalDecl {
            id: FVarId(name.clone()),
            user_name: name,
            type_,
            value: None,
            binder_info: BinderInfo::Default,
            index: 0,
        })
    }

    pub(super) fn symmetric_equality(
        &mut self,
        level: &Level,
        alpha: &Expr,
        left: &Expr,
        right: &Expr,
        proof: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let endpoint = self.equality_local(alpha.clone())?;
        let witness = self.equality_local(equation(
            level.clone(),
            alpha.clone(),
            left.clone(),
            Expr::fvar(endpoint.id.clone()),
        ))?;
        let result = equation(
            level.clone(),
            alpha.clone(),
            Expr::fvar(endpoint.id.clone()),
            left.clone(),
        );
        let result = self.close_equality_binder(&witness, result, true)?;
        let motive = self.close_equality_binder(&endpoint, result, true)?;
        Ok(app(
            Expr::const_(
                Name::from_components(["Eq", "rec"]),
                vec![Level::zero(), level.clone()],
            ),
            [
                alpha.clone(),
                left.clone(),
                motive,
                reflexivity(level.clone(), alpha.clone(), left.clone()),
                right.clone(),
                proof,
            ],
        ))
    }

    /// Validate an orientation before changing any context. Dependencies hidden
    /// by local let aliases count as occurrences, just like visible occurrences.
    fn substitution_orientation(
        &mut self,
        variable: &FVarId,
        witness: &FVarId,
        replacement: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<HashSet<FVarId>>, NatDefinitionElabError> {
        let Some(local) = locals.find(variable) else {
            return Ok(None);
        };
        if local.value.is_some() || variable == witness {
            return Ok(None);
        }
        let mut removed = HashSet::from([variable.clone(), witness.clone()]);
        for local in locals.decls() {
            self.tick()?;
            let mut reads = self.elimination_reads(&local.type_)?;
            if let Some(value) = &local.value {
                reads.extend(self.elimination_reads(value)?);
            }
            if reads.iter().any(|id| removed.contains(id)) {
                removed.insert(local.id.clone());
            }
        }
        if self
            .elimination_reads(replacement)?
            .iter()
            .any(|id| removed.contains(id))
            || self
                .elimination_reads(&local.type_)?
                .iter()
                .any(|id| removed.contains(id))
        {
            return Ok(None);
        }
        Ok(Some(removed))
    }

    /// Substitute a named equality, or locate an equality solving a named local.
    /// The returned child has no original variable/witness in scope. The parent
    /// closes only after the child proof is available, preserving introduced scopes.
    pub(super) fn substitute_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        name: &Name,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.resolve_instances(false)?;
        self.flush(false)?;
        let selected = goal
            .lctx
            .find_by_user_name(name)
            .cloned()
            .ok_or_else(|| error(TacticError::SubstitutionLocal))?;
        let selected_type = self.whnf(&selected.type_)?;
        let selected_is_eq = equality_target(&selected_type).is_some();
        let candidates: Vec<_> = if selected_is_eq {
            vec![selected]
        } else {
            goal.lctx.decls().iter().rev().cloned().collect()
        };
        let mut solution = None;
        for witness in candidates {
            self.tick()?;
            let type_ = self.whnf(&witness.type_)?;
            let Some((level, alpha, left, right)) = equality_target(&type_) else {
                continue;
            };
            for (candidate, replacement, reverse) in [(&left, &right, true), (&right, &left, false)]
            {
                let ExprNode::FVar { id } = candidate.node() else {
                    continue;
                };
                if !selected_is_eq
                    && goal
                        .lctx
                        .find_by_user_name(name)
                        .is_none_or(|local| local.id != *id)
                {
                    continue;
                }
                if let Some(removed) =
                    self.substitution_orientation(id, &witness.id, replacement, &goal.lctx)?
                {
                    solution = Some((
                        witness.clone(),
                        level.clone(),
                        alpha.clone(),
                        id.clone(),
                        replacement.clone(),
                        reverse,
                        removed,
                    ));
                    break;
                }
            }
            if solution.is_some() {
                break;
            }
        }
        let (witness, level, alpha, variable, replacement, reverse, removed) =
            solution.ok_or_else(|| error(TacticError::SubstitutionLocal))?;
        let reverted: Vec<_> = goal
            .lctx
            .decls()
            .iter()
            .filter(|local| removed.contains(&local.id) && local.id != variable)
            .cloned()
            .collect();
        let mut retained = LocalContext::new();
        for local in goal.lctx.decls() {
            if !removed.contains(&local.id) {
                eliminate::add_local(&mut retained, local);
            }
        }
        let mut generalized = self.instantiate(&goal.target)?;
        for local in reverted.iter().rev() {
            generalized = self.close_equality_binder(local, generalized, false)?;
        }
        let type_ = self
            .known_type(&generalized)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let universe = self.sort_level(&Typed {
            value: generalized.clone(),
            type_,
        })?;
        let endpoint = self.equality_local(alpha.clone())?;
        let evidence = self.equality_local(equation(
            level.clone(),
            alpha.clone(),
            replacement.clone(),
            Expr::fvar(endpoint.id.clone()),
        ))?;
        // Generalize the original equality as well as its dependent locals.
        // Passing it back explicitly avoids requiring proof irrelevance to
        // identify h with symm (symm h) in proof-dependent hypotheses.
        let body = self.specialize_locals(
            &generalized,
            &[(variable.clone(), Expr::fvar(endpoint.id.clone()))],
        )?;
        let body = self.close_equality_binder(&evidence, body, true)?;
        let motive = self.close_equality_binder(&endpoint, body, true)?;
        let mut replacements = vec![(variable.clone(), replacement.clone())];
        let target = self.specialize_locals(&generalized, &replacements)?;
        self.txn.lctx = retained;
        let (hole, mut child) = self.proof_goal(target)?;
        for local in &reverted {
            let name = if local.id == witness.id {
                Name::anonymous()
            } else {
                local.user_name.clone()
            };
            let type_ = self.specialize_locals(&local.type_, &replacements)?;
            let value = local
                .value
                .as_ref()
                .map(|value| self.specialize_locals(value, &replacements))
                .transpose()?;
            let id = FVarId(self.fresh_name()?);
            let fresh = LocalDecl {
                id: id.clone(),
                user_name: name,
                type_,
                value,
                binder_info: local.binder_info,
                index: self.txn.lctx.len(),
            };
            eliminate::add_local(&mut self.txn.lctx, &fresh);
            child.introduced.push(fresh);
            replacements.push((local.id.clone(), Expr::fvar(id)));
        }
        child.target = self.specialize_locals(&goal.target, &replacements)?;
        child.lctx = self.txn.lctx.clone();
        self.txn.lctx = goal.lctx.clone();
        let value = Expr::fvar(variable);
        let evidence = if reverse {
            self.symmetric_equality(&level, &alpha, &value, &replacement, Expr::fvar(witness.id))?
        } else {
            Expr::fvar(witness.id)
        };
        let mut result = app(
            Expr::const_(Name::from_components(["Eq", "rec"]), vec![universe, level]),
            [alpha, replacement, motive, hole, value, evidence],
        );
        for local in &reverted {
            if local.value.is_none() {
                result = Expr::app(result, Expr::fvar(local.id.clone()));
            }
        }
        proof.work.push(Work::Close(goal, result));
        proof.work.push(Work::Goal(child));
        Ok(())
    }
}
