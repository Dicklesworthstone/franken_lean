//! Checked index-equation refinement for case analysis.
//!
//! Generalize the discriminant's indices and value, retaining HEq premises which
//! relate them to the original inputs. Instantiate that telescope with reflexive
//! proofs at the call site. Constructor branches discharge those premises using
//! equality transport and constructor evidence, not by retyping local variables.
//! An omitted branch is accepted only after constructing its contradiction proof.
use super::*;
use fln_env::constants::InductiveVal;
use std::collections::{HashSet, VecDeque};

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

impl Context {
    fn refinement_relation(
        &mut self,
        left: &Typed,
        right: &Typed,
    ) -> Result<(Expr, Expr), NatDefinitionElabError> {
        let type_ = self
            .known_type(&left.type_)?
            .ok_or_else(|| error(TacticError::UnsupportedEliminator))?;
        let universe = self.sort_level(&Typed {
            value: left.type_.clone(),
            type_,
        })?;
        let type_ = self
            .known_type(&right.type_)?
            .ok_or_else(|| error(TacticError::UnsupportedEliminator))?;
        let other = self.sort_level(&Typed {
            value: right.type_.clone(),
            type_,
        })?;
        if universe != other {
            return Err(error(TacticError::UnsupportedEliminator));
        }
        let relation = apply(
            Expr::const_(Name::from_components(["HEq"]), vec![universe.clone()]),
            [
                left.type_.clone(),
                left.value.clone(),
                right.type_.clone(),
                right.value.clone(),
            ],
        );
        let reflexivity = apply(
            Expr::const_(Name::from_components(["HEq", "refl"]), vec![universe]),
            [left.type_.clone(), left.value.clone()],
        );
        Ok((relation, reflexivity))
    }

    /// A single bounded generalization step. The inner elimination sees fresh,
    /// distinct index parameters and therefore cannot re-enter this fallback.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn eliminate_constrained_indices<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        args: &'a [Syntax],
        major: &LocalDecl,
        family: &InductiveVal,
        levels: &[Level],
        parameters: &[Expr],
        indices: &[Expr],
    ) -> Result<(), NatDefinitionElabError> {
        let saved = goal.lctx.clone();
        self.txn.lctx = saved.clone();
        let mut telescope =
            self.instantiate_params(&family.base.type_, &family.base.level_params, levels)?;
        let mut family_value = Expr::const_(family.base.name.clone(), levels.to_vec());
        for parameter in parameters {
            self.tick()?;
            let current = self.whnf(&telescope)?;
            let ExprNode::ForallE { body, .. } = current.node() else {
                return Err(error(TacticError::UnsupportedEliminator));
            };
            telescope = self.substitute(body, parameter)?;
            family_value = Expr::app(family_value, parameter.clone());
        }
        let mut binders = Vec::new();
        let mut applications = Vec::new();
        let mut relations = Vec::new();
        for actual in indices {
            self.tick()?;
            let current = self.whnf(&telescope)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = current.node()
            else {
                return Err(error(TacticError::UnsupportedEliminator));
            };
            let mut local = self.equality_local(binder_type.clone())?;
            local.index = self.txn.lctx.len();
            eliminate::add_local(&mut self.txn.lctx, &local);
            let value = Expr::fvar(local.id.clone());
            let type_ = self
                .known_type(actual)?
                .ok_or_else(|| error(TacticError::UnsupportedEliminator))?;
            relations.push(self.refinement_relation(
                &Typed {
                    value: actual.clone(),
                    type_,
                },
                &Typed {
                    value: value.clone(),
                    type_: local.type_.clone(),
                },
            )?);
            telescope = self.substitute(body, &value)?;
            family_value = Expr::app(family_value, value);
            binders.push(local);
            applications.push(actual.clone());
        }
        let mut generic = self.equality_local(family_value)?;
        generic.index = self.txn.lctx.len();
        eliminate::add_local(&mut self.txn.lctx, &generic);
        relations.push(self.refinement_relation(
            &Typed {
                value: Expr::fvar(major.id.clone()),
                type_: major.type_.clone(),
            },
            &Typed {
                value: Expr::fvar(generic.id.clone()),
                type_: generic.type_.clone(),
            },
        )?);
        applications.push(Expr::fvar(major.id.clone()));
        binders.push(generic.clone());
        let mut equations = Vec::new();
        for (type_, reflexivity) in relations {
            self.tick()?;
            let mut local = self.equality_local(type_)?;
            local.index = self.txn.lctx.len();
            equations.push(local.user_name.clone());
            eliminate::add_local(&mut self.txn.lctx, &local);
            binders.push(local);
            applications.push(reflexivity);
        }
        let expanded = self.txn.lctx.clone();
        let mut type_ = goal.target.clone();
        for local in binders.iter().rev() {
            type_ = self.close_equality_binder(local, type_, false)?;
        }
        self.txn.lctx = saved;
        let (hole, mut inner) = self.proof_goal(type_)?;
        inner.target = goal.target.clone();
        inner.lctx = expanded.clone();
        inner.introduced = binders;
        proof
            .work
            .push(Work::Close(goal, apply(hole, applications)));
        self.txn.lctx = expanded;
        self.eliminate_proof_goal_with_indices(
            proof,
            inner,
            args,
            false,
            Some(&generic.id),
            Some(&equations),
        )
    }

    /// Restore speculative proof construction but never refund its work. The
    /// caller recognizes only ordinary tactic misses; resource and kernel
    /// nonanswers propagate rather than being turned into a skipped equation.
    fn restore_refinement_attempt(&mut self, mut saved: Self) {
        saved.txn.budget.heartbeats_consumed = self.txn.budget.heartbeats_consumed;
        *self = saved;
    }

    pub(super) fn refine_index_branch(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        equations: &[Name],
    ) -> Result<Option<ProofGoal>, NatDefinitionElabError> {
        let mut pending: VecDeque<_> = equations.iter().cloned().collect();
        loop {
            let mut progress = false;
            let mut deferred = VecDeque::new();
            while let Some(name) = pending.pop_front() {
                self.tick()?;
                self.txn.lctx = goal.lctx.clone();
                let Some(local) = goal.lctx.find_by_user_name(&name).cloned() else {
                    continue;
                };
                let type_ = self.whnf(&local.type_)?;
                let evidence = Typed {
                    value: Expr::fvar(local.id),
                    type_: type_.clone(),
                };
                if let Some(homogeneous) = self.homogeneous_equality_evidence(&evidence)? {
                    let (_, _, left, right) = equality_target(&homogeneous.type_)
                        .ok_or_else(|| error(TacticError::ExpectedEquality))?;
                    let left = self.whnf(&left)?;
                    let right = self.whnf(&right)?;
                    if self.proof_types_match(&left, &right)? {
                        continue;
                    }
                    if let Some(term) = self.refute_index_evidence(&homogeneous, &goal.target)? {
                        self.close_proof_goal(goal, term)?;
                        return Ok(None);
                    }
                }
                let saved = self.clone();
                let work = proof.work.len();
                match self.substitute_proof_goal_preserving_names(proof, goal.clone(), &name, true)
                {
                    Ok(()) => {
                        let Some(Work::Goal(child)) = proof.work.pop() else {
                            return Err(error(TacticError::MalformedScript));
                        };
                        goal = child;
                        progress = true;
                        continue;
                    }
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                        TacticError::SubstitutionLocal,
                    ))) => {
                        proof.work.truncate(work);
                        self.restore_refinement_attempt(saved);
                    }
                    Err(error) => return Err(error),
                }
                let before: HashSet<_> = goal
                    .lctx
                    .decls()
                    .iter()
                    .map(|local| local.id.clone())
                    .collect();
                let saved = self.clone();
                let work = proof.work.len();
                match self.inject_named_proof_goal(proof, goal.clone(), &name, &[]) {
                    Ok(()) if self.txn.mvars.is_assigned(&goal.id) => return Ok(None),
                    Ok(()) => {
                        let Some(Work::Goal(child)) = proof.work.pop() else {
                            return Err(error(TacticError::MalformedScript));
                        };
                        for local in child.lctx.decls().iter().rev() {
                            if !before.contains(&local.id) && !local.user_name.is_anonymous() {
                                pending.push_front(local.user_name.clone());
                            }
                        }
                        goal = child;
                        progress = true;
                    }
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                        TacticError::ConstructorEquality | TacticError::ExpectedEquality,
                    ))) => {
                        proof.work.truncate(work);
                        self.restore_refinement_attempt(saved);
                        deferred.push_back(name);
                    }
                    Err(error) => return Err(error),
                }
            }
            if !progress || deferred.is_empty() {
                self.txn.lctx = goal.lctx.clone();
                return Ok(Some(goal));
            }
            pending = deferred;
        }
    }
}
