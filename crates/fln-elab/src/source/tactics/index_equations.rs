//! Checked index-equation refinement for case analysis and induction.
//!
//! Generalize the discriminant's indices and value, retaining HEq premises which
//! relate them to the original inputs. Instantiate that telescope with reflexive
//! proofs at the call site. Constructor branches discharge those premises using
//! equality transport and constructor evidence, not by retyping local variables.
//! An omitted branch is accepted only after constructing its contradiction proof.
use super::*;
use fln_env::constants::InductiveVal;
use std::collections::{HashSet, VecDeque};

/// Equations are returned parameters of the generalized motive. For induction
/// the original major must also be quantified: an IH relates its own child to
/// an arbitrary value at the constrained type, never to the original input.
pub(super) struct IndexEquations {
    pub names: Vec<Name>,
    pub induction_major: Option<FVarId>,
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

impl Context {
    /// Specialize a conditional IH only using its generated reflexive index
    /// equations. This chooses a child as a returned argument of the IH, never
    /// identifies the child with the original major. Unsolved equations and
    /// ordinary generalized parameters remain universally quantified.
    pub(super) fn specialize_index_hypothesis(
        &mut self,
        branch: &mut ProofGoal,
        internal: &Name,
        public: Name,
        reverted: &[LocalDecl],
        equations: &IndexEquations,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = branch.lctx.clone();
        let hypothesis = branch
            .lctx
            .find_by_user_name(internal)
            .cloned()
            .ok_or_else(|| error(TacticError::UnsupportedEliminator))?;
        let result =
            self.specialize_index_hypothesis_inner(hypothesis.clone(), reverted, equations);
        // Temporary telescope binders never escape on a resource/type stop.
        self.txn.lctx = branch.lctx.clone();
        let (value, type_) = result?;
        // Preserve the existing explicit IH application API. The public name
        // still denotes the full conditional hypothesis, not its specialization.
        let original = LocalDecl {
            id: FVarId(self.fresh_name()?),
            user_name: public,
            type_: hypothesis.type_,
            value: Some(Expr::fvar(hypothesis.id)),
            binder_info: BinderInfo::Default,
            index: self.txn.lctx.len(),
        };
        eliminate::add_local(&mut self.txn.lctx, &original);
        branch.introduced.push(original);
        let specialized = self.fresh_name()?;
        let alias = LocalDecl {
            id: FVarId(specialized.clone()),
            user_name: specialized.clone(),
            type_,
            value: Some(value),
            binder_info: BinderInfo::Default,
            index: self.txn.lctx.len(),
        };
        eliminate::add_local(&mut self.txn.lctx, &alias);
        branch.introduced.push(alias);
        branch.lctx = self.txn.lctx.clone();
        self.induction_specializations
            .push((internal.clone(), specialized));
        Ok(())
    }

    fn specialize_index_hypothesis_inner(
        &mut self,
        hypothesis: LocalDecl,
        reverted: &[LocalDecl],
        equations: &IndexEquations,
    ) -> Result<(Expr, Expr), NatDefinitionElabError> {
        let mut value = Expr::fvar(hypothesis.id);
        let mut type_ = hypothesis.type_;
        let mut opened = Vec::new();
        // Reverted lets are definitions, not arguments. Weak-head reduction of
        // the following telescope position substitutes their values as usual.
        for original in reverted.iter().filter(|local| local.value.is_none()) {
            self.tick()?;
            let current = self.whnf(&type_)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = current.node()
            else {
                return Err(error(TacticError::UnsupportedEliminator));
            };
            let mut local = self.equality_local(binder_type.clone())?;
            local.binder_info = *binder_info;
            local.index = self.txn.lctx.len();
            eliminate::add_local(&mut self.txn.lctx, &local);
            let argument = Expr::fvar(local.id.clone());
            value = Expr::app(value, argument.clone());
            type_ = self.substitute(body, &argument)?;
            opened.push((local, equations.names.contains(&original.user_name)));
        }
        let temporary: HashSet<_> = opened.iter().map(|(local, _)| local.id.clone()).collect();
        let mut replacements = Vec::new();
        for (equation, generated) in &opened {
            if !generated {
                continue;
            }
            self.tick()?;
            let target = self.specialize_locals(&equation.type_, &replacements)?;
            let target = self.whnf(&target)?;
            let (level, alpha, left, beta, right, heterogeneous) =
                if let Some((level, alpha, left, beta, right)) =
                    equality::heterogeneous_target(&target)
                {
                    (level, alpha, left, beta, right, true)
                } else if let Some((level, alpha, left, right)) = equality_target(&target) {
                    (level, alpha.clone(), left, alpha, right, false)
                } else {
                    continue;
                };
            if !self.proof_types_match(&alpha, &beta)? {
                continue;
            }
            let mut left = self.whnf(&left)?;
            let mut right = self.whnf(&right)?;
            // Only these freshly opened parameters can be instantiated. The
            // replacement must live in the existing branch, not depend on a
            // later temporary binder or introduce a cyclic substitution.
            for (endpoint, other) in [(&left, &right), (&right, &left)] {
                if let ExprNode::FVar { id } = endpoint.node()
                    && temporary.contains(id)
                    && self.elimination_reads(other)?.is_disjoint(&temporary)
                {
                    replacements.push((id.clone(), other.clone()));
                    break;
                }
            }
            left = self.specialize_locals(&left, &replacements)?;
            right = self.specialize_locals(&right, &replacements)?;
            if self.proof_types_match(&left, &right)? {
                let alpha = self.specialize_locals(&alpha, &replacements)?;
                let proof = apply(
                    Expr::const_(
                        Name::from_components([if heterogeneous { "HEq" } else { "Eq" }, "refl"]),
                        vec![level],
                    ),
                    [alpha, left],
                );
                replacements.push((equation.id.clone(), proof));
            }
        }
        value = self.specialize_locals(&value, &replacements)?;
        type_ = self.specialize_locals(&type_, &replacements)?;
        for (mut local, _) in opened.into_iter().rev() {
            if replacements.iter().any(|(id, _)| id == &local.id) {
                continue;
            }
            local.type_ = self.specialize_locals(&local.type_, &replacements)?;
            value = self.close_equality_binder(&local, value, true)?;
            type_ = self.close_equality_binder(&local, type_, false)?;
        }
        Ok((value, type_))
    }

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
        input: &eliminate::EliminationSyntax<'a>,
        induction: bool,
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
        let equations = IndexEquations {
            names: equations,
            induction_major: induction.then(|| major.id.clone()),
        };
        self.eliminate_proof_goal_with_indices(
            proof,
            inner,
            input,
            induction,
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
