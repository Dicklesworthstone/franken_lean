//! Telescopic generalization for multiple rcases/obtain targets. Construct the
//! complete universal statement before opening any target, so later target
//! domains are abstracted together with the goal (`Meta/Tactic/Generalize.lean`).
use super::*;

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

impl Context {
    pub(super) fn generalize_rcases_targets(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        mut targets: Vec<(Name, Option<Name>, Typed)>,
    ) -> Result<(ProofGoal, Vec<FVarId>), NatDefinitionElabError> {
        if targets.len() == 1 {
            let (name, equation, term) = targets.pop().expect("one target");
            let (child, id) = self.generalized_proof_goal(proof, goal, name, equation, term)?;
            return Ok((child, vec![id]));
        }
        self.txn.lctx = goal.lctx.clone();
        let mut target = self.instantiate(&goal.target)?;
        // Fold from the last target: abstracting an earlier expression also
        // changes the types of the later binders. Sequential generalize calls
        // would leave those dependent types referring to the original term.
        for (name, equation, term) in targets.iter().rev() {
            self.tick()?;
            if name.is_anonymous()
                || equation
                    .as_ref()
                    .is_some_and(|h| h.is_anonymous() || h == name)
            {
                return Err(error(TacticError::InvalidGeneralization));
            }
            let marker = FVarId(self.fresh_name()?);
            let (body, _) =
                self.rewrite_template(&target, &term.value, &Expr::fvar(marker.clone()))?;
            target = Expr::forall_e(
                name.clone(),
                term.type_.clone(),
                body.abstract_fvar(&marker, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                BinderInfo::Default,
            );
        }

        // Open temporary parameters only to construct the optional equations.
        // Their identities are closed out before allocating the actual goal.
        let mut binders = Vec::new();
        for (name, _, _) in &targets {
            self.tick()?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = target.node()
            else {
                return Err(error(TacticError::InvalidGeneralization));
            };
            let local = LocalDecl {
                id: FVarId(self.fresh_name()?),
                user_name: name.clone(),
                type_: binder_type.clone(),
                value: None,
                binder_info: BinderInfo::Default,
                index: self.txn.lctx.len(),
            };
            target = self.substitute(body, &Expr::fvar(local.id.clone()))?;
            eliminate::add_local(&mut self.txn.lctx, &local);
            binders.push(local);
        }
        let mut equations = Vec::new();
        let mut reflexivities = Vec::new();
        for ((_, equation, term), local) in targets.iter().zip(&binders) {
            self.tick()?;
            let Some(name) = equation else { continue };
            let sort = self
                .known_type(&term.type_)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let level = self.sort_level(&Typed {
                value: term.type_.clone(),
                type_: sort,
            })?;
            let homogeneous = self.proof_types_match(&term.type_, &local.type_)?;
            let equality = if homogeneous { "Eq" } else { "HEq" };
            let mut arguments = vec![term.type_.clone(), term.value.clone()];
            if !homogeneous {
                let sort = self
                    .known_type(&local.type_)?
                    .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                let other = self.sort_level(&Typed {
                    value: local.type_.clone(),
                    type_: sort,
                })?;
                if level != other {
                    return Err(error(TacticError::InvalidGeneralization));
                }
                arguments.push(local.type_.clone());
            }
            arguments.push(Expr::fvar(local.id.clone()));
            equations.push((
                name.clone(),
                apply(
                    Expr::const_(Name::from_components([equality]), vec![level.clone()]),
                    arguments,
                ),
            ));
            reflexivities.push(apply(
                Expr::const_(Name::from_components([equality, "refl"]), vec![level]),
                [term.type_.clone(), term.value.clone()],
            ));
        }
        for (name, equation) in equations.iter().rev() {
            self.tick()?;
            target = Expr::forall_e(name.clone(), equation.clone(), target, BinderInfo::Default);
        }
        for local in binders.iter().rev() {
            target = self.close_equality_binder(local, target, false)?;
        }
        self.txn.lctx = goal.lctx.clone();

        // Validate the universal telescope, not merely its specialization back
        // to the old arguments. As in ordinary generalize, its asserted type is
        // retained by a let in the final kernel-checked proof.
        let sort = self
            .known_type(&target)?
            .ok_or_else(|| error(TacticError::InvalidGeneralization))?;
        let check = self.hole(sort)?;
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::SafeDefinitions;
        let report = self
            .txn
            .unify(&check, &target, budget)
            .map_err(|reason| failure(SourceInferenceError::Unification(Box::new(reason))))?;
        assert!(report.awakened.is_empty(), "private source queue");
        let (root, mut child) = self.proof_goal(target.clone())?;
        self.inherit_goal_tag(&goal, &child);
        let mut ids = Vec::new();
        for (name, _, _) in &targets {
            self.introduce_proof_binder(&mut child, name.clone())?;
            ids.push(
                child
                    .introduced
                    .last()
                    .expect("generalized target binder")
                    .id
                    .clone(),
            );
        }
        for (name, _) in equations {
            self.introduce_proof_binder(&mut child, name)?;
        }
        child.lctx = self.txn.lctx.clone();
        let mut value = Expr::bvar(0).expect("generalized theorem binder");
        for (_, _, term) in targets {
            self.tick()?;
            value = Expr::app(value, term.value);
        }
        for reflexivity in reflexivities {
            self.tick()?;
            value = Expr::app(value, reflexivity);
        }
        let value = Expr::let_e(self.fresh_name()?, target, root, value, false);
        proof.work.push(Work::Close(goal, value));
        Ok((child, ids))
    }
}
