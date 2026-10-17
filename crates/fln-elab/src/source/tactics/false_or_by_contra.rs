//! Native `false_or_by_contra`, using admitted elimination theorems only.
//!
//! The reference is Lean/Elab/Tactic/FalseOrByContra.lean at the SUITE.lock pin.
//! Introductions and applications use the ordinary proof worklist: an open
//! contradiction is an obligation, not a proof or an admission certificate.
use super::*;

struct Application {
    work: Vec<Work<'static>>,
    goal: Option<ProofGoal>,
}

impl Context {
    pub(super) fn false_or_by_contra_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        // Stage the entire frontier, not just its final application. A failure
        // after introducing dependent binders must not leak locals, holes,
        // assignments, goal tags or instance goals into an alternative.
        let snapshot = self.clone();
        match self.false_or_by_contra_frontier(goal) {
            Ok(work) => {
                proof.work.extend(work);
                Ok(())
            }
            Err(problem) => {
                let spent = self.txn.budget.heartbeats_consumed;
                *self = snapshot;
                self.txn.budget.heartbeats_consumed = spent;
                Err(problem)
            }
        }
    }

    fn false_or_by_contra_frontier(
        &mut self,
        mut goal: ProofGoal,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        let false_name = Name::from_components(["False"]);
        let not_name = Name::from_components(["Not"]);
        loop {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            // Match the reference's whnfR for classification. Introduction
            // itself uses ordinary transparency, through the existing helper.
            let target = self.whnf_with_transparency(
                &goal.target,
                UnificationTransparency::Abbreviations,
                true,
            )?;
            if matches!(target.node(), ExprNode::Const { name, .. } if name == &false_name) {
                return Ok(vec![Work::Goal(goal)]);
            }
            let negation = matches!(target.node(), ExprNode::App { f, .. }
                if matches!(f.node(), ExprNode::Const { name, .. } if name == &not_name));
            if matches!(target.node(), ExprNode::ForallE { .. }) || negation {
                let name = self.fresh_name()?;
                self.introduce_proof_binder(&mut goal, name)?;
                goal.lctx = self.txn.lctx.clone();
                continue;
            }
            break;
        }

        let sort = self
            .known_type(&goal.target)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let proposition = self.proof_types_match(&sort, &Expr::sort(Level::zero()))?;
        let mut application = if proposition {
            // A local/ordinary Decidable dictionary takes precedence. Only an
            // ordinary failure of this application permits the classical
            // alternative; resource stops, cancellation and faults propagate.
            let snapshot = self.clone();
            match self.false_or_by_contra_apply(goal.clone(), "Decidable.byContradiction") {
                Ok(application) => application,
                Err(problem) if backtrack::recoverable(&problem) => {
                    let spent = self.txn.budget.heartbeats_consumed;
                    *self = snapshot;
                    self.txn.budget.heartbeats_consumed = spent;
                    self.false_or_by_contra_apply(goal, "Classical.byContradiction")?
                }
                Err(problem) => return Err(problem),
            }
        } else {
            self.false_or_by_contra_apply(goal, "False.elim")?
        };
        if let Some(mut child) = application.goal {
            if proposition {
                self.txn.lctx = child.lctx.clone();
                let name = self.fresh_name()?;
                self.introduce_proof_binder(&mut child, name)?;
                child.lctx = self.txn.lctx.clone();
            }
            application.work.push(Work::Goal(child));
        }
        Ok(application.work)
    }

    fn false_or_by_contra_apply(
        &mut self,
        goal: ProofGoal,
        name: &str,
    ) -> Result<Application, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let mut proof = introductions::frame(&goal);
        let instance_start = self.instance_goals.len();
        let term = self.constant(&Name::from_components(name.split('.')))?;
        self.apply_proof_term(&mut proof, goal, term, instance_start)?;
        let mut work = Vec::new();
        let mut remaining = None;
        for item in proof.work {
            self.tick()?;
            match item {
                Work::Goal(goal) => {
                    // Conclusion matching also puts already assigned implicit
                    // arguments in this list. They are not new obligations.
                    if self.txn.mvars.is_assigned(&goal.id) {
                        continue;
                    }
                    if remaining.is_some() {
                        // The reference requires at most one subgoal here.
                        // Never discard extra obligations from an unexpected
                        // declaration registered under one of these names.
                        return Err(error(TacticError::MalformedScript));
                    }
                    remaining = Some(goal);
                }
                item @ Work::Close(..) => work.push(item),
                _ => return Err(error(TacticError::MalformedScript)),
            }
        }
        Ok(Application {
            work,
            goal: remaining,
        })
    }
}
