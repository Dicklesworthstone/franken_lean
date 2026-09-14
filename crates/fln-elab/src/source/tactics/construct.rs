//! Constructor tactics use ordinary application, never a new admission rule.
use super::*;
use fln_env::constants::ConstantInfo;

impl Context {
    pub(super) fn construct_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        selected: Option<usize>,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let target = self.whnf(&goal.target)?;
        let mut head = &target;
        while let ExprNode::App { f, .. } = head.node() {
            self.tick()?;
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(error(TacticError::NoConstructor));
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(name).cloned() else {
            return Err(error(TacticError::NoConstructor));
        };
        if selected.is_some() && family.ctors.len() != 2 {
            return Err(error(TacticError::ExpectedTwoConstructors));
        }
        let candidates: Vec<_> = match selected {
            Some(index) => vec![family.ctors[index].clone()],
            None => family.ctors.clone(),
        };
        let snapshot = self.clone();
        for constructor in candidates {
            // All application failures precede worklist publication. Inference
            // changes from an index mismatch or unavailable instance must not
            // contaminate the next constructor, and work is never refunded.
            let spent = self.txn.budget.heartbeats_consumed;
            *self = snapshot.clone();
            self.txn.budget.heartbeats_consumed = spent;
            self.tick()?;
            let Some(ConstantInfo::Ctor(info)) = self.txn.env.find(&constructor) else {
                return Err(error(TacticError::NoConstructor));
            };
            if info.induct != family.base.name || info.num_params != family.num_params {
                return Err(error(TacticError::NoConstructor));
            }
            let instance_start = self.instance_goals.len();
            let term = self.constant(&constructor)?;
            match self.apply_proof_term(proof, goal.clone(), term, instance_start) {
                Ok(()) => return Ok(()),
                Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                    TacticError::ApplyMismatch,
                ))) => {}
                Err(problem) => {
                    let spent = self.txn.budget.heartbeats_consumed;
                    *self = snapshot;
                    self.txn.budget.heartbeats_consumed = spent;
                    return Err(problem);
                }
            }
        }
        let spent = self.txn.budget.heartbeats_consumed;
        *self = snapshot;
        self.txn.budget.heartbeats_consumed = spent;
        Err(error(TacticError::NoConstructor))
    }
}
