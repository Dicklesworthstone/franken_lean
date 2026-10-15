//! Default search dischargers reuse the ordinary typed proof operations.
//! Constructor premises keep telescope order; all their choices share the
//! outer pending stack. Introductions are closed only once evidence exists.
use super::*;

impl Context {
    pub(super) fn search_construction_candidate(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let snapshot = self.clone();
        let mut proof = ProofState {
            extent: None,
            saved: goal.lctx.clone(),
            target: goal.target.clone(),
            root: Expr::mvar(goal.id.clone()),
            instructions: Vec::new(),
            cursor: 0,
            work: Vec::new(),
            controls: Vec::new(),
        };
        match self.construct_proof_goal_ordered(
            &mut proof,
            goal.clone(),
            None,
            ApplyGoalOrder::Telescope,
        ) {
            Ok(()) => return Ok(proof.work),
            Err(problem) if backtrack::recoverable(&problem) => {}
            Err(problem) => return Err(problem),
        }
        restore(self, &snapshot);
        // Preserve a visible let rather than erasing its value and local
        // scope before introducing. Type aliases may expose a forall by WHNF.
        let mut target = self.instantiate(&goal.target)?;
        while let ExprNode::MData { expr, .. } = target.node() {
            self.tick()?;
            target = expr.clone();
        }
        if !matches!(target.node(), ExprNode::LetE { .. }) {
            target = self.whnf(&target)?;
        }
        if !matches!(
            target.node(),
            ExprNode::ForallE { .. } | ExprNode::LetE { .. }
        ) {
            return Err(error(TacticError::NoMatchingAssumption));
        }
        let mut child = goal.clone();
        let name = self.fresh_name()?;
        self.introduce_proof_binder(&mut child, name)?;
        child.lctx = self.txn.lctx.clone();
        Ok(vec![Work::Goal(child)])
    }

    pub(super) fn search_exfalso_frontier(
        &mut self,
        frontier: &[Work<'static>],
        selection: &Selection<'_>,
    ) -> Result<(), NatDefinitionElabError> {
        let mut selected = None;
        for (index, work) in frontier.iter().enumerate() {
            self.tick()?;
            if let Work::Goal(goal) = work
                && !self.txn.mvars.is_assigned(&goal.id)
            {
                if selected.is_some() {
                    return Err(error(TacticError::NoMatchingAssumption));
                }
                selected = Some((index, goal));
            }
        }
        let Some((index, goal)) = selected else {
            return Err(error(TacticError::NoMatchingAssumption));
        };
        let work = self.rule_exfalso(goal)?;
        let mut pending = Vec::with_capacity(frontier.len() + 1);
        for (at, action) in frontier.iter().enumerate() {
            self.tick()?;
            if at == index {
                pending.extend(work.iter().cloned());
            } else {
                pending.push(action.clone());
            }
        }
        self.search_frontier_limits(&pending, selection)
    }
}
