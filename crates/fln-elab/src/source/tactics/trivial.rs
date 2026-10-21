//! `trivial`. Its syntax (`syntax "trivial" : tactic`, vendored src/Init/Tactics.lean) has no
//! elaborator: six `macro_rules` expand it, and `evalTactic` tries them most recent first,
//! undoing each one that fails (`expandEval`, vendored src/Lean/Elab/Tactic/Basic.lean):
//! `apply And.intro <;> trivial`, `apply True.intro`, `decide`, `contradiction`, `rfl`,
//! `assumption`. When every expansion fails, the last failure is the one reported (`throwExs`).
use super::*;

#[derive(Clone, Copy)]
enum Expansion {
    Conjunction,
    True,
    Decide,
    Contradiction,
    Rfl,
    Assumption,
}

const EXPANSIONS: [Expansion; 6] = [
    Expansion::Conjunction,
    Expansion::True,
    Expansion::Decide,
    Expansion::Contradiction,
    Expansion::Rfl,
    Expansion::Assumption,
];

/// The pin's default `maxRecDepth`, which bounds the macro's own recursion through
/// `And.intro`; a deeper conjunction is a resource stop here, never a verdict.
const MAX_CONJUNCTION_DEPTH: usize = 512;

fn conjunction(target: &Expr) -> Option<(Expr, Expr)> {
    let ExprNode::App { f, a: right } = target.node() else {
        return None;
    };
    let ExprNode::App { f: head, a: left } = f.node() else {
        return None;
    };
    matches!(head.node(), ExprNode::Const { name, .. } if *name == Name::from_components(["And"]))
        .then(|| (left.clone(), right.clone()))
}

impl Context {
    pub(super) fn trivial_proof_goal(
        &mut self,
        goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "tacticTrivial"])?;
        self.trivial_at_depth(goal, 0)
    }

    fn trivial_at_depth(
        &mut self,
        goal: ProofGoal,
        depth: usize,
    ) -> Result<(), NatDefinitionElabError> {
        if depth > MAX_CONJUNCTION_DEPTH {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let mut last = None;
        for expansion in EXPANSIONS {
            self.tick()?;
            let snapshot = Box::new(self.clone());
            match self.trivial_expansion(goal.clone(), expansion, depth) {
                Ok(()) => return Ok(()),
                // An ordinary failure moves on to the next expansion, as the pin's does; a
                // refusal this engine cannot judge, or a resource stop, is not the pin's
                // failure and is never passed over.
                Err(problem) if backtrack::recoverable(&problem) => {
                    let spent = self.txn.budget.heartbeats_consumed;
                    *self = *snapshot;
                    self.txn.budget.heartbeats_consumed = spent;
                    last = Some(problem);
                }
                Err(problem) => return Err(problem),
            }
        }
        Err(last.expect("every expansion was tried and failed"))
    }

    fn trivial_expansion(
        &mut self,
        mut goal: ProofGoal,
        expansion: Expansion,
        depth: usize,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        goal.target = self.instantiate(&goal.target)?;
        match expansion {
            // `apply And.intro <;> trivial`: both conjuncts are closed before the conjunction,
            // whose closure abstracts the goal's own binders.
            Expansion::Conjunction => {
                let target = self.whnf(&goal.target)?;
                let (left, right) =
                    conjunction(&target).ok_or_else(|| error(TacticError::ApplyMismatch))?;
                let (left_proof, left_goal) = self.proof_goal(left.clone())?;
                let (right_proof, right_goal) = self.proof_goal(right.clone())?;
                self.trivial_at_depth(left_goal, depth + 1)?;
                self.txn.lctx = goal.lctx.clone();
                self.trivial_at_depth(right_goal, depth + 1)?;
                let value = [left, right, left_proof, right_proof].into_iter().fold(
                    Expr::const_(Name::from_components(["And", "intro"]), Vec::new()),
                    Expr::app,
                );
                self.close_proof_goal(goal, value)
            }
            Expansion::True => {
                let target = self.whnf(&goal.target)?;
                if !matches!(target.node(), ExprNode::Const { name, .. } if *name == Name::from_components(["True"]))
                {
                    return Err(error(TacticError::ApplyMismatch));
                }
                let value = Expr::const_(Name::from_components(["True", "intro"]), Vec::new());
                self.close_proof_goal(goal, value)
            }
            Expansion::Decide => self.decide_proof_goal(goal),
            Expansion::Contradiction => self.contradict_proof_goal(goal),
            Expansion::Rfl => self.rfl_proof_goal(goal),
            Expansion::Assumption => {
                let value = self
                    .matching_assumption(&goal)?
                    .ok_or_else(|| error(TacticError::NoMatchingAssumption))?;
                self.close_proof_goal(goal, value)
            }
        }
    }
}
