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
        self.construct_proof_goal_ordered(proof, goal, selected, ApplyGoalOrder::NonDependentFirst)
    }

    pub(super) fn construct_proof_goal_ordered(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        selected: Option<usize>,
        order: ApplyGoalOrder,
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
            match self.apply_proof_term_ordered(proof, goal.clone(), term, instance_start, order) {
                Ok(()) => return Ok(()),
                Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                    TacticError::ApplyMismatch,
                ))) => {}
                // The pin's `MVarId.constructor` catches every ordinary failure of
                // `apply`, an unsynthesizable instance argument included, and tries
                // the next constructor. `left`/`right` (`nthConstructor`) apply
                // theirs directly and let the failure stand.
                Err(problem) if selected.is_none() && backtrack::recoverable(&problem) => {}
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

/// The pin's `repeat'` stops after this many tactic calls (`repeat'Core`'s `maxIters`,
/// vendored src/Lean/Meta/Tactic/Repeat.lean).
const AND_INTROS_MAX_CALLS: usize = 100_000;

/// A step of [`Context::and_intros_expansion`]'s depth-first walk.
enum AndIntros {
    Expand(ProofGoal),
    Close(ProofGoal, Expr),
}

impl Context {
    /// `and_intros`, the pin's `repeat' refine And.intro ?_ ?_` (vendored
    /// src/Init/Tactics.lean:1355-1357): over every visible goal in order, each goal whose
    /// target is a conjunction at the ambient transparency is split into its two conjuncts,
    /// tagged `refine_1` and `refine_2` under it (`tagUntaggedGoals`), and each of those is
    /// split again, depth first (`repeat'Core`). A goal that is not a conjunction stays.
    pub(super) fn and_intros_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "and_intros", "and_intros keyword")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "tacticAnd_intros"])?;
        let mut calls = 0;
        let main = self.and_intros_expansion(goal, &mut calls)?;
        // The other visible goals, from the main one down to the first barrier, each expanded
        // where it stands.
        let boundary = proof
            .work
            .iter()
            .rposition(|work| {
                matches!(
                    work,
                    Work::EndScript(..)
                        | Work::EndControl(_)
                        | Work::EndAttempt(_)
                        | Work::EndOptions(_)
                )
            })
            .map_or(0, |position| position + 1);
        let mut index = proof.work.len();
        while index > boundary {
            self.tick()?;
            index -= 1;
            let Work::Goal(other) = &proof.work[index] else {
                continue;
            };
            if self.txn.mvars.is_assigned(&other.id) {
                continue;
            }
            let other = other.clone();
            let expansion = self.and_intros_expansion(other, &mut calls)?;
            proof
                .work
                .splice(index..=index, expansion.into_iter().map(Work::from));
        }
        proof.work.extend(main.into_iter().map(Work::from));
        Ok(())
    }

    /// `goal`'s depth-first expansion, in worklist order (the last entry runs first).
    fn and_intros_expansion(
        &mut self,
        goal: ProofGoal,
        calls: &mut usize,
    ) -> Result<Vec<AndIntrosWork>, NatDefinitionElabError> {
        let mut order = Vec::new();
        let mut pending = vec![AndIntros::Expand(goal)];
        while let Some(step) = pending.pop() {
            self.tick()?;
            match step {
                AndIntros::Close(goal, value) => {
                    order.push(AndIntrosWork::Close(goal, value));
                }
                AndIntros::Expand(goal) => {
                    if *calls >= AND_INTROS_MAX_CALLS {
                        order.push(AndIntrosWork::Goal(goal));
                        continue;
                    }
                    *calls += 1;
                    match self.and_intro_split(&goal)? {
                        Some((value, left, right)) => {
                            pending.push(AndIntros::Close(goal, value));
                            pending.push(AndIntros::Expand(right));
                            pending.push(AndIntros::Expand(left));
                        }
                        None => order.push(AndIntrosWork::Goal(goal)),
                    }
                }
            }
        }
        order.reverse();
        Ok(order)
    }

    /// `refine And.intro ?_ ?_` on `goal`: its two new goals and the term closing it, or `None`
    /// where its target is not a conjunction.
    fn and_intro_split(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Option<(Expr, ProofGoal, ProofGoal)>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let target = self.instantiate(&goal.target)?;
        let target = self.whnf(&target)?;
        let ExprNode::App { f, a: right } = target.node() else {
            return Ok(None);
        };
        let ExprNode::App { f: head, a: left } = f.node() else {
            return Ok(None);
        };
        if !matches!(head.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(["And"]) && levels.is_empty())
        {
            return Ok(None);
        }
        let (left, right) = (left.clone(), right.clone());
        let (left_proof, left_goal) = self.proof_goal(left.clone())?;
        let (right_proof, right_goal) = self.proof_goal(right.clone())?;
        let tag = self
            .goal_tags
            .get(&goal.id)
            .cloned()
            .unwrap_or_else(Name::anonymous);
        self.goal_tags
            .insert(left_goal.id.clone(), Name::str(tag.clone(), "refine_1"));
        self.goal_tags
            .insert(right_goal.id.clone(), Name::str(tag, "refine_2"));
        let value = [left, right, left_proof, right_proof].into_iter().fold(
            Expr::const_(Name::from_components(["And", "intro"]), Vec::new()),
            Expr::app,
        );
        Ok(Some((value, left_goal, right_goal)))
    }
}

/// A worklist entry [`Context::and_intros_expansion`] produces.
enum AndIntrosWork {
    Goal(ProofGoal),
    Close(ProofGoal, Expr),
}

impl<'a> From<AndIntrosWork> for Work<'a> {
    fn from(work: AndIntrosWork) -> Self {
        match work {
            AndIntrosWork::Goal(goal) => Work::Goal(goal),
            AndIntrosWork::Close(goal, value) => Work::Close(goal, value),
        }
    }
}
