//! Bounded proof search using ordinary application and checked goal closure.
//!
//! Choice points include the entire remaining obligation stack. A later premise
//! can therefore backtrack into the witness chosen for an earlier dependent
//! premise. Snapshots restore semantic state, never consumed work. Search uses
//! heap worklists and iterative deepening, not source-controlled Rust recursion.
use super::*;

const MAX_APPLICATION_DEPTH: usize = 6;

struct Choice {
    context: Box<Context>,
    pending: Vec<(Work<'static>, usize)>,
    goal: ProofGoal,
    locals: Vec<LocalDecl>,
    next: usize,
    depth: usize,
}

fn restore(context: &mut Context, snapshot: &Context) {
    let spent = context.txn.budget.heartbeats_consumed;
    *context = snapshot.clone();
    context.txn.budget.heartbeats_consumed = spent;
}

impl Context {
    /// Native `solve_by_elim` searches local declarations, newest first. Exact
    /// evidence and reflexivity/True leaves precede applications, and shallower
    /// proofs precede deeper ones. Defaults construct ordinary proof terms;
    /// they never register declarations or grant kernel acceptance.
    pub(super) fn solve_by_elim_proof_goal(
        &mut self,
        goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        let snapshot = Box::new(self.clone());
        for limit in 0..=MAX_APPLICATION_DEPTH {
            restore(self, &snapshot);
            match self.search_local_proof(goal.clone(), limit) {
                Ok(()) => return Ok(()),
                Err(problem) if backtrack::recoverable(&problem) => {}
                Err(problem) => {
                    restore(self, &snapshot);
                    return Err(problem);
                }
            }
        }
        restore(self, &snapshot);
        Err(error(TacticError::NoMatchingAssumption))
    }

    fn search_local_proof(
        &mut self,
        goal: ProofGoal,
        limit: usize,
    ) -> Result<(), NatDefinitionElabError> {
        let mut pending = vec![(Work::Goal(goal), 0)];
        let mut choices: Vec<Choice> = Vec::new();
        let mut retry: Option<Choice> = None;
        loop {
            self.tick()?;
            if let Some(mut choice) = retry.take() {
                let count = choice.locals.len();
                // The default leaf is a genuine choice point, including when
                // there are no locals. Its assignments must be rolled back if
                // a later dependent premise needs a different witness.
                let attempts = if choice.depth < limit { count * 2 + 1 } else { count + 1 };
                let mut selected = None;
                while choice.next < attempts {
                    restore(self, &choice.context);
                    self.tick()?;
                    let candidate = choice.next;
                    choice.next += 1;
                    let result = if candidate == count {
                        self.search_default_candidate(&choice.goal)
                    } else {
                        let application = candidate > count;
                        let index = if application { candidate - count - 1 } else { candidate };
                        let local = choice.locals[index].clone();
                        self.search_local_candidate(&choice.goal, local, application)
                    };
                    match result {
                        Ok(work) => {
                            selected = Some(work);
                            break;
                        }
                        Err(problem) if backtrack::recoverable(&problem) => {}
                        Err(problem) => return Err(problem),
                    }
                }
                if let Some(work) = selected {
                    pending = choice.pending.clone();
                    pending.extend(work.into_iter().map(|work| (work, choice.depth + 1)));
                    choices.push(choice);
                    continue;
                }
                retry = choices.pop();
                if retry.is_none() {
                    return Err(error(TacticError::NoMatchingAssumption));
                }
                continue;
            }
            let Some((work, depth)) = pending.pop() else {
                return Ok(());
            };
            match work {
                Work::Goal(mut goal) => {
                    if self.txn.mvars.is_assigned(&goal.id) {
                        continue;
                    }
                    self.txn.lctx = goal.lctx.clone();
                    goal.target = self.instantiate(&goal.target)?;
                    let mut locals = Vec::new();
                    for local in goal.lctx.decls().iter().rev() {
                        self.tick()?;
                        // Recursive equation hypotheses have their own guarded
                        // lowering path; search must not expose them as axioms.
                        if !self.is_matrix_hypothesis(local) {
                            locals.push(local.clone());
                        }
                    }
                    retry = Some(Choice {
                        context: Box::new(self.clone()),
                        pending: pending.clone(),
                        goal,
                        locals,
                        next: 0,
                        depth,
                    });
                }
                Work::Close(goal, value) => {
                    match self.close_proof_goal(goal, value) {
                        Ok(()) => {}
                        Err(problem) if backtrack::recoverable(&problem) => {
                            retry = choices.pop();
                            if retry.is_none() {
                                return Err(problem);
                            }
                        }
                        Err(problem) => return Err(problem),
                    }
                }
                // Only generated goals and continuations enter this private
                // stack, never source scripts or control frames.
                _ => return Err(error(TacticError::MalformedScript)),
            }
        }
    }

    fn search_default_candidate(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.tick()?;
        let target = self.whnf(&goal.target)?;
        let value = if let Some((level, alpha, left, beta, right)) =
            equality::heterogeneous_target(&target)
        {
            if !self.proof_types_match(&alpha, &beta)?
                || !self.proof_types_match(&left, &right)?
            {
                return Err(error(TacticError::NoMatchingAssumption));
            }
            [alpha, left].into_iter().fold(
                Expr::const_(Name::from_components(["HEq", "refl"]), vec![level]),
                Expr::app,
            )
        } else if let Some((level, alpha, left, right)) = equality_target(&target) {
            if !self.proof_types_match(&left, &right)? {
                return Err(error(TacticError::NoMatchingAssumption));
            }
            equality::reflexivity(level, alpha, left)
        } else if matches!(target.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(["True"]) && levels.is_empty())
        {
            Expr::const_(Name::from_components(["True", "intro"]), Vec::new())
        } else {
            return Err(error(TacticError::NoMatchingAssumption));
        };
        // Just like an explicit rfl/constructor, this is a candidate, not a
        // verdict. Closing and final command admission retain their usual checks.
        Ok(vec![Work::Close(goal.clone(), value)])
    }

    fn search_local_candidate(
        &mut self,
        goal: &ProofGoal,
        local: LocalDecl,
        application: bool,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let value = Expr::fvar(local.id);
        if !application {
            if !self.proof_types_match(&local.type_, &goal.target)? {
                return Err(error(TacticError::NoMatchingAssumption));
            }
            return Ok(vec![Work::Close(goal.clone(), value)]);
        }
        let mut proof = ProofState {
            saved: goal.lctx.clone(),
            target: goal.target.clone(),
            root: Expr::mvar(goal.id.clone()),
            instructions: Vec::new(),
            cursor: 0,
            work: Vec::new(),
            controls: Vec::new(),
        };
        let instance_start = self.instance_goals.len();
        self.apply_proof_term(
            &mut proof,
            goal.clone(),
            Typed { value, type_: local.type_ },
            instance_start,
        )?;
        Ok(proof.work)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        Context::new(&Environment::new(), Budget::for_stack_bytes(2 * 1024 * 1024))
    }

    fn local(context: &mut Context, name: &str, type_: Expr) -> Expr {
        let name = Name::from_components([name]);
        let id = FVarId(name.clone());
        context.txn.lctx.add_param(id.clone(), name, type_, BinderInfo::Default);
        Expr::fvar(id)
    }

    fn proposition(context: &mut Context, name: &str) -> Expr {
        local(context, name, Expr::sort(Level::zero()))
    }

    fn arrow(domain: Expr, range: Expr) -> Expr {
        Expr::forall_e(Name::anonymous(), domain, range, BinderInfo::Default)
    }

    #[test]
    fn search_constructs_a_chain_of_local_applications() {
        let mut context = context();
        let p = proposition(&mut context, "p");
        let q = proposition(&mut context, "q");
        let r = proposition(&mut context, "r");
        let hp = local(&mut context, "hp", p.clone());
        let f = local(&mut context, "f", arrow(p, q.clone()));
        let g = local(&mut context, "g", arrow(q, r.clone()));
        let (root, goal) = context.proof_goal(r).unwrap();
        context.solve_by_elim_proof_goal(goal).unwrap();
        assert_eq!(context.instantiate(&root).unwrap(), Expr::app(g, Expr::app(f, hp)));
    }

    #[test]
    fn search_backtracks_out_of_an_inapplicable_local_lemma() {
        let mut context = context();
        let p = proposition(&mut context, "p");
        let q = proposition(&mut context, "q");
        let r = proposition(&mut context, "r");
        let hp = local(&mut context, "hp", p.clone());
        let good = local(&mut context, "good", arrow(p, r.clone()));
        local(&mut context, "dead_end", arrow(q, r.clone()));
        let (root, goal) = context.proof_goal(r).unwrap();
        context.solve_by_elim_proof_goal(goal).unwrap();
        assert_eq!(context.instantiate(&root).unwrap(), Expr::app(good, hp));
    }

    #[test]
    fn cycles_fail_without_assigning_the_goal_or_refunding_work() {
        let mut context = context();
        let p = proposition(&mut context, "p");
        local(&mut context, "cycle", arrow(p.clone(), p.clone()));
        let (_, goal) = context.proof_goal(p).unwrap();
        let id = goal.id.clone();
        let locals = context.txn.lctx.len();
        let before = context.txn.budget.heartbeats_consumed;
        assert!(context.solve_by_elim_proof_goal(goal).is_err());
        assert!(!context.txn.mvars.is_assigned(&id));
        assert_eq!(context.txn.lctx.len(), locals);
        assert!(context.txn.budget.heartbeats_consumed > before);
    }

    #[test]
    fn search_propagates_resource_exhaustion_and_restores_semantic_state() {
        let mut context = context();
        let p = proposition(&mut context, "p");
        local(&mut context, "hp", p.clone());
        let (_, goal) = context.proof_goal(p).unwrap();
        let id = goal.id.clone();
        context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed + 1;
        assert!(matches!(
            context.solve_by_elim_proof_goal(goal),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit))
        ));
        assert!(!context.txn.mvars.is_assigned(&id));
    }

    #[test]
    fn default_leaf_constructs_true_without_any_local_hypothesis() {
        let mut context = context();
        let target = Expr::const_(Name::from_components(["True"]), Vec::new());
        let (root, goal) = context.proof_goal(target).unwrap();
        context.solve_by_elim_proof_goal(goal).unwrap();
        assert_eq!(
            context.instantiate(&root).unwrap(),
            Expr::const_(Name::from_components(["True", "intro"]), Vec::new())
        );
    }

    #[test]
    fn default_reflexivity_closes_a_local_lemma_premise() {
        let mut context = context();
        let p = proposition(&mut context, "p");
        let alpha = Expr::sort(Level::zero());
        let level = Level::succ(Level::zero());
        let equality = equality::equation(level.clone(), alpha.clone(), p.clone(), p.clone());
        let q = proposition(&mut context, "q");
        let rule = local(&mut context, "rule", arrow(equality, q.clone()));
        let (root, goal) = context.proof_goal(q).unwrap();
        context.solve_by_elim_proof_goal(goal).unwrap();
        assert_eq!(
            context.instantiate(&root).unwrap(),
            Expr::app(rule, equality::reflexivity(level, alpha, p))
        );
    }

    #[test]
    fn default_heterogeneous_reflexivity_constructs_heq_refl() {
        let mut context = context();
        let p = proposition(&mut context, "p");
        let alpha = Expr::sort(Level::zero());
        let level = Level::succ(Level::zero());
        let target = [alpha.clone(), p.clone(), alpha.clone(), p.clone()]
            .into_iter()
            .fold(Expr::const_(Name::from_components(["HEq"]), vec![level.clone()]), Expr::app);
        let (root, goal) = context.proof_goal(target).unwrap();
        context.solve_by_elim_proof_goal(goal).unwrap();
        let expected = [alpha, p].into_iter().fold(
            Expr::const_(Name::from_components(["HEq", "refl"]), vec![level]),
            Expr::app,
        );
        assert_eq!(context.instantiate(&root).unwrap(), expected);
    }

    #[test]
    fn defaults_do_not_prove_an_arbitrary_proposition() {
        let mut context = context();
        let p = proposition(&mut context, "p");
        let (_, goal) = context.proof_goal(p).unwrap();
        let id = goal.id.clone();
        assert!(context.solve_by_elim_proof_goal(goal).is_err());
        assert!(!context.txn.mvars.is_assigned(&id));
    }
}
