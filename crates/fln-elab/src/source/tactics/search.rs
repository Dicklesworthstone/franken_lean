//! Bounded local-lemma search using ordinary application and checked goal closure.
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
    /// evidence precedes applications, and shallower proofs precede deeper ones.
    /// This bounded subset does not silently consult global lemmas or axioms.
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
                let attempts = if choice.depth < limit { count * 2 } else { count };
                let mut selected = None;
                while choice.next < attempts {
                    restore(self, &choice.context);
                    self.tick()?;
                    let application = choice.next >= count;
                    let local = choice.locals[choice.next % count].clone();
                    choice.next += 1;
                    match self.search_local_candidate(&choice.goal, local, application) {
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
                // Only application-generated goals and continuations enter
                // this private stack, never source scripts or control frames.
                _ => return Err(error(TacticError::MalformedScript)),
            }
        }
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
}
