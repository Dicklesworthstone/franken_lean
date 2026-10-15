//! Bounded proof search using ordinary application and checked goal closure.
//!
//! Choice points include the entire remaining obligation stack. A later premise
//! can therefore backtrack into the witness chosen for an earlier dependent
//! premise. Snapshots restore semantic state, never consumed work. Search uses
//! heap worklists and iterative deepening, not source-controlled Rust recursion.
use super::*;

mod construction;
mod rules;
mod rules_config;
mod selection;
pub(super) use selection::selection;
use selection::{Candidate, Selection};

const MAX_APPLICATION_DEPTH: usize = 6;

struct Choice<'a> {
    context: Box<Context>,
    pending: Vec<(Work<'static>, usize)>,
    goal: ProofGoal,
    candidates: Vec<Candidate<'a>>,
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
    /// evidence, reflexivity/True leaves, and reversed equality facts precede
    /// applications. Shallower proofs precede deeper ones. Defaults construct
    /// ordinary proof terms, never declarations or kernel acceptance.
    #[cfg(test)]
    fn solve_by_elim_proof_goal(&mut self, goal: ProofGoal) -> Result<(), NatDefinitionElabError> {
        self.solve_by_elim_selected_proof_goal(goal, &Selection::default())
    }

    /// Share choices across the visible frontier, including deferred close
    /// actions. A later sibling may constrain a witness chosen for an earlier
    /// sibling, so mapping independent searches over the goals is insufficient.
    pub(super) fn solve_by_elim_selected_proof_state(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        selection: &Selection<'_>,
    ) -> Result<(), NatDefinitionElabError> {
        if !selection.all_goals {
            return self.solve_by_elim_selected_proof_goal(goal, selection);
        }
        let mut boundary = proof.work.len();
        let mut frontier = Vec::new();
        for work in proof.work.iter().rev() {
            self.tick()?;
            match work {
                Work::Goal(goal) => frontier.push(Work::Goal(goal.clone())),
                Work::Close(goal, value) => {
                    frontier.push(Work::Close(goal.clone(), value.clone()));
                }
                // Never steal another branch's script, term, rewrite, or the
                // goals suspended outside a focus/attempt/option scope.
                _ => break,
            }
            boundary -= 1;
        }
        frontier.reverse();
        frontier.push(Work::Goal(goal));
        let goals = frontier
            .iter()
            .filter(
                |work| matches!(work, Work::Goal(goal) if !self.txn.mvars.is_assigned(&goal.id)),
            )
            .count();
        if goals > 1 && !selection.remove.is_empty() {
            return Err(error(TacticError::InvalidSearchArguments(
                "removing local hypotheses is not supported across multiple goals",
            )));
        }
        // Both context and worklist commit only after every goal and close
        // continuation has succeeded. Failure leaves sibling work untouched.
        self.solve_selected_frontier(&frontier, selection)?;
        proof.work.truncate(boundary);
        Ok(())
    }

    fn solve_by_elim_selected_proof_goal(
        &mut self,
        goal: ProofGoal,
        selection: &Selection<'_>,
    ) -> Result<(), NatDefinitionElabError> {
        self.solve_selected_frontier(&[Work::Goal(goal)], selection)
    }

    fn solve_selected_frontier(
        &mut self,
        frontier: &[Work<'static>],
        selection: &Selection<'_>,
    ) -> Result<(), NatDefinitionElabError> {
        let snapshot = Box::new(self.clone());
        for work in frontier.iter().rev() {
            if let Work::Goal(goal) = work {
                let validated = self.selected_search_candidates(goal, selection);
                restore(self, &snapshot);
                validated?;
            }
        }
        let first = self.search_frontier_limits(frontier, selection);
        if first.is_ok() {
            return first;
        }
        restore(self, &snapshot);
        let problem = first.expect_err("unsuccessful search");
        if !backtrack::recoverable(&problem) {
            return Err(problem);
        }
        // The pin retries exfalso only after the complete initial search fails,
        // and only for one visible goal. Never prove an early sibling and then
        // silently change just the later sibling into False.
        let retry = self.search_exfalso_frontier(frontier, selection);
        if retry.is_err() {
            restore(self, &snapshot);
        }
        retry
    }

    fn search_frontier_limits(
        &mut self,
        frontier: &[Work<'static>],
        selection: &Selection<'_>,
    ) -> Result<(), NatDefinitionElabError> {
        let snapshot = Box::new(self.clone());
        for limit in 0..=MAX_APPLICATION_DEPTH {
            restore(self, &snapshot);
            match self.search_selected_proof(frontier, selection, limit) {
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

    fn search_selected_proof(
        &mut self,
        frontier: &[Work<'static>],
        selection: &Selection<'_>,
        limit: usize,
    ) -> Result<(), NatDefinitionElabError> {
        let mut pending: Vec<_> = frontier.iter().cloned().map(|work| (work, 0)).collect();
        let mut choices: Vec<Choice<'_>> = Vec::new();
        let mut retry: Option<Choice<'_>> = None;
        let defaults = usize::from(selection.defaults);
        loop {
            self.tick()?;
            if let Some(mut choice) = retry.take() {
                let count = choice.candidates.len();
                // Defaults and both orientations are genuine choice points:
                // a later dependent premise may require another witness.
                let applications = choice.depth < limit;
                let regular_attempts = if applications {
                    count * 4 + defaults
                } else {
                    count * 2 + defaults
                };
                // The constructor/intro discharger is one final choice, not a
                // new unbounded recursive search or a second constructor loop.
                let attempts = regular_attempts + usize::from(applications);
                let mut selected = None;
                while choice.next < attempts {
                    restore(self, &choice.context);
                    self.tick()?;
                    let candidate = choice.next;
                    choice.next += 1;
                    let result = if candidate == regular_attempts {
                        self.search_construction_candidate(&choice.goal)
                    } else if candidate < count {
                        let candidate = choice.candidates[candidate].clone();
                        self.search_candidate(&choice.goal, candidate, false)
                    } else if defaults != 0 && candidate == count {
                        self.search_default_candidate(&choice.goal)
                    } else {
                        let offset = candidate - count - defaults;
                        let (index, application, reverse) = if offset < count {
                            (offset, false, true)
                        } else if offset < count * 2 {
                            (offset - count, true, false)
                        } else {
                            (offset - count * 2, true, true)
                        };
                        let candidate = choice.candidates[index].clone();
                        if reverse {
                            self.search_symmetric_candidate(&choice.goal, candidate, application)
                        } else {
                            self.search_candidate(&choice.goal, candidate, application)
                        }
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
                    let candidates = self.selected_search_candidates(&goal, selection)?;
                    retry = Some(Choice {
                        context: Box::new(self.clone()),
                        pending: pending.clone(),
                        goal,
                        candidates,
                        next: 0,
                        depth,
                    });
                }
                Work::Close(goal, value) => match self.close_proof_goal(goal, value) {
                    Ok(()) => {}
                    Err(problem) if backtrack::recoverable(&problem) => {
                        retry = choices.pop();
                        if retry.is_none() {
                            return Err(problem);
                        }
                    }
                    Err(problem) => return Err(problem),
                },
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
        // SolveByElim.lean's default ApplyRulesConfig uses Default
        // transparency. Keep this separate from rw/simp's reducible closure:
        // search may unfold an ordinary definition, but not an irreducible one.
        // The shared conversion query also preserves native arithmetic and
        // propagates resource stops through the existing choice checkpoints.
        let value = if let Some((level, alpha, left, beta, right)) =
            equality::heterogeneous_target(&target)
        {
            if !self.coercion_eq(&alpha, &beta)? || !self.coercion_eq(&left, &right)? {
                return Err(error(TacticError::NoMatchingAssumption));
            }
            [alpha, left].into_iter().fold(
                Expr::const_(Name::from_components(["HEq", "refl"]), vec![level]),
                Expr::app,
            )
        } else if let Some((level, alpha, left, right)) = equality_target(&target) {
            if !self.coercion_eq(&left, &right)? {
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

    fn search_symmetric_candidate(
        &mut self,
        goal: &ProofGoal,
        candidate: Candidate<'_>,
        application: bool,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.tick()?;
        let target = self.whnf(&goal.target)?;
        let Some((level, alpha, left, right)) = equality_target(&target) else {
            return Err(error(TacticError::NoMatchingAssumption));
        };
        let reversed =
            equality::equation(level.clone(), alpha.clone(), right.clone(), left.clone());
        let (witness, subgoal) = self.proof_goal(reversed)?;
        let candidate = self.search_candidate(&subgoal, candidate, application)?;
        let value = self.symmetric_equality(&level, &alpha, &right, &left, witness)?;
        // The local rule must actually prove the reversed equation before the
        // Eq.rec bridge closes the parent. This is not a recursive "try symm"
        // rule, so it cannot alternate orientations forever or evade the depth
        // bound. Its premises still participate in whole-stack backtracking.
        let mut work = vec![Work::Close(goal.clone(), value)];
        work.extend(candidate);
        Ok(work)
    }

    fn search_candidate(
        &mut self,
        goal: &ProofGoal,
        candidate: Candidate<'_>,
        application: bool,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        // A supplied lemma is elaborated afresh at each choice. In particular,
        // neither its universe metavariables nor its instance obligations may
        // be reused by a second application or a different goal context.
        let instance_start = self.instance_goals.len();
        let term = match candidate {
            Candidate::Local(local) => Typed {
                value: Expr::fvar(local.id),
                type_: local.type_,
            },
            Candidate::Explicit(syntax) => self.term(syntax, None)?,
        };
        if !application {
            if !self.proof_types_match(&term.type_, &goal.target)? {
                return Err(error(TacticError::NoMatchingAssumption));
            }
            self.resolve_instances(false)?;
            if self.instance_goals[instance_start..]
                .iter()
                .any(|id| !self.txn.mvars.is_assigned(id))
            {
                return Err(error(TacticError::ApplyMismatch));
            }
            return Ok(vec![Work::Close(goal.clone(), term.value)]);
        }
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
        self.apply_proof_term(&mut proof, goal.clone(), term, instance_start)?;
        Ok(proof.work)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }

    fn source_environment() -> Environment {
        use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
        use fln_env::pmap::CollisionBudget;
        use fln_kernel::capability::{Published, admit};
        use fln_kernel::council::{Council, CouncilOutcome, convene};

        let mut environment = Environment::new();
        for declaration in crate::seed::source_seed_declarations() {
            let Outcome::Complete(admitted) = admit(
                &environment,
                declaration,
                Budget::for_stack_bytes(2 * 1024 * 1024),
            ) else {
                panic!("seed nonanswer");
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("seed rejected");
            };
            environment = match checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) {
                Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                    result,
                ))) => result.environment,
                Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
                other => panic!("seed publication {other:?}"),
            };
        }
        environment
    }

    fn seeded_context() -> Context {
        Context::new(
            &source_environment(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }

    fn local(context: &mut Context, name: &str, type_: Expr) -> Expr {
        let name = Name::from_components([name]);
        let id = FVarId(name.clone());
        context
            .txn
            .lctx
            .add_param(id.clone(), name, type_, BinderInfo::Default);
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
        assert_eq!(
            context.instantiate(&root).unwrap(),
            Expr::app(g, Expr::app(f, hp))
        );
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
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert!(!context.txn.mvars.is_assigned(&id));
    }

    #[test]
    fn every_joint_search_budget_stop_restores_all_assignments_and_pending_work() {
        let mut original = context();
        let p = proposition(&mut original, "p");
        let q = proposition(&mut original, "q");
        local(&mut original, "hp", p.clone());
        local(&mut original, "hq", q.clone());
        let (root, first) = original.proof_goal(p.clone()).unwrap();
        let (_, second) = original.proof_goal(q).unwrap();
        let proof = ProofState {
            extent: None,
            saved: original.txn.lctx.clone(),
            target: p,
            root,
            instructions: Vec::new(),
            cursor: 0,
            work: vec![Work::Goal(second.clone())],
            controls: Vec::new(),
        };
        let selection = Selection {
            all_goals: true,
            ..Selection::default()
        };
        let before = original.txn.budget.heartbeats_consumed;
        let mut completed = original.clone();
        let mut completed_proof = proof.clone();
        completed
            .solve_by_elim_selected_proof_state(&mut completed_proof, first.clone(), &selection)
            .unwrap();
        assert!(completed.txn.mvars.is_assigned(&first.id));
        assert!(completed.txn.mvars.is_assigned(&second.id));
        assert!(completed_proof.work.is_empty());
        let work = completed.txn.budget.heartbeats_consumed - before;
        for allowance in 0..work {
            let mut limited = original.clone();
            limited.txn.budget.max_heartbeats = before + allowance;
            let mut pending = proof.clone();
            let outcome =
                limited.solve_by_elim_selected_proof_state(&mut pending, first.clone(), &selection);
            let problem = outcome.expect_err("a smaller budget must not complete joint search");
            assert!(
                matches!(
                    &problem,
                    NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit)
                ) || matches!(&problem, NatDefinitionElabError::Inference(SourceInferenceError::Unification(reason)) if matches!(reason.as_ref(), UnificationError::HeartbeatLimit)),
                "allowance {allowance}: {problem:?}"
            );
            assert!(!backtrack::recoverable(&problem), "allowance {allowance}");
            assert!(!limited.txn.mvars.is_assigned(&first.id));
            assert!(!limited.txn.mvars.is_assigned(&second.id));
            assert_eq!(limited.txn.mvars.len(), original.txn.mvars.len());
            assert_eq!(
                limited.txn.mvars.assignments(),
                original.txn.mvars.assignments()
            );
            assert_eq!(limited.txn.lctx.decls(), original.txn.lctx.decls());
            assert_eq!(limited.instance_goals, original.instance_goals);
            assert!(limited.txn.budget.heartbeats_consumed >= before + allowance);
            assert!(matches!(pending.work.as_slice(), [Work::Goal(goal)] if goal.id == second.id));
        }
    }

    #[test]
    fn every_structural_search_budget_stop_restores_binders_and_deferred_evidence() {
        let mut initial = seeded_context();
        let p = proposition(&mut initial, "P");
        let t = Expr::const_(Name::from_components(["True"]), Vec::new());
        let both = Expr::app(
            Expr::app(
                Expr::const_(Name::from_components(["And"]), Vec::new()),
                p.clone(),
            ),
            t,
        );
        let q = proposition(&mut initial, "Q");
        let mut negative = initial.clone();
        local(&mut negative, "hp", p.clone());
        local(
            &mut negative,
            "no",
            arrow(
                p.clone(),
                Expr::const_(Name::from_components(["False"]), Vec::new()),
            ),
        );
        for (mut original, target) in [(initial, arrow(p, both)), (negative, q)] {
            let (root, goal) = original.proof_goal(target).unwrap();
            let selection = Selection {
                defaults: false,
                ..Selection::default()
            };
            let before = original.txn.budget.heartbeats_consumed;
            let mut complete = original.clone();
            complete
                .solve_by_elim_selected_proof_goal(goal.clone(), &selection)
                .unwrap();
            let work = complete.txn.budget.heartbeats_consumed - before;
            let proof = complete.instantiate(&root).unwrap();
            assert!(!proof.has_expr_mvar());
            assert!(!proof.has_level_mvar());
            assert!(!proof.has_loose_bvars());
            for allowance in 0..work {
                let mut limited = original.clone();
                limited.txn.budget.max_heartbeats = before + allowance;
                let problem = limited
                    .solve_by_elim_selected_proof_goal(goal.clone(), &selection)
                    .expect_err("a partial search is not closed evidence");
                assert!(
                    !backtrack::recoverable(&problem),
                    "{allowance}: {problem:?}"
                );
                assert!(limited.txn.budget.heartbeats_consumed >= before + allowance);
                // Normalize only the caller-supplied cap and consumed work.
                // Every semantic component, including universes, queued
                // constraints, context and assignments, must be unchanged.
                limited.txn.budget = original.txn.budget.clone();
                assert_eq!(limited.txn, original.txn, "{allowance}");
                assert_eq!(limited.next, original.next);
                assert_eq!(limited.equations.len(), original.equations.len());
                assert!(
                    limited
                        .equations
                        .iter()
                        .zip(&original.equations)
                        .all(|(a, b)| a.sides == b.sides && a.policy == b.policy)
                );
                assert_eq!(limited.instance_goals, original.instance_goals);
                assert_eq!(limited.goal_tags, original.goal_tags);
                assert_eq!(limited.trace_local_names, original.trace_local_names);
            }
        }
    }

    #[test]
    fn default_leaf_constructs_true_without_any_local_hypothesis() {
        let mut context = seeded_context();
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
        let mut context = seeded_context();
        let p = proposition(&mut context, "p");
        let alpha = Expr::sort(Level::zero());
        let level = Level::one();
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
        let mut context = seeded_context();
        let p = proposition(&mut context, "p");
        let alpha = Expr::sort(Level::zero());
        let level = Level::one();
        let target = [alpha.clone(), p.clone(), alpha.clone(), p.clone()]
            .into_iter()
            .fold(
                Expr::const_(Name::from_components(["HEq"]), vec![level.clone()]),
                Expr::app,
            );
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

    #[test]
    fn source_defaults_and_symmetric_rules_build_kernel_accepted_theorems() {
        let environment = source_environment();
        for source in [
            "theorem automatic : True := by solve_by_elim",
            "theorem automatic (x : Nat) : x = x := by solve_by_elim",
            "theorem automatic : 2 + 3 = 5 := by solve_by_elim",
            "theorem automatic (x : Nat) : HEq x x := by solve_by_elim",
            "theorem automatic (P : Prop) (f : True -> P) : P := by solve_by_elim",
            "theorem automatic (x : Nat) (P : Prop) (f : x = x -> P) : P := by solve_by_elim",
            "theorem automatic (x y : Nat) (h : x = y) : y = x := by solve_by_elim",
            "theorem automatic (x y : Nat) (P : Prop) (h : P) (f : P -> x = y) : y = x := by solve_by_elim",
            "theorem automatic (x y : Nat) (P : Prop) (f : y = x -> P) (h : x = y) : P := by solve_by_elim",
            "theorem automatic {A : Type} (x y : A) (h : x = y) : y = x := by solve_by_elim",
            "theorem automatic (x y : Nat) (P Q : Prop) (good : y = x -> P) (bad : Q -> P) (h : x = y) : P := by solve_by_elim",
            "theorem automatic (x y : Nat) (P : Nat -> Prop) (Q : Prop) (hx : P x) (f : (n : Nat) -> n = n -> P n -> Q) : Q := by solve_by_elim",
        ] {
            let result = crate::check_definition_source(
                source.as_bytes(),
                &environment,
                Budget::for_stack_bytes(2 * 1024 * 1024),
            )
            .unwrap_or_else(|problem| panic!("{source}\n{problem:?}"));
            assert!(
                matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                "{source}\n{:?}",
                result.outcome,
            );
            let fln_kernel::Declaration::Thm(theorem) = result.declaration else {
                panic!("search must produce a theorem, not an axiom");
            };
            assert!(!theorem.value.has_fvar(), "{source}");
            assert!(!theorem.value.has_expr_mvar(), "{source}");
            assert!(!theorem.value.has_level_mvar(), "{source}");
            assert!(!theorem.value.has_loose_bvars(), "{source}");
        }
    }

    #[test]
    fn source_defaults_and_symmetry_never_admit_missing_evidence() {
        let environment = source_environment();
        for source in [
            "theorem unsound : 1 = 2 := by solve_by_elim",
            "theorem unsound (P : Prop) : P := by solve_by_elim",
            "theorem unsound (x y : Nat) : y = x := by solve_by_elim",
            "theorem unsound (P : Prop) (cycle : P -> P) : P := by solve_by_elim",
            "theorem unsound (x y : Nat) (P : Prop) (f : P -> x = y) : y = x := by solve_by_elim",
            "theorem unsound : Nat := by solve_by_elim",
        ] {
            if let Ok(result) = crate::check_definition_source(
                source.as_bytes(),
                &environment,
                Budget::for_stack_bytes(2 * 1024 * 1024),
            ) {
                assert!(
                    !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                    "{source}",
                );
            }
        }
    }
}
