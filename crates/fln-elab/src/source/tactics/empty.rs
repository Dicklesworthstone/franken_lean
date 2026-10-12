//! Empty pattern matrices and `nofun` build ordinary checked eliminations.
//!
//! Columns are consumed on a heap worklist. A constructor branch survives only
//! as another obligation. Nonrecursive constructor fields become new columns.
//! All written discriminants are elaborated before this module is entered and
//! retained as checked lets, including those an earlier contradiction makes
//! computationally irrelevant. Leaves use only selected evidence, never an
//! unrelated ambient hypothesis, to construct a checked contradiction proof.
use super::*;
use fln_env::constants::{ConstantInfo, InductiveVal};
use std::collections::{HashMap, HashSet, VecDeque};

enum EmptyTask {
    Split(ProofGoal, VecDeque<Name>, Vec<Name>),
    Close(ProofGoal, Expr),
}

impl Context {
    pub(in crate::source) fn start_empty_match<'a>(
        &mut self,
        terms: Vec<Typed>,
        expected: Option<Expr>,
    ) -> Result<ProofState<'a>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = self.empty_match_inner(terms, expected);
        self.txn.lctx = saved;
        result
    }

    fn empty_match_inner<'a>(
        &mut self,
        terms: Vec<Typed>,
        expected: Option<Expr>,
    ) -> Result<ProofState<'a>, NatDefinitionElabError> {
        if terms.is_empty() {
            return Err(error(TacticError::EliminationCoverage));
        }
        let target = match expected {
            Some(target) => self.instantiate(&target)?,
            None => {
                let sort = self.type_expected()?;
                self.hole(sort)?
            }
        };
        let (root, mut goal) = self.proof_goal(target.clone())?;
        let mut proof = self.empty_proof_state(target, root);
        let mut columns = Vec::new();
        for term in terms {
            self.tick()?;
            let name = self.fresh_name()?;
            let local = LocalDecl {
                id: FVarId(name.clone()),
                user_name: name.clone(),
                type_: term.type_,
                value: Some(term.value),
                binder_info: BinderInfo::Default,
                index: self.txn.lctx.len(),
            };
            eliminate::add_local(&mut self.txn.lctx, &local);
            goal.introduced.push(local);
            columns.push(name);
        }
        goal.lctx = self.txn.lctx.clone();
        self.solve_empty_matrix(&mut proof, goal, &columns)?;
        Ok(proof)
    }

    pub(in crate::source) fn start_empty_function<'a>(
        &mut self,
        syntax: &Syntax,
        expected: Option<Expr>,
    ) -> Result<ProofState<'a>, NatDefinitionElabError> {
        let parts = expect_node(
            syntax,
            &parser_kind(&["Term", "nofun"]),
            1,
            "empty function",
        )?;
        expect_atom(&parts[0], "nofun", "empty function keyword")?;
        let saved = self.txn.lctx.clone();
        let result = self.empty_function_inner(expected);
        self.txn.lctx = saved;
        result
    }

    fn empty_function_inner<'a>(
        &mut self,
        expected: Option<Expr>,
    ) -> Result<ProofState<'a>, NatDefinitionElabError> {
        let expected = expected.ok_or_else(|| error(TacticError::ExpectedGoal))?;
        let target = self.instantiate(&expected)?;
        let (root, mut goal) = self.proof_goal(target.clone())?;
        let mut proof = self.empty_proof_state(target, root);
        let mut columns = Vec::new();
        // The pin's forallTelescopeReducing opens the entire expected function
        // type. Fresh private locals preserve dependent and implicit binders.
        loop {
            self.tick()?;
            let reduced = self.whnf(&goal.target)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = reduced.node()
            else {
                break;
            };
            let name = self.fresh_name()?;
            let local = LocalDecl {
                id: FVarId(name.clone()),
                user_name: name.clone(),
                type_: binder_type.clone(),
                value: None,
                binder_info: *binder_info,
                index: self.txn.lctx.len(),
            };
            goal.target = self.substitute(body, &Expr::fvar(local.id.clone()))?;
            eliminate::add_local(&mut self.txn.lctx, &local);
            goal.introduced.push(local);
            columns.push(name);
        }
        if columns.is_empty() {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        }
        goal.lctx = self.txn.lctx.clone();
        self.solve_empty_matrix(&mut proof, goal, &columns)?;
        Ok(proof)
    }

    fn empty_proof_state<'a>(&self, target: Expr, root: Expr) -> ProofState<'a> {
        ProofState {
            extent: None,
            saved: self.txn.lctx.clone(),
            target,
            root,
            instructions: Vec::new(),
            cursor: 0,
            work: Vec::new(),
            controls: Vec::new(),
        }
    }

    /// Name actual constructor fields so dependent specialization preserves the
    /// remaining matrix columns. Names are private binders, never evidence.
    fn empty_field_names(
        &mut self,
        family: &InductiveVal,
    ) -> Result<HashMap<Name, Vec<Name>>, NatDefinitionElabError> {
        let mut fields = HashMap::new();
        for name in &family.ctors {
            self.tick()?;
            let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(name) else {
                return Err(error(TacticError::UnsupportedEliminator));
            };
            let count = constructor.num_fields;
            let mut names = Vec::new();
            for _ in 0..count {
                self.tick()?;
                names.push(self.fresh_name()?);
            }
            fields.insert(name.clone(), names);
        }
        Ok(fields)
    }

    fn solve_empty_matrix<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        columns: &[Name],
    ) -> Result<(), NatDefinitionElabError> {
        // The pin's ex-falso transition eliminates proof-valued families into
        // False first. Eliminating Or or Exists directly into data is illegal,
        // even if all of their branches are subsequently proved impossible.
        self.txn.lctx = goal.lctx.clone();
        let false_type = Expr::const_(Name::from_components(["False"]), Vec::new());
        let (absurd, child) = self.proof_goal(false_type.clone())?;
        let value = self
            .empty_evidence(
                &Typed {
                    value: absurd,
                    type_: false_type,
                },
                &goal.target,
            )?
            .ok_or_else(|| error(TacticError::UnsupportedEliminator))?;
        let mut pending = vec![
            EmptyTask::Close(goal, value),
            EmptyTask::Split(child, columns.iter().cloned().collect(), columns.to_vec()),
        ];
        while let Some(task) = pending.pop() {
            self.tick()?;
            let (goal, mut remaining, evidence) = match task {
                EmptyTask::Close(goal, value) => {
                    self.close_proof_goal(goal, value)?;
                    continue;
                }
                EmptyTask::Split(goal, remaining, evidence) => (goal, remaining, evidence),
            };
            self.txn.lctx = goal.lctx.clone();
            let Some(column) = remaining.pop_front() else {
                let mut selected = Vec::new();
                for name in evidence {
                    self.tick()?;
                    if let Some(local) = goal.lctx.find_by_user_name(&name) {
                        selected.push(Typed {
                            value: Expr::fvar(local.id.clone()),
                            type_: local.type_.clone(),
                        });
                    }
                }
                match self.contradict_evidence_goal(goal, selected) {
                    Ok(()) => continue,
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                        TacticError::NoContradiction,
                    ))) => return Err(error(TacticError::EliminationCoverage)),
                    Err(error) => return Err(error),
                }
            };
            let mut local = goal
                .lctx
                .find_by_user_name(&column)
                .cloned()
                .ok_or_else(|| error(TacticError::EliminationLocal))?;
            // Follow exact aliases only. Every written value stays in the
            // outer checked let telescope, including unused trailing inputs.
            let mut seen = HashSet::new();
            while let Some(value) = &local.value {
                self.tick()?;
                let ExprNode::FVar { id } = value.node() else {
                    break;
                };
                if !seen.insert(local.id.clone()) {
                    return Err(error(TacticError::EliminationLocal));
                }
                let Some(original) = goal.lctx.find(id) else {
                    break;
                };
                local = original.clone();
            }
            let type_ = self.whnf(&local.type_)?;
            let mut head = &type_;
            while let ExprNode::App { f, .. } = head.node() {
                self.tick()?;
                head = f;
            }
            let family = match head.node() {
                ExprNode::Const { name, .. } => match self.txn.env.find(name) {
                    Some(ConstantInfo::Induct(family)) => Some(family.clone()),
                    _ => None,
                },
                _ => None,
            };
            let Some(family) = family else {
                pending.push(EmptyTask::Split(goal, remaining, evidence));
                continue;
            };
            let fields = self.empty_field_names(&family)?;
            let mut ordered_fields = Vec::new();
            for constructor in &family.ctors {
                for field in &fields[constructor] {
                    self.tick()?;
                    ordered_fields.push(field.clone());
                }
            }
            // Match.processConstructor first tries cases, so impossible
            // indices can close even a recursive family. If live cases remain,
            // the pin rolls it back rather than descending forever into Nat,
            // lists, or an inductive with only recursive constructors.
            let saved = family.is_rec.then(|| self.clone());
            let original = family.is_rec.then(|| goal.clone());
            let work_start = proof.work.len();
            self.eliminate_proof_goal_with_indices(
                proof,
                goal,
                &eliminate::EliminationSyntax::EmptyMatrix(fields),
                false,
                Some(&local.id),
                None,
            )?;
            if let Some(saved) = saved
                && proof.work[work_start..]
                    .iter()
                    .any(|work| matches!(work, Work::Goal(_)))
            {
                let consumed = self.txn.budget.heartbeats_consumed;
                *self = saved;
                self.txn.budget.heartbeats_consumed = consumed;
                proof.work.truncate(work_start);
                pending.push(EmptyTask::Split(
                    original.expect("recursive case snapshot"),
                    remaining,
                    evidence,
                ));
                continue;
            }
            for work in proof.work.split_off(work_start) {
                self.tick()?;
                pending.push(match work {
                    Work::Goal(child) => {
                        let mut columns = remaining.clone();
                        let mut evidence = evidence.clone();
                        // Other constructors' names do not occur in this
                        // branch. Solved fields have become let aliases; the
                        // pin substitutes and drops those non-variable columns.
                        for name in ordered_fields.iter().rev() {
                            self.tick()?;
                            if child
                                .lctx
                                .find_by_user_name(name)
                                .is_some_and(|local| local.value.is_none())
                            {
                                columns.push_front(name.clone());
                                evidence.push(name.clone());
                            }
                        }
                        EmptyTask::Split(child, columns, evidence)
                    }
                    Work::Close(parent, value) => EmptyTask::Close(parent, value),
                    _ => return Err(failure(SourceInferenceError::Scope)),
                });
            }
        }
        Ok(())
    }
}
