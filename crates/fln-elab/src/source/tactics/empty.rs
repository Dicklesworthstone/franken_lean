//! Empty pattern matrices and `nofun` build ordinary checked eliminations.
//!
//! Columns are consumed on a heap worklist. A constructor branch survives only
//! as another obligation; running out of columns with any live goal refuses.
//! All written discriminants are elaborated before this module is entered and
//! retained as checked lets, including those an earlier contradiction makes
//! computationally irrelevant. No ambient assumption search supplies a result.
use super::*;
use fln_env::constants::ConstantInfo;
use std::collections::HashSet;

enum EmptyTask {
    Split(ProofGoal, usize),
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

    fn solve_empty_matrix<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        columns: &[Name],
    ) -> Result<(), NatDefinitionElabError> {
        let mut pending = vec![EmptyTask::Split(goal, 0)];
        while let Some(task) = pending.pop() {
            self.tick()?;
            let (goal, next) = match task {
                EmptyTask::Close(goal, value) => {
                    self.close_proof_goal(goal, value)?;
                    continue;
                }
                EmptyTask::Split(goal, next) => (goal, next),
            };
            self.txn.lctx = goal.lctx.clone();
            let Some(column) = columns.get(next) else {
                return Err(error(TacticError::EliminationCoverage));
            };
            let mut local = goal
                .lctx
                .find_by_user_name(column)
                .cloned()
                .ok_or_else(|| error(TacticError::EliminationLocal))?;
            // Follow only exact aliases. Arbitrary reduction here would drop
            // written lets or separate a later column from its original index.
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
            let inductive = matches!(head.node(), ExprNode::Const { name, .. }
                if matches!(self.txn.env.find(name), Some(ConstantInfo::Induct(_))));
            if !inductive {
                // Types and abstract parameters cannot be split. They remain
                // checked binders; a later supplied column must prove emptiness.
                pending.push(EmptyTask::Split(goal, next + 1));
                continue;
            }
            self.eliminate_proof_goal_with_indices(
                proof,
                goal,
                &eliminate::EliminationSyntax::EmptyMatrix,
                false,
                Some(&local.id),
                None,
            )?;
            // Preserve the ordinary proof driver's LIFO order: all child
            // obligations finish before the parent recursor is assigned.
            for work in proof.work.drain(..) {
                self.tick()?;
                pending.push(match work {
                    Work::Goal(child) => EmptyTask::Split(child, next + 1),
                    Work::Close(parent, value) => EmptyTask::Close(parent, value),
                    _ => return Err(failure(SourceInferenceError::Scope)),
                });
            }
        }
        Ok(())
    }
}
