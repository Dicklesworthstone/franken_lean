//! Generic associative normalization for `ac_rfl`.
//!
//! The laws come from the ordinary instance registry, never from the spelling of
//! an operator. `reflection` builds the pin's `Lean.Data.AC.Context.eq_of_norm`
//! certificate; the normalizer is only a candidate producer. Congruence and the
//! final `Eq.refl` remain ordinary terms checked with the complete declaration.
//! Binder bodies and dependent arguments are left opaque in this initial slice.
//! If they prevent closure, report a capability stop rather than a failed proof.

mod reflection;

use super::*;
use std::collections::HashMap;

const MAX_AC_NODES: usize = 4096;

#[derive(Clone)]
struct Laws {
    operator: Expr,
    alpha: Expr,
    level: Level,
    associative: Expr,
    commutative: Option<Expr>,
    idempotent: Option<Expr>,
}

struct Normalized {
    value: Expr,
    proof: Option<Expr>,
    incomplete: bool,
}

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn unsupported() -> NatDefinitionElabError {
    error(TacticError::UnsupportedTactic(parser_kind(&[
        "Tactic", "acRfl",
    ])))
}

fn binary(term: &Expr) -> Option<(&Expr, &Expr, &Expr)> {
    let ExprNode::App { f, a: right } = term.node() else {
        return None;
    };
    let ExprNode::App {
        f: operator,
        a: left,
    } = f.node()
    else {
        return None;
    };
    Some((operator, left, right))
}

impl Context {
    pub(super) fn ac_reflexivity(&mut self, goal: ProofGoal) -> Result<(), NatDefinitionElabError> {
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "acRfl"])?;
        self.txn.lctx = goal.lctx.clone();
        self.resolve_instances(false)?;
        self.flush(false)?;
        let target = self.instantiate(&goal.target)?;
        let exposed = self.whnf(&target)?;
        if equality_target(&exposed).is_none() {
            return Err(error(TacticError::ExpectedEquality));
        }
        if target.has_expr_mvar() || target.has_loose_bvars() {
            return Err(unsupported());
        }
        let normalized = self.ac_normalize(&target)?;
        let (witness, child) = self.proof_goal(normalized.value.clone())?;
        if let Err(problem) = self.eq_refl_proof_goal(child, false) {
            return if normalized.incomplete && backtrack::recoverable(&problem) {
                Err(unsupported())
            } else {
                Err(problem)
            };
        }
        let value = match normalized.proof {
            None => witness,
            Some(proof) => apply(
                Expr::const_(name("Eq.mpr"), vec![Level::zero()]),
                [target, normalized.value, proof, witness],
            ),
        };
        self.close_proof_goal(goal, value)
    }

    fn ac_instance(&mut self, target: Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut trial = self.clone();
        let locals = trial.txn.lctx.clone();
        let result = (|| {
            let hole = trial.instance_hole(target)?;
            let ExprNode::MVar { id } = hole.node() else {
                return Err(failure(SourceInferenceError::Scope));
            };
            let registry = trial
                .registry_cache
                .read_with_scopes(&trial.txn.env, &trial.source_scope.instance_scopes)
                .map_err(|problem| failure(SourceInferenceError::InstanceRegistry(problem)))?;
            match trial.search_instance(id.clone(), &registry)? {
                super::super::instances::SearchResult::Solved => {
                    let value = trial.instantiate(&hole)?;
                    if value.has_expr_mvar() {
                        return Err(unsupported());
                    }
                    Ok(Some(value))
                }
                super::super::instances::SearchResult::Failed => Ok(None),
                super::super::instances::SearchResult::Stuck => Err(unsupported()),
            }
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        if matches!(&result, Ok(Some(_))) {
            trial.txn.lctx = locals;
            *self = trial;
        }
        result
    }

    fn ac_laws(
        &mut self,
        operator: &Expr,
        left: &Expr,
    ) -> Result<Option<Laws>, NatDefinitionElabError> {
        if !self.txn.env.contains(&name("Std.Associative")) {
            return Ok(None);
        }
        let alpha = self
            .known_type(left)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let sort = self
            .known_type(&alpha)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let level = self.sort_level(&Typed {
            value: alpha.clone(),
            type_: sort,
        })?;
        // Most application prefixes are not homogeneous binary operations.
        // Do not submit ill-typed class applications to instance search.
        let function_type = self
            .known_type(operator)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let operation_type = Expr::forall_e(
            Name::anonymous(),
            alpha.clone(),
            Expr::forall_e(
                Name::anonymous(),
                alpha.clone(),
                alpha.clone(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let mut budget = self.ambient_budget(UnificationTransparency::Default);
        budget.max_assignments = 0;
        if !self.proof_types_match_with_budget(&function_type, &operation_type, budget)? {
            return Ok(None);
        }
        let class = |class| {
            apply(
                Expr::const_(name(class), vec![level.clone()]),
                [alpha.clone(), operator.clone()],
            )
        };
        let Some(associative) = self.ac_instance(class("Std.Associative"))? else {
            return Ok(None);
        };
        let commutative = self.ac_instance(class("Std.Commutative"))?;
        let idempotent = self.ac_instance(class("Std.IdempotentOp"))?;
        Ok(Some(Laws {
            operator: operator.clone(),
            alpha,
            level,
            associative,
            commutative,
            idempotent,
        }))
    }

    fn ac_equation(&mut self, left: &Expr, right: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let alpha = self
            .known_type(left)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let sort = self
            .known_type(&alpha)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let level = self.sort_level(&Typed {
            value: alpha.clone(),
            type_: sort,
        })?;
        Ok(equality::equation(
            level,
            alpha,
            left.clone(),
            right.clone(),
        ))
    }

    fn ac_join(
        &mut self,
        original: &Expr,
        previous: &Expr,
        next: &Expr,
        first: Option<Expr>,
        second: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let Some(first) = first else {
            return Ok(second);
        };
        let equation = self.ac_equation(original, next)?;
        let (level, alpha, ..) =
            equality_target(&equation).ok_or_else(|| failure(SourceInferenceError::Scope))?;
        Ok(apply(
            Expr::const_(name("Eq.trans"), vec![level]),
            [
                alpha,
                original.clone(),
                previous.clone(),
                next.clone(),
                first,
                second,
            ],
        ))
    }

    /// Congruence changes exactly one immediate child. A whole-expression
    /// rewrite would also change identical copies inside a sibling, invalidating
    /// the sibling's already-computed normalization or entering a dependent
    /// argument that the traversal intentionally left opaque.
    fn ac_congruence(
        &mut self,
        current: &Expr,
        slot: usize,
        child: &Expr,
        normalized: &Expr,
        proof: Expr,
    ) -> Result<(Expr, Expr), NatDefinitionElabError> {
        let equation = self.ac_equation(child, normalized)?;
        let (u, alpha, ..) =
            equality_target(&equation).ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let marker = self.equality_local(alpha.clone())?;
        let rebuild = |replacement| match (current.node(), slot) {
            (ExprNode::App { a, .. }, 0) => Some(Expr::app(replacement, a.clone())),
            (ExprNode::App { f, .. }, 1) => Some(Expr::app(f.clone(), replacement)),
            (ExprNode::MData { data, .. }, 0) => Some(Expr::mdata(data.clone(), replacement)),
            _ => None,
        };
        let body = rebuild(Expr::fvar(marker.id.clone()))
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let next =
            rebuild(normalized.clone()).ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let target_type = self
            .known_type(current)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let sort = self
            .known_type(&target_type)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let v = self.sort_level(&Typed {
            value: target_type.clone(),
            type_: sort,
        })?;
        let motive = Expr::lam(
            marker.user_name,
            alpha.clone(),
            body.abstract_fvar(&marker.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
        let evidence = apply(
            Expr::const_(name("congrArg"), vec![u, v]),
            [
                alpha,
                target_type,
                child.clone(),
                normalized.clone(),
                motive,
                proof,
            ],
        );
        Ok((next, evidence))
    }

    fn ac_normalize(&mut self, root: &Expr) -> Result<Normalized, NatDefinitionElabError> {
        enum Task {
            Visit(Expr),
            Build {
                original: Expr,
                children: Vec<Expr>,
                start: usize,
                incomplete: bool,
            },
        }
        let mut pending = vec![Task::Visit(root.clone())];
        let mut values: Vec<Normalized> = Vec::new();
        let mut laws: HashMap<Expr, Option<Laws>> = HashMap::new();
        let mut visited = 0usize;
        while let Some(task) = pending.pop() {
            self.tick()?;
            match task {
                Task::Visit(original) => {
                    visited += 1;
                    if visited > MAX_AC_NODES {
                        return Err(failure(SourceInferenceError::ResourceLimit));
                    }
                    let mut incomplete = false;
                    let children = match original.node() {
                        ExprNode::App { f, a } => {
                            let function_type = self
                                .known_type(f)?
                                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                            let function_type = self.whnf(&function_type)?;
                            let ExprNode::ForallE { body, .. } = function_type.node() else {
                                return Err(unsupported());
                            };
                            if body.has_loose_bvar(0) {
                                incomplete = matches!(
                                    a.node(),
                                    ExprNode::App { .. }
                                        | ExprNode::Lam { .. }
                                        | ExprNode::ForallE { .. }
                                        | ExprNode::LetE { .. }
                                        | ExprNode::MData { .. }
                                        | ExprNode::Proj { .. }
                                );
                                vec![f.clone()]
                            } else {
                                vec![f.clone(), a.clone()]
                            }
                        }
                        ExprNode::MData { expr, .. } => {
                            vec![expr.clone()]
                        }
                        ExprNode::Lam { .. }
                        | ExprNode::ForallE { .. }
                        | ExprNode::LetE { .. }
                        | ExprNode::Proj { .. } => {
                            incomplete = true;
                            Vec::new()
                        }
                        _ => Vec::new(),
                    };
                    pending.push(Task::Build {
                        original,
                        children: children.clone(),
                        start: values.len(),
                        incomplete,
                    });
                    pending.extend(children.into_iter().rev().map(Task::Visit));
                }
                Task::Build {
                    original,
                    children,
                    start,
                    mut incomplete,
                } => {
                    let descendants = values.split_off(start);
                    let mut current = original.clone();
                    let mut proof = None;
                    for (slot, (child, normalized)) in
                        children.into_iter().zip(descendants).enumerate()
                    {
                        incomplete |= normalized.incomplete;
                        let Some(value) = normalized.proof else {
                            continue;
                        };
                        let (next, step) =
                            self.ac_congruence(&current, slot, &child, &normalized.value, value)?;
                        proof = Some(self.ac_join(&original, &current, &next, proof, step)?);
                        current = next;
                    }
                    if let Some((operator, left, _)) = binary(&current) {
                        let operator = operator.clone();
                        if !laws.contains_key(&operator) {
                            let found = self.ac_laws(&operator, left)?;
                            laws.insert(operator.clone(), found);
                        }
                        if let Some(Some(laws)) = laws.get(&operator) {
                            let (next, step) = self.ac_normalize_operator(&current, laws)?;
                            if let Some(step) = step {
                                proof =
                                    Some(self.ac_join(&original, &current, &next, proof, step)?);
                                current = next;
                            }
                        }
                    }
                    values.push(Normalized {
                        value: current,
                        proof,
                        incomplete,
                    });
                }
            }
        }
        values
            .pop()
            .ok_or_else(|| failure(SourceInferenceError::Scope))
    }
}
