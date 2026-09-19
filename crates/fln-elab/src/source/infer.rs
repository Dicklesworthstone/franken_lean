//! Bounded, untrusted reconstruction of types needed by source constraints.
//!
//! In particular, implicit type arguments can be function types, not just named
//! scalars. Opening binders on an explicit worklist lets their universe equations
//! be generated without recursive host-stack growth or a second trusted checker.

use super::*;

enum Task {
    Visit(Expr),
    Apply(Expr),
    BinderDomain {
        name: Name,
        domain: Expr,
        body: Expr,
        style: BinderInfo,
        lambda: bool,
    },
    BinderBody {
        name: Name,
        domain: Expr,
        id: FVarId,
        level: Level,
        style: BinderInfo,
        lambda: bool,
        saved: LocalContext,
    },
}

impl Context {
    pub(super) fn known_type(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = self.reconstruct_type(expression);
        // Even a resource stop or an unsupported node must not leak the
        // temporary binder context into the surrounding source elaboration.
        self.txn.lctx = saved;
        result
    }

    fn reconstruct_type(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let mut tasks = vec![Task::Visit(expression.clone())];
        let mut types = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(expression) => {
                    let expression = self.instantiate(&expression)?;
                    match expression.node() {
                        ExprNode::MData { expr, .. } => tasks.push(Task::Visit(expr.clone())),
                        ExprNode::LetE { value, body, .. } => {
                            tasks.push(Task::Visit(self.substitute(body, value)?));
                        }
                        ExprNode::App { f, a } => {
                            tasks.push(Task::Apply(a.clone()));
                            tasks.push(Task::Visit(f.clone()));
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        }
                        | ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            tasks.push(Task::BinderDomain {
                                name: binder_name.clone(),
                                domain: binder_type.clone(),
                                body: body.clone(),
                                style: *binder_info,
                                lambda: matches!(expression.node(), ExprNode::Lam { .. }),
                            });
                            tasks.push(Task::Visit(binder_type.clone()));
                        }
                        _ => match self.leaf_type(&expression)? {
                            Some(type_) => types.push(type_),
                            None => return Ok(None),
                        },
                    }
                }
                Task::Apply(argument) => {
                    let type_ = types.pop().expect("function type precedes application");
                    let type_ = self.whnf(&type_)?;
                    let ExprNode::ForallE { body, .. } = type_.node() else {
                        return Ok(None);
                    };
                    types.push(self.substitute(body, &argument)?);
                }
                Task::BinderDomain {
                    name,
                    domain,
                    body,
                    style,
                    lambda,
                } => {
                    let type_ = types.pop().expect("domain type precedes binder opening");
                    let type_ = self.whnf(&type_)?;
                    let ExprNode::Sort { level } = type_.node() else {
                        return Ok(None);
                    };
                    let saved = self.txn.lctx.clone();
                    let id = FVarId(self.fresh_name()?);
                    self.txn
                        .lctx
                        .add_param(id.clone(), name.clone(), domain.clone(), style);
                    let opened = self.substitute(&body, &Expr::fvar(id.clone()))?;
                    tasks.push(Task::BinderBody {
                        name,
                        domain,
                        id,
                        level: level.clone(),
                        style,
                        lambda,
                        saved,
                    });
                    tasks.push(Task::Visit(opened));
                }
                Task::BinderBody {
                    name,
                    domain,
                    id,
                    level,
                    style,
                    lambda,
                    saved,
                } => {
                    let body_type = types.pop().expect("body type precedes binder closing");
                    let type_ = if lambda {
                        let body = body_type
                            .abstract_fvar(&id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                        Expr::forall_e(name, domain, body, style)
                    } else {
                        let body_type = self.whnf(&body_type)?;
                        let ExprNode::Sort { level: body_level } = body_type.node() else {
                            return Ok(None);
                        };
                        Expr::sort(
                            Level::imax(level, body_level.clone())
                                .map_err(|_| failure(SourceInferenceError::Scope))?,
                        )
                    };
                    self.txn.lctx = saved;
                    types.push(type_);
                }
            }
        }
        if types.len() != 1 {
            return Ok(None);
        }
        Ok(types.pop())
    }
}

impl Context {
    /// Comparing function types must constrain the universes of their domains
    /// and codomains, not just the universe of the complete Pi. A whole-Pi
    /// constraint can hide a needed assignment behind a maximum: e.g.
    /// `Nat -> Nat` against `?A -> ?B` does not by itself tell the bounded
    /// universe solver that `?B : Type ?v` requires `?v = 0`.
    ///
    /// These are only inference obligations. The ordinary unifier still checks
    /// the original equation and K1 still validates every assignment. Do not
    /// decompose arbitrary applications: reducible heads can discard arguments.
    pub(super) fn constrain_telescope_universes(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if !actual.has_expr_mvar()
            && !actual.has_level_mvar()
            && !expected.has_expr_mvar()
            && !expected.has_level_mvar()
        {
            return Ok(());
        }
        let saved = self.txn.lctx.clone();
        let result = self.telescope_universe_constraints(actual, expected);
        self.txn.lctx = saved;
        result
    }

    fn telescope_universe_constraints(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let mut pending = vec![(actual.clone(), expected.clone(), self.txn.lctx.clone())];
        while let Some((left, right, scope)) = pending.pop() {
            self.tick()?;
            self.txn.lctx = scope;
            let left = self.instantiate(&left)?;
            let right = self.instantiate(&right)?;
            if let (Some(a), Some(b)) = (self.known_type(&left)?, self.known_type(&right)?)
                && (a.has_level_mvar() || b.has_level_mvar())
            {
                self.equations.push(SourceEquation::inference(a, b));
            }
            if let (
                ExprNode::ForallE {
                    binder_name,
                    binder_type: a,
                    body: ab,
                    binder_info,
                },
                ExprNode::ForallE {
                    binder_type: b,
                    body: bb,
                    ..
                },
            ) = (left.node(), right.node())
            {
                let outer = self.txn.lctx.clone();
                let id = FVarId(self.fresh_name()?);
                let local = Expr::fvar(id.clone());
                let ab = self.substitute(ab, &local)?;
                let bb = self.substitute(bb, &local)?;
                self.txn
                    .lctx
                    .add_param(id, binder_name.clone(), a.clone(), *binder_info);
                pending.push((ab, bb, self.txn.lctx.clone()));
                pending.push((a.clone(), b.clone(), outer));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod telescope_tests {
    use super::*;

    #[test]
    fn every_budget_stop_restores_the_ambient_local_context() {
        let parameter = Name::from_components(["ambient"]);
        let domain = Expr::sort(Level::mvar(LMVarId(Name::from_components(["unknown"]))));
        let fixed = Expr::sort(Level::one());
        let left = Expr::forall_e(
            parameter.clone(),
            domain.clone(),
            domain,
            BinderInfo::Default,
        );
        let right = Expr::forall_e(
            parameter.clone(),
            fixed.clone(),
            fixed.clone(),
            BinderInfo::Default,
        );
        let make_context = || {
            let mut context = Context::new(
                &Environment::new(),
                Budget::for_stack_bytes(2 * 1024 * 1024),
            );
            context.txn.lctx.add_param(
                FVarId(parameter.clone()),
                parameter.clone(),
                fixed.clone(),
                BinderInfo::Default,
            );
            context
        };
        let mut control = make_context();
        let initial = control.txn.lctx.clone();
        control
            .constrain_telescope_universes(&left, &right)
            .unwrap();
        assert_eq!(control.txn.lctx, initial);
        let work = control.txn.budget.heartbeats_consumed;
        assert!(work > 0);
        // A zero heartbeat limit intentionally means unlimited.
        for limit in 1..work {
            let mut stopped = make_context();
            stopped.txn.budget.max_heartbeats = limit;
            assert!(
                stopped
                    .constrain_telescope_universes(&left, &right)
                    .is_err(),
                "{limit}"
            );
            assert_eq!(stopped.txn.lctx, initial, "{limit}");
            assert!(stopped.txn.mvars.assignments().is_empty());
        }
    }
}
