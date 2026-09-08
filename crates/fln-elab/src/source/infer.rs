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
