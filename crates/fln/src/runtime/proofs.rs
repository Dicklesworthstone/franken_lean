//! Post-admission proof erasure. A proof occupies an inert scalar slot in this
//! bounded FIR profile; its construction is never compiled or executed. Keeping
//! slots preserves source de Bruijn indices and field positions. This is not the
//! Reference's packed ABI and does not change any declaration sent to a checker.
use super::*;
use fln_core::level::Level;
mod locals;
mod projections;

// Bool.false is the existing, checked scalar-zero binding. Source typing forbids
// observing a proof as a Bool; this representation exists only after admission.
fn erased_type() -> Expr {
    Expr::const_(name("Bool"), vec![])
}
fn erased_value() -> Expr {
    Expr::const_(name("Bool.false"), vec![])
}

enum Frame {
    Visit(Expr, Option<Expr>),
    Keep(Expr),
    Apply(usize),
    Lambda(Name, Expr, BinderInfo),
    LetValue(Name, Expr, Expr, Expr, bool),
    LetBody(Name, Expr, Expr, bool),
    Projection(Name, u64),
}

impl Preparation<'_> {
    fn proof_erasure_available(&self) -> bool {
        source_scalar_constructor_binding(self.environment, &name("Bool.false")).is_some()
    }

    fn push_proof_local(
        &mut self,
        locals: &mut Vec<Expr>,
        type_: Expr,
    ) -> Result<(), IngressError> {
        self.tick()?;
        let observed = locals.len().saturating_add(1);
        if observed > self.limits.max_context_depth {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: self.limits.max_context_depth,
                observed,
            });
        }
        locals
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ContextDepth,
                requested: observed,
            })?;
        locals.push(type_);
        Ok(())
    }
    fn copy_proof_context(&mut self, context: &[Expr]) -> Result<Vec<Expr>, IngressError> {
        let mut locals = Vec::new();
        for type_ in context {
            self.push_proof_local(&mut locals, type_.clone())?;
        }
        Ok(locals)
    }

    /// Classify an already checked type, not an untrusted proposition by name.
    /// Pi types are propositions exactly when their codomain is a proposition.
    /// Unknown types remain unknown; resource exhaustion is never an erasure.
    pub(super) fn proposition_type(
        &mut self,
        input: &Expr,
        context: &[Expr],
    ) -> Result<bool, IngressError> {
        let mut locals = self.copy_proof_context(context)?;
        let mut type_ = input.clone();
        loop {
            self.tick()?;
            match type_.node() {
                ExprNode::Sort { .. } => return Ok(false),
                ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    self.push_proof_local(&mut locals, binder_type.clone())?;
                    type_ = body.clone();
                }
                _ => {
                    let Some(sort) = self.projection_receiver_type(&type_, &locals)? else {
                        return Ok(false);
                    };
                    let sort = self.type_head(&sort)?;
                    return Ok(
                        matches!(sort.node(), ExprNode::Sort { level } if level == &Level::zero()),
                    );
                }
            }
        }
    }

    /// Only runtime domains/results are replaced. Type arguments to a family
    /// retain their original syntax for monomorphization and layout discovery.
    pub(super) fn erase_runtime_type(&mut self, input: &Expr) -> Result<Expr, IngressError> {
        if !self.proof_erasure_available() {
            return self.erase_data_indices(input);
        }
        self.erase_type_in(input, &[])
    }

    fn erase_type_in(&mut self, input: &Expr, context: &[Expr]) -> Result<Expr, IngressError> {
        self.erase_domains(input, context)
    }

    fn erase_domains(&mut self, input: &Expr, context: &[Expr]) -> Result<Expr, IngressError> {
        enum Work {
            Visit(Expr),
            Domain(Name, Expr, Expr, BinderInfo),
            Body(Name, Expr, BinderInfo),
        }
        let mut locals = self.copy_proof_context(context)?;
        let mut work = vec![Work::Visit(input.clone())];
        let mut values = Vec::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Work::Visit(source) => {
                    if self.proposition_type(&source, &locals)? {
                        reserve(&mut values, self.limits.max_nodes)?;
                        values.push(erased_type());
                        continue;
                    }
                    let normal = self.type_head(&source)?;
                    if let ExprNode::ForallE {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } = normal.node()
                    {
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Domain(
                            binder_name.clone(),
                            binder_type.clone(),
                            body.clone(),
                            *binder_info,
                        ));
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Visit(binder_type.clone()));
                    } else {
                        reserve(&mut values, self.limits.max_nodes)?;
                        values.push(self.erase_data_indices(&normal)?);
                    }
                }
                Work::Domain(name, original, body, info) => {
                    let domain = values
                        .pop()
                        .ok_or_else(|| unsupported("proof type domain"))?;
                    self.push_proof_local(&mut locals, original)?;
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Body(name, domain, info));
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Visit(body));
                }
                Work::Body(name, domain, info) => {
                    locals.pop();
                    let body = values.pop().ok_or_else(|| unsupported("proof type body"))?;
                    values.push(Expr::forall_e(name, domain, body, info));
                }
            }
        }
        values.pop().ok_or_else(|| unsupported("proof type result"))
    }

    pub(super) fn erase_proofs(
        &mut self,
        input: &Expr,
        expected: Option<Expr>,
    ) -> Result<Expr, IngressError> {
        if !self.proof_erasure_available() {
            return Ok(input.clone());
        }
        let mut context = Vec::new();
        let mut work = vec![Frame::Visit(input.clone(), expected)];
        let mut values = Vec::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Frame::Visit(expr, expected) => {
                    let expected = match expected {
                        Some(type_) => Some(type_),
                        // Typed parents classify proof-producing binders. Do
                        // not reinfer each suffix of a long lambda/let chain.
                        None if matches!(
                            expr.node(),
                            ExprNode::Lam { .. } | ExprNode::LetE { .. } | ExprNode::Lit { .. }
                        ) =>
                        {
                            None
                        }
                        None => self.projection_receiver_type(&expr, &context)?,
                    };
                    if let Some(type_) = &expected
                        && self.proposition_type(type_, &context)?
                    {
                        reserve(&mut values, self.limits.max_nodes)?;
                        values.push(erased_value());
                        continue;
                    }
                    match expr.node() {
                        ExprNode::App { .. } => {
                            let (head, args) = self.spine(&expr)?;
                            let mut type_ = self.projection_receiver_type(&head, &context)?;
                            let mut arguments = Vec::new();
                            for arg in &args {
                                self.tick()?;
                                let domain = if let Some(current) = type_ {
                                    let normal = self.type_head(&current)?;
                                    if let ExprNode::ForallE {
                                        binder_type, body, ..
                                    } = normal.node()
                                    {
                                        type_ = Some(self.substitution(body, arg)?);
                                        Some(binder_type.clone())
                                    } else {
                                        type_ = None;
                                        None
                                    }
                                } else {
                                    None
                                };
                                // Preserve motives and type arguments verbatim.
                                // They are inputs to checked-family recognition,
                                // not runtime proof computations.
                                let static_type = match &domain {
                                    Some(domain) => self.type_parameter(domain)?,
                                    None => false,
                                };
                                reserve(&mut arguments, self.limits.max_application_args)?;
                                arguments.push(if static_type {
                                    Frame::Keep(arg.clone())
                                } else {
                                    Frame::Visit(arg.clone(), domain)
                                });
                            }
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Frame::Apply(args.len()));
                            for task in arguments.into_iter().rev() {
                                reserve(&mut work, self.limits.max_nodes)?;
                                work.push(task);
                            }
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Frame::Visit(head, None));
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            let type_ = self.erase_type_in(binder_type, &context)?;
                            self.push_proof_local(&mut context, binder_type.clone())?;
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Frame::Lambda(binder_name.clone(), type_, *binder_info));
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Frame::Visit(body.clone(), None));
                        }
                        ExprNode::LetE {
                            decl_name: binder_name,
                            type_,
                            value,
                            body,
                            non_dep: nondep,
                        } => {
                            if self.type_parameter(type_)? {
                                // Source matching retains type-valued let obligations
                                // for both checkers. After admission they are static
                                // type bindings, not executable callbacks. Substitute
                                // capture-avoidantly before erasing runtime annotations.
                                let body = self.substitution(body, value)?;
                                reserve(&mut work, self.limits.max_nodes)?;
                                work.push(Frame::Visit(body, expected));
                                continue;
                            }
                            if let Some(lambda) = self.local_callable_template(value, type_)? {
                                // A local name must not hide a generic or staged
                                // literal helper from later call-site specialization.
                                // Only lambda syntax moves; computed initializers
                                // retain the ordinary strict binding below.
                                let body = self.substitution(body, &lambda)?;
                                reserve(&mut work, self.limits.max_nodes)?;
                                work.push(Frame::Visit(body, expected));
                                continue;
                            }
                            let runtime_type = self.erase_type_in(type_, &context)?;
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Frame::LetValue(
                                binder_name.clone(),
                                type_.clone(),
                                runtime_type,
                                body.clone(),
                                *nondep,
                            ));
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Frame::Visit(value.clone(), Some(type_.clone())));
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => {
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Frame::Projection(struct_name.clone(), *idx));
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Frame::Visit(expr.clone(), None));
                        }
                        ExprNode::MData { expr, .. } => {
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Frame::Visit(expr.clone(), expected));
                        }
                        _ => {
                            reserve(&mut values, self.limits.max_nodes)?;
                            values.push(expr);
                        }
                    }
                }
                Frame::Keep(expr) => {
                    reserve(&mut values, self.limits.max_nodes)?;
                    values.push(expr);
                }
                Frame::Apply(count) => {
                    let start = values
                        .len()
                        .checked_sub(count + 1)
                        .ok_or_else(|| unsupported("proof application stack"))?;
                    let mut args = values.drain(start..);
                    let mut expr = args
                        .next()
                        .ok_or_else(|| unsupported("proof application head"))?;
                    for arg in args {
                        expr = Expr::app(expr, arg);
                    }
                    values.push(expr);
                }
                Frame::Lambda(name, domain, info) => {
                    context.pop();
                    let body = values
                        .pop()
                        .ok_or_else(|| unsupported("proof lambda body"))?;
                    values.push(Expr::lam(name, domain, body, info));
                }
                Frame::LetValue(name, original, type_, body, nondep) => {
                    let value = values.pop().ok_or_else(|| unsupported("proof let value"))?;
                    self.push_proof_local(&mut context, original)?;
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Frame::LetBody(name, type_, value, nondep));
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Frame::Visit(body, None));
                }
                Frame::LetBody(name, type_, value, nondep) => {
                    context.pop();
                    let body = values.pop().ok_or_else(|| unsupported("proof let body"))?;
                    values.push(Expr::let_e(name, type_, value, body, nondep));
                }
                Frame::Projection(name, index) => {
                    let expr = values
                        .pop()
                        .ok_or_else(|| unsupported("proof projection receiver"))?;
                    values.push(Expr::proj(name, index, expr));
                }
            }
        }
        if values.len() != 1 || !context.is_empty() {
            return Err(unsupported("proof erasure result"));
        }
        Ok(values.pop().expect("one proof-erased expression"))
    }
}

#[cfg(test)]
mod tests;
