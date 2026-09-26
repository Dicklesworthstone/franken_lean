//! Recover return-stage metadata under the actual lexical capture environment.
//!
//! A source Pi telescope cannot describe where a closure returns another
//! closure. In particular, the annotation on a captured alias is not evidence
//! of its call boundaries. Walk prepared syntax once with scope-local value
//! types; never substitute, execute, eta-expand, or cast the captured value.
use super::*;

fn push<T>(
    values: &mut Vec<T>,
    value: T,
    limit: usize,
    resource: IngressResource,
) -> Result<(), IngressError> {
    let observed = values.len().saturating_add(1);
    if observed > limit {
        return Err(IngressError::ResourceLimit {
            resource,
            limit,
            observed,
        });
    }
    values
        .try_reserve(1)
        .map_err(|_| IngressError::AllocationFailure {
            resource,
            requested: observed,
        })?;
    values.push(value);
    Ok(())
}

enum Work {
    Visit(Expr),
    Let { body: Expr, type_: Expr },
    Leave(usize),
    Arguments(Vec<Expr>),
    Value(Option<ValueType>),
    Lambda { binding: usize, depth: usize },
}

impl Preparation<'_> {
    /// The entry expression has its own lexical scopes and is not a catalog
    /// function. Its prepared local closures need the same capture discovery.
    pub(crate) fn refine_expression_captures(
        &mut self,
        expression: &Expr,
    ) -> Result<(), IngressError> {
        self.captured_result(expression, &[])?;
        Ok(())
    }

    /// Only local lambdas acquire more precise results. A catalog function's
    /// fixed parameter/result ABI, branch ABI, and recursive ABI remain exact.
    pub(in crate::runtime) fn refine_function_captures(
        &mut self,
        functions: &[FunctionBinding],
    ) -> Result<(), IngressError> {
        for function in functions {
            self.tick()?;
            self.captured_result(&function.body, &function.parameters)?;
        }
        Ok(())
    }

    fn captured_result(
        &mut self,
        body: &Expr,
        parameters: &[ValueType],
    ) -> Result<Option<ValueType>, IngressError> {
        let mut context = Vec::new();
        for &parameter in parameters {
            self.tick()?;
            push(
                &mut context,
                Some(parameter),
                self.limits.max_context_depth,
                IngressResource::ContextDepth,
            )?;
        }
        let mut work = Vec::new();
        let mut value = None;
        push(
            &mut work,
            Work::Visit(body.clone()),
            self.limits.max_nodes,
            IngressResource::PendingTasks,
        )?;
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Work::Visit(expr) => match expr.node() {
                    ExprNode::BVar { idx } => {
                        value = usize::try_from(*idx)
                            .ok()
                            .and_then(|index| index.checked_add(1))
                            .and_then(|offset| context.len().checked_sub(offset))
                            .and_then(|index| context[index]);
                    }
                    ExprNode::MData { expr, .. } => push(
                        &mut work,
                        Work::Visit(expr.clone()),
                        self.limits.max_nodes,
                        IngressResource::PendingTasks,
                    )?,
                    ExprNode::LetE {
                        type_,
                        value: initializer,
                        body,
                        ..
                    } => {
                        push(
                            &mut work,
                            Work::Let {
                                body: body.clone(),
                                type_: type_.clone(),
                            },
                            self.limits.max_nodes,
                            IngressResource::PendingTasks,
                        )?;
                        push(
                            &mut work,
                            Work::Visit(initializer.clone()),
                            self.limits.max_nodes,
                            IngressResource::PendingTasks,
                        )?;
                    }
                    ExprNode::Lam { .. } => {
                        let mut found = None;
                        for index in (0..self.lambdas.len()).rev() {
                            self.tick()?;
                            if self.lambdas[index].lambda == expr {
                                found = Some(index);
                                break;
                            }
                        }
                        let Some(index) = found else {
                            // No representation authority: ordinary ingress
                            // will refuse an unannotated executable lambda.
                            value = None;
                            continue;
                        };
                        let binding = &self.lambdas[index];
                        if !matches!(binding.recursion, LambdaRecursion::NonRecursive) {
                            // Recursive lambdas have additional peer binders.
                            // Do not infer their scopes from the public arity.
                            let signature = ClosureSignature {
                                parameters: binding.parameters.clone(),
                                parameter_ownership: binding.parameter_ownership.clone(),
                                result: binding.result,
                                result_ownership: binding.result_ownership,
                            };
                            value = Some(self.stage_interface(signature)?);
                            continue;
                        }
                        if binding.parameters.is_empty() {
                            return Err(unsupported("empty captured callback signature"));
                        }
                        let parameters = binding.parameters.clone();
                        let depth = context.len();
                        let mut body = expr.clone();
                        for parameter in parameters {
                            self.tick()?;
                            let ExprNode::Lam { body: next, .. } = body.node() else {
                                return Err(unsupported("captured callback lambda spine"));
                            };
                            body = next.clone();
                            push(
                                &mut context,
                                Some(parameter),
                                self.limits.max_context_depth,
                                IngressResource::ContextDepth,
                            )?;
                        }
                        push(
                            &mut work,
                            Work::Lambda {
                                binding: index,
                                depth,
                            },
                            self.limits.max_nodes,
                            IngressResource::PendingTasks,
                        )?;
                        push(
                            &mut work,
                            Work::Visit(body),
                            self.limits.max_nodes,
                            IngressResource::PendingTasks,
                        )?;
                    }
                    ExprNode::App { .. } => {
                        let (head, arguments) = self.spine(&expr)?;
                        push(
                            &mut work,
                            Work::Arguments(arguments),
                            self.limits.max_nodes,
                            IngressResource::PendingTasks,
                        )?;
                        push(
                            &mut work,
                            Work::Visit(head),
                            self.limits.max_nodes,
                            IngressResource::PendingTasks,
                        )?;
                    }
                    ExprNode::Const { .. } => {
                        value = match self.callable_type(&expr)? {
                            Some(type_) => self.value_type(&type_)?,
                            None => None,
                        };
                    }
                    ExprNode::Proj { expr, .. } => {
                        // Inspect the receiver for nested local closures, but
                        // its own interface is not the selected field's type.
                        push(
                            &mut work,
                            Work::Value(None),
                            self.limits.max_nodes,
                            IngressResource::PendingTasks,
                        )?;
                        push(
                            &mut work,
                            Work::Visit(expr.clone()),
                            self.limits.max_nodes,
                            IngressResource::PendingTasks,
                        )?;
                    }
                    _ => value = None,
                },
                Work::Let { body, type_ } => {
                    if value.is_none() {
                        value = self.value_type(&type_)?;
                    }
                    let depth = context.len();
                    push(
                        &mut context,
                        value,
                        self.limits.max_context_depth,
                        IngressResource::ContextDepth,
                    )?;
                    push(
                        &mut work,
                        Work::Leave(depth),
                        self.limits.max_nodes,
                        IngressResource::PendingTasks,
                    )?;
                    push(
                        &mut work,
                        Work::Visit(body),
                        self.limits.max_nodes,
                        IngressResource::PendingTasks,
                    )?;
                }
                Work::Leave(depth) => context.truncate(depth),
                Work::Arguments(arguments) => {
                    let result = match value {
                        Some(value) => self.stage_apply(value, arguments.len())?,
                        None => None,
                    };
                    push(
                        &mut work,
                        Work::Value(result),
                        self.limits.max_nodes,
                        IngressResource::PendingTasks,
                    )?;
                    // Arguments can contain closures capturing the surrounding
                    // let telescope even when the callee itself is unknown.
                    for argument in arguments.into_iter().rev() {
                        self.tick()?;
                        push(
                            &mut work,
                            Work::Visit(argument),
                            self.limits.max_nodes,
                            IngressResource::PendingTasks,
                        )?;
                    }
                }
                Work::Value(result) => value = result,
                Work::Lambda {
                    binding: index,
                    depth,
                } => {
                    context.truncate(depth);
                    let binding = &self.lambdas[index];
                    let local = matches!(binding.lambda.node(), ExprNode::Lam { binder_name, .. }
                        if binder_name.parent().eq(&name("_fln_runtime_local")));
                    let expected = binding.result;
                    if local
                        && let Some(actual @ ValueType::Closure(_)) = value
                        && actual != expected
                        && matches!(expected, ValueType::Closure(_))
                        && self.same_stage_telescope(actual, expected)?
                    {
                        self.lambdas[index].result = actual;
                        self.lambdas[index].result_ownership = result_ownership(actual);
                    }
                    let binding = &self.lambdas[index];
                    let signature = ClosureSignature {
                        parameters: binding.parameters.clone(),
                        parameter_ownership: binding.parameter_ownership.clone(),
                        result: binding.result,
                        result_ownership: binding.result_ownership,
                    };
                    value = Some(self.stage_interface(signature)?);
                }
            }
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
