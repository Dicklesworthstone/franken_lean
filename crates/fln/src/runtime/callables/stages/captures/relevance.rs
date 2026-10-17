//! Decide whether a prepared catalog body can change local capture metadata.
//!
//! The full capture pass discovers value types even when nobody consumes its
//! result. Catalog bodies only need it for a local lambda's closure result.
//! Scan the same executable paths without reconstructing those unused types;
//! whole interfaces and suffixes of live bindings are collected at finalization.
use super::*;

enum Work {
    Visit { expression: Expr, depth: usize },
    Let { body: Expr, depth: usize },
    Arguments { arguments: Vec<Expr>, depth: usize },
}

fn enter(depth: usize, limit: usize) -> Result<usize, IngressError> {
    let observed = depth.checked_add(1).ok_or(IngressError::ResourceLimit {
        resource: IngressResource::ContextDepth,
        limit,
        observed: usize::MAX,
    })?;
    if observed > limit {
        return Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit,
            observed,
        });
    }
    Ok(observed)
}

pub(super) fn contains_candidate(
    preparation: &mut Preparation<'_>,
    expression: &Expr,
    parameters: &[ValueType],
    lambdas: &LambdaIndex,
) -> Result<bool, IngressError> {
    let mut depth = 0;
    for _ in parameters {
        preparation.tick()?;
        depth = enter(depth, preparation.limits.max_context_depth)?;
    }
    let mut work = Vec::new();
    push(
        &mut work,
        Work::Visit {
            expression: expression.clone(),
            depth,
        },
        preparation.limits.max_nodes,
        IngressResource::PendingTasks,
    )?;
    while let Some(task) = work.pop() {
        preparation.tick()?;
        match task {
            Work::Visit { expression, depth } => match expression.node() {
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => push(
                    &mut work,
                    Work::Visit {
                        expression: expr.clone(),
                        depth,
                    },
                    preparation.limits.max_nodes,
                    IngressResource::PendingTasks,
                )?,
                ExprNode::LetE { value, body, .. } => {
                    // The initializer belongs to the outer scope. Enter the
                    // body's slot only after that initializer has been scanned.
                    push(
                        &mut work,
                        Work::Let {
                            body: body.clone(),
                            depth,
                        },
                        preparation.limits.max_nodes,
                        IngressResource::PendingTasks,
                    )?;
                    push(
                        &mut work,
                        Work::Visit {
                            expression: value.clone(),
                            depth,
                        },
                        preparation.limits.max_nodes,
                        IngressResource::PendingTasks,
                    )?;
                }
                ExprNode::Lam { .. } => {
                    let Some(index) = lambdas.get(preparation, &expression)? else {
                        // As in captured_result_in, absent representation
                        // authority is left for executable ingress to refuse.
                        continue;
                    };
                    let binding = &preparation.lambdas[index];
                    if !matches!(binding.recursion, LambdaRecursion::NonRecursive) {
                        // Recursive rows have synthetic peer binders. The full
                        // pass stops here too instead of guessing their scopes.
                        continue;
                    }
                    let arity = binding.parameters.len();
                    if arity == 0 {
                        return Err(unsupported("empty captured callback signature"));
                    }
                    let candidate = can_refine(binding);
                    let mut body = expression.clone();
                    let mut depth = depth;
                    for _ in 0..arity {
                        preparation.tick()?;
                        let ExprNode::Lam { body: next, .. } = body.node() else {
                            return Err(unsupported("captured callback lambda spine"));
                        };
                        body = next.clone();
                        depth = enter(depth, preparation.limits.max_context_depth)?;
                    }
                    if candidate {
                        return Ok(true);
                    }
                    // Fixed and scalar-result lambdas can still contain local
                    // closures that capture this exact surrounding telescope.
                    push(
                        &mut work,
                        Work::Visit {
                            expression: body,
                            depth,
                        },
                        preparation.limits.max_nodes,
                        IngressResource::PendingTasks,
                    )?;
                }
                ExprNode::App { .. } => {
                    // Reuse the ordinary bounded spine parser: skipping type
                    // discovery must not bypass the application-arity limit.
                    let (head, arguments) = preparation.spine(&expression)?;
                    push(
                        &mut work,
                        Work::Arguments { arguments, depth },
                        preparation.limits.max_nodes,
                        IngressResource::PendingTasks,
                    )?;
                    push(
                        &mut work,
                        Work::Visit {
                            expression: head,
                            depth,
                        },
                        preparation.limits.max_nodes,
                        IngressResource::PendingTasks,
                    )?;
                }
                _ => {}
            },
            Work::Let { body, depth } => {
                let depth = enter(depth, preparation.limits.max_context_depth)?;
                push(
                    &mut work,
                    Work::Visit {
                        expression: body,
                        depth,
                    },
                    preparation.limits.max_nodes,
                    IngressResource::PendingTasks,
                )?;
            }
            Work::Arguments { arguments, depth } => {
                for argument in arguments.into_iter().rev() {
                    preparation.tick()?;
                    push(
                        &mut work,
                        Work::Visit {
                            expression: argument,
                            depth,
                        },
                        preparation.limits.max_nodes,
                        IngressResource::PendingTasks,
                    )?;
                }
            }
        }
    }
    Ok(false)
}

#[cfg(test)]
mod tests;
