//! Bounded administrative evaluation of closed instance factories.
//!
//! Lambda bodies remain code until applied. Every supplied argument, local
//! initializer and constructor operand must independently be inert, even when
//! the result would discard it. Intrinsics, recursors, axioms, unsafe bodies
//! and open values never become compile-time dictionary evidence.
use super::*;
use std::collections::VecDeque;

enum Task {
    Value(Expr),
    Constructor(Expr, usize),
    Application(usize),
    Continue(VecDeque<Expr>),
    Let(Expr),
}

fn push(tasks: &mut Vec<Task>, task: Task, limit: usize) -> Result<(), IngressError> {
    reserve(tasks, limit)?;
    tasks.push(task);
    Ok(())
}

impl Preparation<'_> {
    /// Return an inert value, not a kernel normal form. This private result is
    /// substituted only for a static instance argument after source admission;
    /// the specialization key retains the caller's exact original argument.
    pub(super) fn instance_factory_value(
        &mut self,
        input: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        self.tick()?;
        if !closed(input) {
            return Ok(None);
        }
        // Preserve the existing accepted profile, including opaque type-only
        // constructor parameters. Factory evaluation only extends that profile;
        // it must not make an already supported dictionary require more erasure.
        if self.static_value(input)? {
            return Ok(Some(input.clone()));
        }
        let mut tasks = vec![Task::Value(input.clone())];
        let mut values = Vec::new();
        let limit = self.limits.max_nodes;
        while let Some(task) = tasks.pop() {
            self.tick()?;
            reserve(&mut values, limit)?;
            match task {
                Task::Value(expression) => {
                    let (head, arguments) = self.spine(&expression)?;
                    if let ExprNode::Const { name, levels } = head.node() {
                        match self.environment.find(name) {
                            Some(ConstantInfo::Induct(family))
                                if !family.is_unsafe
                                    && levels.len() == family.base.level_params.len() =>
                            {
                                // A checked type value does not evaluate its
                                // indices. Its original syntax remains a type.
                                values.push(expression);
                                continue;
                            }
                            Some(ConstantInfo::Ctor(constructor))
                                if !constructor.is_unsafe
                                    && levels.len() == constructor.base.level_params.len() =>
                            {
                                let arity = (constructor.num_params as usize)
                                    .checked_add(constructor.num_fields as usize)
                                    .ok_or_else(|| unsupported("instance constructor arity"))?;
                                if arguments.len() > arity {
                                    return Ok(None);
                                }
                                // Partial constructor applications are inert
                                // functions too. Projection still requires full
                                // saturation. Check parameters as well as fields:
                                // a value parameter is not an erased type argument.
                                push(&mut tasks, Task::Constructor(head, arguments.len()), limit)?;
                                for argument in arguments.into_iter().rev() {
                                    self.tick()?;
                                    push(&mut tasks, Task::Value(argument), limit)?;
                                }
                                continue;
                            }
                            _ => {}
                        }
                    }
                    if !arguments.is_empty() {
                        push(&mut tasks, Task::Application(arguments.len()), limit)?;
                        for argument in arguments.into_iter().rev() {
                            self.tick()?;
                            push(&mut tasks, Task::Value(argument), limit)?;
                        }
                        // Function and arguments are checked before beta can
                        // drop a parameter. A computed unused argument refuses.
                        push(&mut tasks, Task::Value(head), limit)?;
                        continue;
                    }
                    match head.node() {
                        ExprNode::Lam { .. }
                        | ExprNode::ForallE { .. }
                        | ExprNode::Sort { .. }
                        | ExprNode::Lit { .. } => values.push(head),
                        ExprNode::Const { name, levels } => {
                            let Some(definition) = self.definition(name) else {
                                return Ok(None);
                            };
                            if definition.safety != DefinitionSafety::Safe
                                || definition.base.level_params.len() != levels.len()
                            {
                                return Ok(None);
                            }
                            let body = self.universe_instance(
                                &definition.value,
                                &definition.base.level_params,
                                levels,
                            )?;
                            push(&mut tasks, Task::Value(body), limit)?;
                        }
                        ExprNode::LetE { value, body, .. } => {
                            push(&mut tasks, Task::Let(body.clone()), limit)?;
                            push(&mut tasks, Task::Value(value.clone()), limit)?;
                        }
                        _ => return Ok(None),
                    }
                }
                Task::Constructor(mut head, count) => {
                    let start = values
                        .len()
                        .checked_sub(count)
                        .ok_or_else(|| unsupported("instance constructor values"))?;
                    for argument in values.drain(start..) {
                        self.tick()?;
                        head = Expr::app(head, argument);
                    }
                    values.push(head);
                }
                Task::Application(count) => {
                    let start = values
                        .len()
                        .checked_sub(count)
                        .ok_or_else(|| unsupported("instance application values"))?;
                    if start == 0 {
                        return Err(unsupported("instance application function"));
                    }
                    let mut arguments = VecDeque::new();
                    arguments
                        .try_reserve(count)
                        .map_err(|_| IngressError::AllocationFailure {
                            resource: IngressResource::ApplicationArguments,
                            requested: count,
                        })?;
                    for argument in values.drain(start..) {
                        self.tick()?;
                        arguments.push_back(argument);
                    }
                    push(&mut tasks, Task::Continue(arguments), limit)?;
                }
                Task::Continue(mut arguments) => {
                    let Some(argument) = arguments.pop_front() else {
                        continue;
                    };
                    let function = values
                        .pop()
                        .ok_or_else(|| unsupported("instance factory function"))?;
                    if let ExprNode::Lam { body, .. } = function.node() {
                        let body = self.substitution(body, &argument)?;
                        push(&mut tasks, Task::Continue(arguments), limit)?;
                        push(&mut tasks, Task::Value(body), limit)?;
                    } else {
                        let (head, _) = self.spine(&function)?;
                        let ExprNode::Const { name, .. } = head.node() else {
                            return Ok(None);
                        };
                        if !matches!(
                            self.environment.find(name),
                            Some(ConstantInfo::Ctor(_) | ConstantInfo::Induct(_))
                        ) {
                            return Ok(None);
                        }
                        let mut value = Expr::app(function, argument);
                        for argument in arguments {
                            self.tick()?;
                            value = Expr::app(value, argument);
                        }
                        // Reuse the same saturation and operand checks for an
                        // indirectly obtained constructor or type constructor.
                        push(&mut tasks, Task::Value(value), limit)?;
                    }
                }
                Task::Let(body) => {
                    let value = values
                        .pop()
                        .ok_or_else(|| unsupported("instance factory initializer"))?;
                    let body = self.substitution(&body, &value)?;
                    push(&mut tasks, Task::Value(body), limit)?;
                }
            }
        }
        if values.len() != 1 {
            return Err(unsupported("instance factory result"));
        }
        Ok(values.pop())
    }
}

#[cfg(test)]
mod tests;
