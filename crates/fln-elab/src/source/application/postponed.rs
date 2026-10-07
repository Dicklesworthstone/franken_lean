//! The pin postpones a callee whose type is still a metavariable application
//! (`Elab/App.lean`, `elabAppArgs` / `tryPostponeIfMVar`). The containing
//! argument is retried on the ordinary term worklist after later arguments
//! constrain its expected type. No function shape or coercion is guessed.
//!
//! Rolling back the whole argument avoids keeping its newly opened lambda
//! locals in a hole that the surrounding lambda has already closed. Pending
//! arguments only resume in their original lexical context. A scope cannot
//! close over unresolved work, and failed resumed work remains a declaration
//! diagnostic unless its owning transaction is rolled back.
use super::*;

#[derive(Clone)]
pub(in crate::source) struct Argument<'a> {
    pub syntax: &'a Syntax,
    pub expected: Expr,
    waiting: Expr,
    blocker: MVarId,
    lctx: LocalContext,
    hole: Expr,
}

#[derive(Clone, Default)]
pub(in crate::source) struct Queue<'a> {
    arguments: Vec<Argument<'a>>,
}

impl<'a> Queue<'a> {
    pub fn has_current_scope(&self, context: &mut Context) -> Result<bool, NatDefinitionElabError> {
        for argument in &self.arguments {
            context.tick()?;
            if argument.lctx == context.txn.lctx {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub fn take_ready(
        &mut self,
        context: &mut Context,
    ) -> Result<Option<Argument<'a>>, NatDefinitionElabError> {
        for index in 0..self.arguments.len() {
            context.tick()?;
            let argument = &self.arguments[index];
            if argument.lctx == context.txn.lctx
                && context.instantiate(&argument.expected)? != argument.waiting
            {
                return Ok(Some(self.arguments.remove(index)));
            }
        }
        Ok(None)
    }

    pub fn scope_blockers(
        &self,
        context: &mut Context,
    ) -> Result<Vec<MVarId>, NatDefinitionElabError> {
        let mut blockers = Vec::new();
        for argument in &self.arguments {
            context.tick()?;
            if argument.lctx == context.txn.lctx
                && let Some(blocker) =
                    context.application_type_unavailable(&Expr::mvar(argument.blocker.clone()))?
            {
                blockers.push(blocker);
            }
        }
        Ok(blockers)
    }

    pub fn close_scope(&mut self, context: &mut Context) -> Result<(), NatDefinitionElabError> {
        let mut index = 0;
        while index < self.arguments.len() {
            context.tick()?;
            if self.arguments[index].lctx == context.txn.lctx {
                self.arguments.remove(index);
                context
                    .postponed_application_errors
                    .push(failure(SourceInferenceError::ExpectedFunction));
            } else {
                index += 1;
            }
        }
        Ok(())
    }

    pub fn finish(&mut self, context: &mut Context) -> Result<(), NatDefinitionElabError> {
        while self.arguments.pop().is_some() {
            context.tick()?;
            context
                .postponed_application_errors
                .push(failure(SourceInferenceError::ExpectedFunction));
        }
        Ok(())
    }
}

pub(in crate::source) struct Checkpoint<'a> {
    context: Box<Context>,
    queue: Queue<'a>,
    pub syntax: &'a Syntax,
    pub expected: Expr,
    pub hole: Option<Expr>,
    pub tasks: usize,
    pub values: usize,
}

impl<'a> Checkpoint<'a> {
    pub fn argument(
        context: &mut Context,
        queue: &Queue<'a>,
        syntax: &'a Syntax,
        expected: Expr,
        tasks: usize,
        values: usize,
    ) -> Result<Option<Self>, NatDefinitionElabError> {
        let expected = context.instantiate(&expected)?;
        if !expected.has_expr_mvar() {
            return Ok(None);
        }
        Ok(Some(Self {
            context: Box::new(context.clone()),
            queue: queue.clone(),
            syntax,
            expected,
            hole: None,
            tasks,
            values,
        }))
    }

    pub fn resume(
        context: &Context,
        queue: &Queue<'a>,
        argument: Argument<'a>,
        tasks: usize,
        values: usize,
    ) -> Self {
        Self {
            context: Box::new(context.clone()),
            queue: queue.clone(),
            syntax: argument.syntax,
            expected: argument.expected,
            hole: Some(argument.hole),
            tasks,
            values,
        }
    }

    pub fn restore(&self, context: &mut Context, queue: &mut Queue<'a>) {
        let spent = context.txn.budget.heartbeats_consumed;
        *context = (*self.context).clone();
        context.txn.budget.heartbeats_consumed = spent;
        *queue = self.queue.clone();
    }

    /// Move a suspended nested argument outward only by replaying an entire
    /// containing argument. Its snapshot must precede the closing lexical
    /// scope, and its expected type must own the unresolved dependency.
    /// Current assignments may alias a saved ?A to an inner ?B. Return the
    /// saved owner ?A, never an inner identity that rollback would discard.
    pub fn outer_blocker(
        &self,
        context: &mut Context,
        blockers: &[MVarId],
    ) -> Result<Option<MVarId>, NatDefinitionElabError> {
        let saved = &self.context.txn.lctx;
        if saved.len() >= context.txn.lctx.len() {
            return Ok(None);
        }
        for index in 0..saved.len() {
            context.tick()?;
            if saved.decls()[index] != context.txn.lctx.decls()[index] {
                return Ok(None);
            }
        }
        context.tick()?;
        let expected = self
            .context
            .txn
            .instantiate_expr(&self.expected)
            .map_err(|error| failure(SourceInferenceError::Universe(error)))?;
        let mut owners: Vec<_> = self
            .context
            .txn
            .mvars
            .collect_mvars(&expected)
            .into_iter()
            .collect();
        owners.sort_by(|left, right| left.0.cmp(&right.0));
        for owner in owners {
            let current = context.instantiate(&Expr::mvar(owner.clone()))?;
            let dependencies = context.txn.mvars.collect_mvars(&current);
            for blocker in blockers {
                context.tick()?;
                if dependencies.contains(blocker) {
                    return Ok(Some(owner));
                }
            }
        }
        Ok(None)
    }

    pub fn postpone(
        &self,
        context: &mut Context,
        queue: &mut Queue<'a>,
        blocker: &MVarId,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let expected = context.instantiate(&self.expected)?;
        // An unrelated inner argument's result hole cannot unblock this
        // callee. Continue unwinding to the argument whose expected type
        // actually owns the unavailable carrier.
        if !context.txn.mvars.collect_mvars(&expected).contains(blocker) {
            return Ok(None);
        }
        let hole = match &self.hole {
            Some(hole) => hole.clone(),
            None => context.hole(expected.clone())?,
        };
        queue.arguments.push(Argument {
            syntax: self.syntax,
            expected: expected.clone(),
            waiting: expected.clone(),
            blocker: blocker.clone(),
            lctx: context.txn.lctx.clone(),
            hole: hole.clone(),
        });
        Ok(Some(Typed {
            value: hole,
            type_: expected,
        }))
    }
}

impl Context {
    pub(in crate::source) fn application_type_unavailable(
        &mut self,
        type_: &Expr,
    ) -> Result<Option<MVarId>, NatDefinitionElabError> {
        let mut head = self.whnf(type_)?;
        while let ExprNode::App { f, .. } = head.node() {
            self.tick()?;
            head = f.clone();
        }
        Ok(match head.node() {
            ExprNode::MVar { id } => Some(id.clone()),
            _ => None,
        })
    }
}
