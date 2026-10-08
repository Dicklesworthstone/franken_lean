//! Infer an application's implicit type constructor from its expected result.
//!
//! The ordinary unifier deliberately leaves non-pattern flexible applications
//! suspended. Source application elaboration may additionally try the pin's
//! first-order approximation (ExprDefEq.processAssignmentFOApproxAux): match
//! arguments from the right, then the remaining function. This is a candidate
//! assignment, not an injectivity rule. Publish it only when the whole original
//! equation checks, and keep every failed attempt's spent work.
use super::*;

impl Context {
    pub(super) fn first_order_result_hint(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let mut trial = self.clone();
        let result = trial.first_order_result_hint_trial(actual, expected);
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result {
            Ok(true) => {
                *self = trial;
                Ok(())
            }
            Ok(false) => Ok(()),
            Err(error) if nonmatch(&error) => Ok(()),
            Err(error) => Err(error),
        }
    }

    fn first_order_result_hint_trial(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let actual = self.instantiate(actual)?;
        let expected = self.instantiate(expected)?;
        let mut head = &actual;
        let mut arguments = 0usize;
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::MData { expr, .. } => head = expr,
                ExprNode::App { f, .. } => {
                    arguments = arguments
                        .checked_add(1)
                        .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                    head = f;
                }
                _ => break,
            }
        }
        if arguments == 0 || !matches!(head.node(), ExprNode::MVar { .. }) {
            return Ok(false);
        }
        let mut left = actual.clone();
        let mut right = expected.clone();
        for _ in 0..arguments {
            self.tick()?;
            while let ExprNode::MData { expr, .. } = left.node() {
                self.tick()?;
                left = expr.clone();
            }
            while let ExprNode::MData { expr, .. } = right.node() {
                self.tick()?;
                right = expr.clone();
            }
            let (ExprNode::App { f: a, a: x }, ExprNode::App { f: b, a: y }) =
                (left.node(), right.node())
            else {
                return Ok(false);
            };
            if !self.coercion_eq(x, y)? {
                return Ok(false);
            }
            left = a.clone();
            right = b.clone();
        }
        if !self.coercion_eq(&left, &right)? {
            return Ok(false);
        }
        self.coercion_eq(&actual, &expected)
    }
}

#[cfg(test)]
mod tests;
