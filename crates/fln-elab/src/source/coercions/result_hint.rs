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

impl Context {
    /// `show T from e` is the pin's `let_fun this : T := e; this` against the expected type
    /// (`Lean/Elab/BuiltinNotation.lean`, `elabShow`): its `isDefEq T expected` assigns what it
    /// can and postpones the instance arguments it cannot decide yet, for synthesis to check.
    /// So `0 + 0 = 0` against `(0 : Int) + 0 = 0` fixes the numerals' type to `Int` before any
    /// default instance is tried. The ordinary unifier defers such an equation whole. Unify two
    /// applications of one constant argument by argument instead, descending into the deferred
    /// ones. A refuted pair is the pin's failed `isDefEq` (a coercion may follow), so nothing
    /// is assigned; what stays undecided is left to the ascription's own check.
    pub(in crate::source) fn show_result_hint(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let mut trial = self.clone();
        let result = trial.show_result_hint_trial(actual, expected, 0);
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

    fn show_result_hint_trial(
        &mut self,
        actual: &Expr,
        expected: &Expr,
        depth: usize,
    ) -> Result<bool, NatDefinitionElabError> {
        const MAX_DEPTH: usize = 32;
        let actual = self.instantiate(actual)?;
        let expected = self.instantiate(expected)?;
        match self.coercion_conversion(&actual, &expected)? {
            Conversion::Equal => return Ok(true),
            Conversion::Refuted(_) => return Ok(false),
            Conversion::Deferred => {}
        }
        if depth >= MAX_DEPTH {
            return Ok(true);
        }
        let spine = |term: &Expr| {
            let mut head = term.clone();
            let mut arguments = Vec::new();
            loop {
                match head.node() {
                    ExprNode::MData { expr, .. } => head = expr.clone(),
                    ExprNode::App { f, a } => {
                        arguments.push(a.clone());
                        head = f.clone();
                    }
                    _ => break,
                }
            }
            arguments.reverse();
            (head, arguments)
        };
        let (left_head, left_arguments) = spine(&actual);
        let (right_head, right_arguments) = spine(&expected);
        let same_head = matches!(
            (left_head.node(), right_head.node()),
            (ExprNode::Const { name: left, .. }, ExprNode::Const { name: right, .. }) if left == right
        );
        if !same_head || left_arguments.len() != right_arguments.len() {
            return Ok(true);
        }
        if let Conversion::Refuted(_) = self.coercion_conversion(&left_head, &right_head)? {
            return Ok(false);
        }
        for (left, right) in left_arguments.iter().zip(&right_arguments) {
            self.tick()?;
            if !self.show_result_hint_trial(left, right, depth + 1)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests;
