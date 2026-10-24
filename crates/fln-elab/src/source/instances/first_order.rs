//! The pin's first-order approximation while selecting an instance candidate.
//!
//! A generic result such as `Inhabited (?m ?a)` does not contain a Miller pattern.
//! `processAssignmentFOApproxAux` (Lean/Meta/ExprDefEq.lean) first compares the
//! rightmost arguments, then the remaining function. This may choose `?a := Nat`
//! and `?m := Id`; it does not assert that an arbitrary function is injective.
//! Every comparison keeps instance-selection transparency, and the whole original
//! selection equation must succeed before any speculative assignment survives.
use super::*;

impl Context {
    pub(super) fn first_order_instance_selection(
        &mut self,
        actual: &Expr,
        expected: &Expr,
        registry: &InstanceRegistry,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut trial = self.clone();
        let result = trial.first_order_instance_selection_trial(actual, expected, registry);
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result {
            Ok(true) => {
                *self = trial;
                Ok(true)
            }
            Ok(false) => Ok(false),
            Err(error) if nonmatch(&error) => Ok(false),
            Err(error) => Err(error),
        }
    }

    fn instance_selection_spine(
        &mut self,
        expression: &Expr,
    ) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = self.instantiate(expression)?;
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                _ => return Ok((head, arguments)),
            }
        }
    }

    fn first_order_instance_selection_trial(
        &mut self,
        actual: &Expr,
        expected: &Expr,
        registry: &InstanceRegistry,
    ) -> Result<bool, NatDefinitionElabError> {
        let (left, arguments) = self.instance_selection_spine(actual)?;
        let (right, expected_arguments) = self.instance_selection_spine(expected)?;
        let (ExprNode::Const { name: class, .. }, ExprNode::Const { name: other, .. }) =
            (left.node(), right.node())
        else {
            return Ok(false);
        };
        if class != other
            || !registry.is_class(class)
            || arguments.len() != expected_arguments.len()
        {
            return Ok(false);
        }
        let mut approximated = false;
        // Class arguments are visited in their declared order. Only an actual
        // flexible application receives the approximation, never a rigid alias.
        for (argument, expected_argument) in arguments.iter().zip(&expected_arguments).rev() {
            self.tick()?;
            if !self.flexible_non_pattern(argument)? {
                continue;
            }
            let (head, suffix) = self.instance_selection_spine(argument)?;
            let (mut other, mut other_suffix) = self.instance_selection_spine(expected_argument)?;
            if suffix.len() > other_suffix.len() {
                return Ok(false);
            }
            // The spine stores the last argument first, exactly the pin's
            // recursive `args.back!` comparison. Each equation is checked by
            // the ordinary transactional solver under Instances transparency.
            for (left, right) in suffix.iter().zip(&other_suffix) {
                self.unify_pending_batch(&[(left.clone(), right.clone())], false, false)?
                    .map_err(|reason| {
                        failure(SourceInferenceError::Unification(Box::new(reason)))
                    })?;
            }
            for argument in other_suffix.drain(suffix.len()..).rev() {
                other = Expr::app(other, argument);
            }
            self.unify_pending_batch(&[(head, other)], false, false)?
                .map_err(|reason| failure(SourceInferenceError::Unification(Box::new(reason))))?;
            approximated = true;
        }
        if !approximated {
            return Ok(false);
        }
        // This includes every original class argument and universe constraint,
        // together with the candidate's suspended equations. An assignment
        // guess never substitutes for selection or final declaration admission.
        self.flush(true)?;
        Ok(true)
    }
}
