//! Infer an application's implicit type constructor from its expected result.
//!
//! The ordinary unifier deliberately leaves non-pattern flexible applications
//! suspended. Source application elaboration may additionally try the pin's
//! first-order approximation (ExprDefEq.processAssignmentFOApprox): match
//! arguments from the right, then the remaining function, and when that fails
//! unfold the expected side's head definition once and try again. This is a
//! candidate assignment, not an injectivity rule. Publish it only when the whole
//! original equation checks, and keep every failed attempt's spent work.
use super::*;
use fln_env::constants::ReducibilityHints;

impl Context {
    /// `processAssignmentFOApprox` (vendored `Lean/Meta/ExprDefEq.lean:1172-1212`): an attempt
    /// that fails against `expected` unfolds its head definition once (`unfoldDefinition?`) and
    /// tries again, so `?f ?α` meets `def D := Id Nat` as `Id Nat` and chooses `?f := Id`. Each
    /// attempt is its own trial, and only a complete solution is published.
    pub(in crate::source) fn first_order_result_hint(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut value = expected.clone();
        loop {
            let mut trial = self.clone();
            let result = trial.first_order_result_hint_trial(actual, &value);
            self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
            match result {
                Ok(Some(true)) => {
                    *self = trial;
                    return Ok(true);
                }
                // No applied hole: nothing to approximate, unfolded or not.
                Ok(None) => return Ok(false),
                Ok(Some(false)) => {}
                Err(error) if nonmatch(&error) => {}
                Err(error) => return Err(error),
            }
            let mut probe = self.clone();
            let unfolded = probe.first_order_unfold(&value);
            self.txn.budget.heartbeats_consumed = probe.txn.budget.heartbeats_consumed;
            match unfolded? {
                Some(next) => value = next,
                None => return Ok(false),
            }
        }
    }

    /// The pin's `unfoldDefinition?` (vendored `Lean/Meta/WHNF.lean:871`) at the ambient
    /// transparency, then the loop's `headBeta`: `value` with its head definition unfolded once
    /// and its arguments kept, or `None`. A matcher stays folded, and so does a structural
    /// definition whose arguments reach no smart-unfolding alternative. Metadata also stops the
    /// loop: `unfoldDefinition?` opens only an application or a constant.
    fn first_order_unfold(&mut self, value: &Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
        let value = self.instantiate(value)?;
        let (head, _) = operators::spine(&value);
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        if definition.base.level_params.len() != levels.len()
            || crate::source::equation_theorems::is_matcher_name(name)
        {
            return Ok(None);
        }
        let table = crate::reducibility::table(&self.txn.env).map_err(|error| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(error),
            )))
        })?;
        let abbreviation = definition.hints == ReducibilityHints::Abbrev;
        let permitted = match self.ambient_transparency(UnificationTransparency::Default) {
            UnificationTransparency::None => false,
            UnificationTransparency::Abbreviations => {
                table.get(name).map_or(abbreviation, |status| {
                    status == crate::reducibility::Reducibility::Reducible
                })
            }
            UnificationTransparency::Instances => table.get(name).map_or(
                abbreviation,
                crate::reducibility::Reducibility::unfolds_at_instances,
            ),
            UnificationTransparency::Default | UnificationTransparency::SafeDefinitions => {
                table.status(name) != crate::reducibility::Reducibility::Irreducible
            }
        };
        if !permitted {
            return Ok(None);
        }
        // The `unfold` tactic's stuck-match refusal is that tactic's own; here a folded
        // definition only ends the loop.
        self.unfold_tactic = false;
        let unfolded = self.unfold_selected_definition(&value, &definition)?;
        if unfolded == value {
            return Ok(None);
        }
        self.head_beta(unfolded).map(Some)
    }

    /// Term checking may put the unknown constructor on either side: a
    /// polymorphic result has it on the left, an annotated argument on the
    /// right. Try the pin's first-order choice before either carrier unfolds.
    /// This affects source expected-type propagation, not tactic matching or
    /// the native solver's genuine higher-order pattern rules.
    pub(in crate::source) fn contextual_result_hint(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        if self.flexible_non_pattern(actual)? {
            self.first_order_result_hint(actual, expected)
        } else if self.flexible_non_pattern(expected)? {
            self.first_order_result_hint(expected, actual)
        } else {
            Ok(false)
        }
    }

    /// Whether term elaboration must try first-order approximation. Distinct
    /// locals already in the hole's own context are not pattern variables under
    /// the pin's `setElabConfig` (`quasiPatternApprox := false`): abstracting them
    /// would replace a dependent carrier by a family that changes its parameters.
    /// Genuine pattern arguments are fresh locals outside that context.
    pub(in crate::source) fn flexible_non_pattern(
        &mut self,
        type_: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let type_ = self.instantiate(type_)?;
        let mut head = &type_;
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::MData { expr, .. } => head = expr,
                ExprNode::App { f, a } => {
                    arguments.push(a);
                    head = f;
                }
                _ => break,
            }
        }
        let ExprNode::MVar { id } = head.node() else {
            return Ok(false);
        };
        if arguments.is_empty() || self.txn.mvars.is_assigned(id) {
            return Ok(false);
        }
        let mut locals = std::collections::HashSet::new();
        let Some(declaration) = self.txn.mvars.get_decl(id) else {
            return Ok(false);
        };
        Ok(!arguments.iter().all(|argument| {
            matches!(argument.node(), ExprNode::FVar { id }
                if !declaration.lctx.contains(id) && locals.insert(id.clone()))
        }))
    }

    /// One attempt: `None` when `actual` is no applied hole, else whether it solved the
    /// equation.
    fn first_order_result_hint_trial(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<Option<bool>, NatDefinitionElabError> {
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
            return Ok(None);
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
                return Ok(Some(false));
            };
            if !self.coercion_eq(x, y)? {
                return Ok(Some(false));
            }
            left = a.clone();
            right = b.clone();
        }
        if !self.coercion_eq(&left, &right)? {
            return Ok(Some(false));
        }
        self.coercion_eq(&actual, &expected).map(Some)
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
        let mut whole = self.clone();
        let conversion = whole.coercion_conversion(&actual, &expected);
        self.txn.budget.heartbeats_consumed = whole.txn.budget.heartbeats_consumed;
        match conversion? {
            Conversion::Refuted(_) => return Ok(false),
            // An equation that holds only by choosing an instance is left to synthesis, as the
            // pin postpones instance arguments: decompose it instead.
            Conversion::Equal if !whole.assigned_instance_goal_since(self) => {
                *self = whole;
                return Ok(true);
            }
            Conversion::Equal | Conversion::Deferred => {}
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
        let pairs = std::iter::once((&left_head, &right_head))
            .chain(left_arguments.iter().zip(&right_arguments));
        for (left, right) in pairs {
            self.tick()?;
            let mut pair = self.clone();
            let settled = pair.show_result_hint_trial(left, right, depth + 1);
            self.txn.budget.heartbeats_consumed = pair.txn.budget.heartbeats_consumed;
            if !settled? {
                return Ok(false);
            }
            if !pair.assigned_instance_goal_since(self) {
                *self = pair;
            }
        }
        Ok(true)
    }

    /// Whether this context assigned, since `before`, a hole that instance synthesis owns: an
    /// instance goal, or an `outParam`/`semiOutParam` hole synthesis determines from its inputs.
    fn assigned_instance_goal_since(&self, before: &Context) -> bool {
        if before
            .instance_goals
            .iter()
            .any(|id| !before.txn.mvars.is_assigned(id) && self.txn.mvars.is_assigned(id))
        {
            return true;
        }
        self.txn.mvars.assignments().keys().any(|id| {
            !before.txn.mvars.is_assigned(id)
                && before.txn.mvars.get_decl(id).is_some_and(|decl| {
                    let mut head = &decl.type_;
                    while let ExprNode::App { f, .. } = head.node() {
                        head = f;
                    }
                    matches!(head.node(), ExprNode::Const { name, .. }
                        if *name == Name::from_components(["outParam"])
                            || *name == Name::from_components(["semiOutParam"]))
                })
        })
    }
}

#[cfg(test)]
mod tests;
