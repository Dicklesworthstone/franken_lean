//! The pin's `isDefEqUnitLike` (Lean/Meta/ExprDefEq.lean): neutral values
//! of the same nonrecursive, zero-field structure compare by their types.
//! Constructor eta alone cannot compare two distinct neutral inhabitants.
//!
//! The metadata and type hints select the rung, but are not typing evidence.
//! A shared K1 guard checks BOTH original inhabitants before either disappears.
//! It never creates an inhabitant, solves an opaque hole, or publishes a decl.
use super::*;

impl Engine<'_> {
    pub(super) fn unit_like_eta(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
        pending: &mut VecDeque<Equation>,
    ) -> Result<bool, UnificationError> {
        let Some(left_type) = self.eta_neutral_type(left, locals)? else {
            return Ok(false);
        };
        let left_type = self.whnf(&left_type, locals)?;
        let (head, parameters) = self.eta_spine(&left_type)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(false);
        };
        let Some(shape) = self.eta_shape(name)? else {
            return Ok(false);
        };
        if shape.fields != 0
            || parameters.len() != shape.parameters
            || levels.len() != shape.level_params.len()
        {
            return Ok(false);
        }
        let family = self.eta_specialize(&shape.family_type, &shape.level_params, levels)?;
        let Some(sort) = self.eta_apply_type(family, &parameters, locals)? else {
            return Ok(false);
        };
        let ExprNode::Sort { level } = sort.node() else {
            return Ok(false);
        };
        // Do not trust a field-count tag detached from its constructor type.
        let constructor =
            self.eta_specialize(&shape.constructor_type, &shape.level_params, levels)?;
        let Some(result) = self.eta_apply_type(constructor, &parameters, locals)? else {
            return Ok(false);
        };
        if !same_terms(&result, &left_type, &mut self.meter)? {
            return Ok(false);
        }
        let Some(right_type) = self.eta_neutral_type(right, locals)? else {
            return Ok(false);
        };
        let same_type = same_terms(&left_type, &right_type, &mut self.meter)?;
        if !same_type
            && (left_type.has_expr_mvar()
                || left_type.has_level_mvar()
                || right_type.has_expr_mvar()
                || right_type.has_level_mvar())
        {
            // Type hints produce an ordinary equation, never an equality
            // verdict. Keep the original pair on the outer worklist, so it
            // returns through the K1 guard after assignments make progress.
            // An unchanged generation reaches the normal deferred fixed point.
            pending.push_front((left_type, right_type, locals.clone()));
            return Err(UnificationError::Deferred(
                UnificationDeferred::UnsupportedEquation,
            ));
        }
        // Even after useful type inference, erasing the original arguments
        // must not erase an unresolved term, instance, or universe obligation.
        // The whole transaction rolls back if those cannot be resolved.
        if left.has_expr_mvar()
            || right.has_expr_mvar()
            || left.has_level_mvar()
            || right.has_level_mvar()
        {
            return Ok(false);
        }
        if [&left_type, &right_type, &sort]
            .iter()
            .any(|term| term.has_expr_mvar() || term.has_level_mvar() || term.has_loose_bvars())
        {
            return Ok(false);
        }
        if !self.check_typed_pair(
            left_type.clone(),
            level.clone(),
            left.clone(),
            right.clone(),
            locals,
        )? {
            return Ok(false);
        }
        if !same_type {
            // K1 validates typing, but its delta is broader than the caller's.
            // Parameter and universe conversion still use the original policy.
            pending.push_front((left_type, right_type, locals.clone()));
        }
        Ok(true)
    }
}
