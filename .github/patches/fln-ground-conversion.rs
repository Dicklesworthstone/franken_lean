//! Closed conversion at the source solver's safe-definition transparency.
//!
//! The pattern solver can determine every implicit argument and still get stuck
//! on a rigid computation (for example the remaining `Nat.add 2 2 = 4` in a
//! term-mode `rfl`). Discarding that batch also discards the inferred arguments.
//! Ask our existing, bounded kernel conversion query before decomposing such a
//! ground equation. This is not a Reference call or declaration admission.
//! Every assignment and the final declaration retain their ordinary checks.
use super::*;

impl Engine<'_> {
    pub(super) fn ground_conversion(
        &mut self,
        left: &Expr,
        right: &Expr,
        locals: &LocalContext,
    ) -> Result<bool, UnificationError> {
        // K1 has its own safe-definition conversion policy, not the elaborator's
        // abbreviation/instance policies. Never use it to widen those policies,
        // or to expose local lets when a caller explicitly disabled zeta-delta.
        if self.budget.transparency != UnificationTransparency::SafeDefinitions
            || !self.budget.zeta_delta
        {
            return Ok(false);
        }
        let mut left = self.instantiate(left)?;
        let mut right = self.instantiate(right)?;
        let closed = |term: &Expr| {
            !term.has_expr_mvar() && !term.has_level_mvar() && !term.has_loose_bvars()
        };
        if !closed(&left) || !closed(&right) {
            return Ok(false);
        }

        // Close the exact local telescope. A let stays a let and a parameter
        // stays a parameter; no witness is invented for an opaque hypothesis.
        // Unresolved local types/values defer rather than becoming assumptions
        // about the values their metavariables might eventually receive.
        let mut seen = HashSet::new();
        for local in locals.decls().iter().rev() {
            self.meter.node()?;
            if !seen.insert(local.id.clone()) {
                return Ok(false);
            }
            let domain = self.instantiate(&local.type_)?;
            let value = local
                .value
                .as_ref()
                .map(|value| self.instantiate(value))
                .transpose()?;
            if !closed(&domain) || value.as_ref().is_some_and(|value| !closed(value)) {
                return Ok(false);
            }
            for term in [&mut left, &mut right] {
                self.scan(term)?;
                let body = term
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| UnificationError::ExpressionScope)?;
                *term = match &value {
                    Some(value) => Expr::let_e(
                        local.user_name.clone(),
                        domain.clone(),
                        value.clone(),
                        body,
                        false,
                    ),
                    None => Expr::lam(
                        local.user_name.clone(),
                        domain.clone(),
                        body,
                        local.binder_info,
                    ),
                };
                self.scan(term)?;
            }
        }
        if !closed(&left) || !closed(&right) {
            return Ok(false);
        }
        let left_facts = self.scan(&left)?;
        let right_facts = self.scan(&right)?;
        if !left_facts.fvars.is_empty() || !right_facts.fvars.is_empty() {
            return Ok(false);
        }
        let mut parameters = left_facts.params;
        for parameter in right_facts.params {
            self.meter.node()?;
            if !parameters.contains(&parameter) {
                parameters.push(parameter);
            }
        }

        // Like assignment and proof-irrelevance validation, each query has the
        // caller's separately calibrated K1 budget. Poll on both sides of this
        // bounded synchronous call; an observed cancellation never commits it.
        self.meter.tick()?;
        self.kernel_checks += 1;
        let outcome = fln_kernel::check_def_eq(
            &self.work.env,
            &parameters,
            &left,
            &right,
            self.budget.kernel,
        );
        self.meter.tick()?;
        match outcome {
            Outcome::Complete(Verdict::Accepted { .. }) => Ok(true),
            Outcome::Complete(Verdict::Rejected { .. }) => Ok(false),
            outcome => Err(UnificationError::ConversionCheck {
                outcome: Box::new(outcome),
            }),
        }
    }
}
