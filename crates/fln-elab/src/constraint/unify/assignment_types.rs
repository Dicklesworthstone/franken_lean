//! Type constraints produced by native pattern assignment (plan §10.2).
//!
//! A term equation can determine its missing type as well as its value. These
//! are ordinary worklist equations, not typing judgments: every assigned value
//! and every inferred type still passes the parent's K1 validation barrier.
//! Neutral synthesis deliberately leaves argument checking to that barrier.
use super::*;

impl Engine<'_> {
    pub(super) fn assignment_type_equation(
        &mut self,
        expected: &Expr,
        value: &Expr,
        locals: &LocalContext,
    ) -> Result<Option<Equation>, UnificationError> {
        let expected = self.instantiate(expected)?;
        if !expected.has_expr_mvar() && !expected.has_level_mvar() {
            // Preserve the existing K1 verdict for a closed ill-typed value.
            // Do not make every ordinary assignment pay for type synthesis.
            return Ok(None);
        }
        let value = self.instantiate(value)?;
        let inferred = match value.node() {
            ExprNode::Sort { level } => Some(Expr::sort(
                Level::succ(level.clone()).map_err(|_| UnificationError::ExpressionScope)?,
            )),
            ExprNode::Lit {
                literal: Literal::Nat(_),
            } => Some(Expr::const_(Name::from_components(["Nat"]), Vec::new())),
            _ => match self.eta_neutral_type(&value, locals) {
                // An unavailable approximation is not a failed typing judgment.
                // Final assignment checking will retain unresolved obligations.
                Err(UnificationError::Deferred(_)) => None,
                result => result?,
            },
        };
        let Some(inferred) = inferred else {
            return Ok(None);
        };
        self.scan(&inferred)?;
        if same_terms(&expected, &inferred, &mut self.meter)? {
            return Ok(None);
        }
        for _ in locals.decls() {
            self.meter.node()?;
        }
        Ok(Some((expected, inferred, locals.clone())))
    }
}
