//! Source-level universe substitution uses the same metered DAG traversal as
//! native unifier delta reduction, without assigning caller universe parameters.
mod generalization;

use super::{Context, SourceInferenceError, failure};
use crate::NatDefinitionElabError;
use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;

impl Context {
    pub(super) fn instantiate_params(
        &mut self,
        expr: &Expr,
        params: &[Name],
        levels: &[Level],
    ) -> Result<Expr, NatDefinitionElabError> {
        crate::universe::parameters::instantiate(
            || self.tick(),
            || failure(SourceInferenceError::Scope),
            expr,
            params,
            levels,
        )
    }
}
