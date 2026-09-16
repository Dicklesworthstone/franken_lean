//! Generalize unresolved universes in the validation copy only. Acceptance of
//! this universal obligation justifies an alias for every future specialization;
//! it neither solves a universe metavariable nor changes the real term store.
use super::{Engine, UnificationError};
use crate::universe::UniverseStore;
use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use std::collections::HashSet;

impl Engine<'_> {
    pub(super) fn generalize_assignment_universes(
        &mut self,
        value: Expr,
        type_: Expr,
    ) -> Result<(Expr, Expr, bool), UnificationError> {
        if !value.has_level_mvar() && !type_.has_level_mvar() {
            return Ok((value, type_, false));
        }
        let left = self.scan(&value)?;
        let right = self.scan(&type_)?;
        let mut reserved: HashSet<_> = left.params.into_iter().chain(right.params).collect();
        let mut generalized = UniverseStore::new();
        let mut ordinal = 0_u64;
        for uvar in left.uvars.into_iter().chain(right.uvars) {
            self.meter.tick()?;
            if generalized.is_assigned(&uvar) {
                continue;
            }
            let name = loop {
                self.meter.tick()?;
                let name = Name::num(Name::from_components(["_fln_residual_universe"]), ordinal);
                ordinal = ordinal
                    .checked_add(1)
                    .ok_or(UnificationError::ExpressionScope)?;
                if reserved.insert(name.clone()) {
                    break name;
                }
            };
            generalized.assign(uvar, Level::param(name));
        }
        let value = generalized
            .instantiate_expr_with_limit(
                &value,
                self.budget
                    .max_visited_nodes
                    .saturating_sub(self.meter.nodes),
            )
            .map_err(UnificationError::Universe)?;
        self.scan(&value)?;
        let type_ = generalized
            .instantiate_expr_with_limit(
                &type_,
                self.budget
                    .max_visited_nodes
                    .saturating_sub(self.meter.nodes),
            )
            .map_err(UnificationError::Universe)?;
        self.scan(&type_)?;
        Ok((value, type_, true))
    }
}
