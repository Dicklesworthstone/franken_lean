//! Execute general well-founded fixpoints through the admitted equality from
//! `Init.WFComputable`. The source term and both checking seats keep `fix`;
//! only compiler preparation selects `fixC`, whose checked recursive companion
//! follows the ordinary executable-body path. No accessibility proof is run.
//!
//! This is the native bridge for this one library equation, not a general
//! implementation of the imported `csimp` registry. The equation itself must
//! be present, with both constant endpoints and their complete universe/type
//! interfaces checked. A declaration with the theorem's spelling is not enough.
use super::*;

#[cfg(test)]
mod tests;

fn source_name() -> Name {
    name("WellFounded.fix")
}

fn target_name() -> Name {
    name("WellFounded.fixC")
}

fn equation_name() -> Name {
    name("WellFounded.fix_eq_fixC")
}

impl Preparation<'_> {
    /// Called after explicit implementation lookup. A present companion keeps
    /// its ordinary selection path, including refusal on invalid linkage.
    /// It never creates an environment declaration or supplies a proof.
    pub(super) fn well_founded_fix_target(
        &mut self,
        requested: &Name,
    ) -> Result<Option<Name>, IngressError> {
        if requested != &source_name() {
            return Ok(None);
        }
        // A present companion retains the pin's existing selection priority.
        // Even a malformed companion blocks this bridge: ordinary linkage
        // validation must refuse it instead of silently choosing another body.
        if self.has_recursive_companion(requested)? {
            return Ok(None);
        }
        self.tick()?;
        let equation = equation_name();
        let Some(info) = self.environment.find(&equation) else {
            // The imported WF definitions alone do not make the generic
            // fixpoint executable. Retain the ordinary unsupported outcome.
            return Ok(None);
        };
        if !matches!(info, ConstantInfo::Thm(_)) {
            return Err(unsupported(
                "well-founded execution requires an admitted equality theorem",
            ));
        }
        if self
            .runtime_initializers
            .is_some_and(|names| names.contains(requested))
        {
            return Err(unsupported(
                "well-founded fixpoint requires runtime initialization",
            ));
        }
        source_intrinsics::check_selected_extern_attribute(
            self.environment,
            requested,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        if self
            .externs
            .as_ref()
            .is_some_and(|table| table.get(requested).is_some())
        {
            return Ok(None);
        }
        let target = target_name();
        // Attribute chains and this native equation cannot form a second,
        // otherwise invisible cycle across the two selection mechanisms.
        let replacement = self.implementation_target(&target)?;
        if replacement.as_ref() == Some(requested) {
            return Err(unsupported("well-founded executable replacement cycle"));
        }
        if replacement.is_none() {
            // The equality cannot erase the target's runtime authority when
            // no companion remains to check it before body specialization.
            // An explicit target implementation retains ordinary precedence.
            if self
                .runtime_initializers
                .is_some_and(|names| names.contains(&target))
            {
                return Err(unsupported(
                    "well-founded execution target requires runtime initialization",
                ));
            }
            source_intrinsics::check_selected_extern_attribute(
                self.environment,
                &target,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?;
            if self
                .externs
                .as_ref()
                .is_some_and(|table| table.get(&target).is_some())
            {
                return Err(unsupported(
                    "well-founded execution target extern has no supported native implementation",
                ));
            }
        }
        if self.well_founded_fix_checked {
            return Ok(Some(replacement.unwrap_or(target)));
        }
        let ConstantInfo::Thm(theorem) = self.environment.find(&equation).unwrap().clone() else {
            unreachable!("immutable admitted equation");
        };
        let (head, arguments) = self.spine(&theorem.base.type_)?;
        if !matches!(head.node(), ExprNode::Const { name: label, levels }
            if label == &name("Eq") && levels.len() == 1)
            || arguments.len() != 3
        {
            return Err(unsupported(
                "well-founded execution equation is not constant equality",
            ));
        }
        let (
            ExprNode::Const { name: from, levels },
            ExprNode::Const {
                name: to,
                levels: other,
            },
        ) = (arguments[1].node(), arguments[2].node())
        else {
            return Err(unsupported(
                "well-founded execution equation has nonconstant endpoints",
            ));
        };
        if from != requested
            || to != &target
            || levels != other
            || levels.len() != theorem.base.level_params.len()
        {
            return Err(unsupported(
                "well-founded execution equation has different endpoints",
            ));
        }
        let mut parameters = HashSet::new();
        for parameter in &theorem.base.level_params {
            self.tick()?;
            parameters
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: parameters.len().saturating_add(1),
                })?;
            if !parameters.insert(Level::param(parameter.clone())) {
                return Err(unsupported(
                    "well-founded execution equation repeats a universe",
                ));
            }
        }
        for level in levels {
            self.tick()?;
            if !parameters.remove(level) {
                return Err(unsupported(
                    "well-founded execution equation universe mapping",
                ));
            }
        }
        for endpoint in [requested, &target] {
            self.tick()?;
            let Some(ConstantInfo::Defn(definition)) = self.environment.find(endpoint).cloned()
            else {
                return Err(unsupported(
                    "well-founded execution requires safe definition endpoints",
                ));
            };
            if definition.safety != DefinitionSafety::Safe
                || definition.base.level_params.len() != levels.len()
            {
                return Err(unsupported(
                    "well-founded execution endpoint universe or safety",
                ));
            }
            let type_ = self.universe_instance(
                &definition.base.type_,
                &definition.base.level_params,
                levels,
            )?;
            if type_ != arguments[0] {
                return Err(unsupported(
                    "well-founded execution equation interface mismatch",
                ));
            }
        }
        if !source_intrinsics::equality_family_matches(
            self.environment,
            &mut self.visited,
            self.limits,
        )? {
            return Err(unsupported(
                "well-founded execution requires canonical equality",
            ));
        }
        // Cache only after all theorem/interface/metadata checks and metered
        // work succeed. Preparation is bound to one immutable environment.
        self.well_founded_fix_checked = true;
        Ok(Some(replacement.unwrap_or(target)))
    }
}
