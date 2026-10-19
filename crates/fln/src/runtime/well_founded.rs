//! Execute the five constant-replacement equations in `Init.WFComputable`.
//! Both checking seats retain the logical expressions; compiler preparation
//! selects the equal computable definitions and their ordinary companions.
//! Accessibility proofs are never evaluated by this bridge.
//!
//! This is not a general imported `csimp` registry. Each named equation must
//! actually be an admitted equality with the exact constant endpoints and
//! complete universe/type interfaces. Names alone authorize no replacement.
use super::*;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod family_tests;

fn source_name() -> Name {
    name("WellFounded.fix")
}

fn target_name() -> Name {
    name("WellFounded.fixC")
}

fn equation_name() -> Name {
    name("WellFounded.fix_eq_fixC")
}

fn equation_for(requested: &Name) -> Option<(Name, Name)> {
    if requested == &source_name() {
        return Some((target_name(), equation_name()));
    }
    for (source, target, equation) in [
        ("Acc.rec", "Acc.recC", "Acc.rec_eq_recC"),
        ("Acc.ndrec", "Acc.ndrecC", "Acc.ndrec_eq_ndrecC"),
        ("Acc.ndrecOn", "Acc.ndrecOnC", "Acc.ndrecOn_eq_ndrecOnC"),
        ("WellFounded.fixF", "WellFounded.fixFC", "WellFounded.fixF_eq_fixFC"),
    ] {
        if requested == &name(source) {
            return Some((name(target), name(equation)));
        }
    }
    None
}

impl Preparation<'_> {
    /// Explicit implementations and existing companions retain their priority.
    /// Follow mixed equation/attribute chains on a bounded heap worklist so a
    /// cycle across two different well-founded operations cannot hide behind
    /// individually acyclic implemented_by metadata.
    pub(super) fn well_founded_fix_target(
        &mut self,
        requested: &Name,
    ) -> Result<Option<Name>, IngressError> {
        let mut current = requested.clone();
        let mut result = None;
        let mut seen = HashSet::new();
        let mut checked_fix = false;
        while let Some((target, equation)) = equation_for(&current) {
            self.tick()?;
            seen.try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: seen.len().saturating_add(1),
                })?;
            if !seen.insert(current.clone()) {
                return Err(unsupported("well-founded executable replacement cycle"));
            }
            let Some(next) = self.well_founded_equation_target(&current, &target, &equation)?
            else {
                break;
            };
            checked_fix |= current == source_name();
            result = Some(next.clone());
            current = next;
        }
        // The existing cache certifies only fix_eq_fixC, never another entry.
        // A failed mixed chain must not publish a new successful cache state.
        self.well_founded_fix_checked |= checked_fix;
        Ok(result)
    }

    fn well_founded_equation_target(
        &mut self,
        requested: &Name,
        target: &Name,
        equation: &Name,
    ) -> Result<Option<Name>, IngressError> {
        // Even a malformed companion blocks the equation: ordinary linkage
        // validation must refuse it instead of silently choosing another body.
        if self.has_recursive_companion(requested)? {
            return Ok(None);
        }
        self.tick()?;
        let Some(info) = self.environment.find(equation) else {
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
        let replacement = self.implementation_target(target)?;
        if replacement.as_ref() == Some(requested) {
            return Err(unsupported("well-founded executable replacement cycle"));
        }
        if replacement.is_none() {
            if self
                .runtime_initializers
                .is_some_and(|names| names.contains(target))
            {
                return Err(unsupported(
                    "well-founded execution target requires runtime initialization",
                ));
            }
            source_intrinsics::check_selected_extern_attribute(
                self.environment,
                target,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?;
            if self
                .externs
                .as_ref()
                .is_some_and(|table| table.get(target).is_some())
            {
                return Err(unsupported(
                    "well-founded execution target extern has no supported native implementation",
                ));
            }
        }
        if requested == &source_name() && self.well_founded_fix_checked {
            return Ok(Some(replacement.unwrap_or_else(|| target.clone())));
        }
        let ConstantInfo::Thm(theorem) = self.environment.find(equation).unwrap().clone() else {
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
            || to != target
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
        for endpoint in [requested, target] {
            self.tick()?;
            let Some(info) = self.environment.find(endpoint).cloned() else {
                return Err(unsupported(
                    "well-founded execution requires safe definition endpoints",
                ));
            };
            // Acc.rec is the admitted primitive recursor, not a definition.
            // Only this logical source may use Rec; executable targets must
            // remain safe definitions, checked again at companion selection.
            let safe = match &info {
                ConstantInfo::Defn(definition) => definition.safety == DefinitionSafety::Safe,
                ConstantInfo::Rec(recursor) => {
                    endpoint == requested && requested == &name("Acc.rec") && !recursor.is_unsafe
                }
                _ => false,
            };
            let base = info.constant_val();
            if !safe || base.level_params.len() != levels.len() {
                return Err(unsupported(
                    "well-founded execution endpoint universe or safety",
                ));
            }
            let type_ = self.universe_instance(&base.type_, &base.level_params, levels)?;
            if !self.well_founded_interface_matches(&type_, &arguments[0])? {
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
        Ok(Some(replacement.unwrap_or_else(|| target.clone())))
    }

    // Recursor-generated and source-written telescopes may use different
    // binder labels and transparent annotations. Compare their de Bruijn
    // structure without reducing executable definitions or erasing domains.
    fn well_founded_interface_matches(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<bool, IngressError> {
        let mut work = vec![(actual, expected)];
        let mut seen = HashSet::new();
        while let Some((a, b)) = work.pop() {
            self.tick()?;
            if a.allocation_identity() == b.allocation_identity() {
                continue;
            }
            seen.try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: seen.len().saturating_add(1),
                })?;
            if !seen.insert((a.allocation_identity(), b.allocation_identity())) {
                continue;
            }
            reserve(&mut work, self.limits.max_nodes)?;
            match (a.node(), b.node()) {
                (ExprNode::MData { expr, .. }, _) => work.push((expr, b)),
                (_, ExprNode::MData { expr, .. }) => work.push((a, expr)),
                (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
                (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) if a == b => {}
                (
                    ExprNode::Const { name: a, levels: al },
                    ExprNode::Const { name: b, levels: bl },
                ) if a == b && al == bl => {}
                (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                    work.push((aa, ba));
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push((af, bf));
                }
                (
                    ExprNode::ForallE { binder_type: at, body: ab, binder_info: ai, .. },
                    ExprNode::ForallE { binder_type: bt, body: bb, binder_info: bi, .. },
                )
                | (
                    ExprNode::Lam { binder_type: at, body: ab, binder_info: ai, .. },
                    ExprNode::Lam { binder_type: bt, body: bb, binder_info: bi, .. },
                ) if ai == bi => {
                    work.push((ab, bb));
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push((at, bt));
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

}
