//! A private executable bridge for the pin's selected bounded Array fold.
//!
//! The logical Array record contains a List. Extracting [start, stop) clamps
//! to that list and folding it preserves the pin's callback order, one bind
//! per visited element, and pure only at exhaustion. This uses no Monad laws,
//! unsafe body, or native Array representation.
use super::*;

#[derive(Default)]
pub(super) struct Store {
    adapter: Option<Name>,
}

fn logical_name() -> Name {
    Name::from_components(["Array", "foldlM"])
}

fn selected_name() -> Name {
    Name::from_components(["Array", "foldlMUnsafe"])
}

fn private_name() -> Name {
    Name::from_components(["_fln_runtime_array_foldlM"])
}

pub(super) fn canonical_pair(source: &Name, selected: &Name) -> bool {
    source == &logical_name() && selected == &selected_name()
}

fn variable(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("Array fold adapter binder scope"))
}

fn application(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

impl Preparation<'_> {
    /// Called only after the ordinary implementation resolver selected the
    /// exact explicit edge. The complete model also binds helper selections.
    pub(super) fn array_fold_target(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        if let Some(adapter) = &self.array_fold.adapter {
            return Ok(adapter.clone());
        }
        source_intrinsics::array_fold::matches(
            self.environment,
            self.implementations
                .as_ref()
                .expect("Array fold implementation edge was already validated"),
            self.runtime_initializers,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        let mut definition = match self.environment.find(&logical_name()) {
            Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Safe => {
                value.clone()
            }
            _ => {
                return Err(unsupported(
                    "Array fold requires its safe logical interface",
                ));
            }
        };

        // Keep the admitted interface and its binder kinds. The executable
        // template is private and never replaces the logical declaration.
        let mut telescope = definition.base.type_.clone();
        let mut binders = Vec::new();
        loop {
            self.tick()?;
            match telescope.node() {
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    reserve(&mut binders, self.limits.max_context_depth)?;
                    binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
                    telescope = body.clone();
                }
                ExprNode::MData { expr, .. } => telescope = expr.clone(),
                _ => break,
            }
        }
        if binders.len() != 9 {
            return Err(unsupported("Array fold interface telescope"));
        }

        // List.foldlM names the accumulator universe u, result universe v,
        // and element universe w. Array.foldlM uses v, w, and u respectively.
        // Respect each admitted constant's stored universe order.
        let parameters = &definition.base.level_params;
        let fold_levels = self.array_fold_levels(
            "List.foldlM",
            parameters,
            &[("u", "v"), ("v", "w"), ("w", "u")],
        )?;
        let extract_levels =
            self.array_fold_levels("List.extract", parameters, &[("u", "u")])?;

        // Context: α, β, m, Monad m, f, init, as, start, stop.
        // List.extract is drop(start).take(stop - start), so no Array-size
        // arithmetic or callbacks are needed to construct the selected slice.
        let slice = application(
            Expr::const_(Name::from_components(["List", "extract"]), extract_levels),
            [
                variable(8)?,
                Expr::proj(Name::from_components(["Array"]), 0, variable(2)?),
                variable(1)?,
                variable(0)?,
            ],
        );
        // List.foldlM takes m, Monad m, accumulator type, element type,
        // callback, initial accumulator, and the selected list.
        let mut value = application(
            Expr::const_(Name::from_components(["List", "foldlM"]), fold_levels),
            [
                variable(6)?,
                variable(5)?,
                variable(7)?,
                variable(8)?,
                variable(4)?,
                variable(3)?,
                slice,
            ],
        );
        for (binder_name, binder_type, binder_info) in binders.into_iter().rev() {
            self.tick()?;
            value = Expr::lam(binder_name, binder_type, value, binder_info);
        }
        if value.has_loose_bvars() || value.has_fvar() || value.has_expr_mvar() {
            return Err(unsupported(
                "Array fold adapter has an open executable body",
            ));
        }
        definition.base.name = private_name();
        definition.value = value;
        definition.hints = ReducibilityHints::Abbrev;
        definition.all.clear();
        let adapter = definition.base.name.clone();
        self.remember_array_fold_definition(definition)?;
        // Only successful model validation and complete private registration
        // earn a cache entry. Every refusal leaves this slot empty.
        self.array_fold.adapter = Some(adapter.clone());
        Ok(adapter)
    }

    fn array_fold_levels(
        &mut self,
        label: &str,
        parameters: &[Name],
        mapping: &[(&str, &str)],
    ) -> Result<Vec<Level>, IngressError> {
        let helper = self
            .environment
            .find(&Name::from_components(label.split('.')))
            .ok_or_else(|| unsupported("Array fold helper is absent"))?;
        if helper.constant_val().level_params.len() != mapping.len() {
            return Err(unsupported("Array fold helper universe arity"));
        }
        let mut levels = Vec::new();
        for parameter in &helper.constant_val().level_params {
            self.tick()?;
            let mapped = mapping
                .iter()
                .find_map(|(source, target)| {
                    (parameter == &Name::from_components([*source]))
                        .then(|| Name::from_components([*target]))
                })
                .ok_or_else(|| unsupported("Array fold helper universe interface"))?;
            if !parameters.contains(&mapped) {
                return Err(unsupported("Array fold source universe interface"));
            }
            reserve(&mut levels, self.limits.max_context_depth)?;
            levels.push(Level::param(mapped));
        }
        Ok(levels)
    }
}

#[cfg(test)]
mod tests;
