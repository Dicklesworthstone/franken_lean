//! A private executable bridge for the pin's selected Array traversal.
//!
//! The Array record still contains its logical List. Under the complete pinned
//! contract, List.forIn' visits exactly those elements in the same order, with
//! one callback bind per element and pure only on exhaustion or `done`. The
//! callback receives the original Array membership proof, not List membership.
//! No unsafe body, native Array ABI, or LawfulMonad equation is used here.
use super::*;

#[derive(Default)]
pub(super) struct Store {
    adapter: Option<Name>,
}

fn logical_name() -> Name {
    Name::from_components(["Array", "forIn'"])
}

fn selected_name() -> Name {
    Name::from_components(["Array", "forIn'Unsafe"])
}

fn private_name() -> Name {
    Name::from_components(["_fln_runtime_array_forIn"])
}

pub(super) fn canonical_pair(source: &Name, selected: &Name) -> bool {
    source == &logical_name() && selected == &selected_name()
}

fn variable(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("Array iteration adapter binder scope"))
}

fn application(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

impl Preparation<'_> {
    /// Called only after the explicit canonical edge has been selected by the
    /// ordinary, metered implementation resolver. Reading that resolver again
    /// here would recurse through initializer checks.
    pub(super) fn array_iteration_target(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        if let Some(adapter) = &self.array_iteration.adapter {
            return Ok(adapter.clone());
        }
        source_intrinsics::array_iteration::matches(
            self.environment,
            self.implementations
                .as_ref()
                .expect("Array implementation edge was already validated"),
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
                    "Array iteration requires its safe logical interface",
                ));
            }
        };

        // Keep the admitted interface, including universe order, dependent
        // domains and binder kinds. The generated declaration remains private.
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
        if binders.len() != 7 {
            return Err(unsupported("Array iteration interface telescope"));
        }
        let parameters = &definition.base.level_params;
        let list_levels = self.array_iteration_levels("List.forIn'", parameters)?;
        let member_levels = self.array_iteration_levels("Array.Mem.mk", parameters)?;
        let list_name = Name::from_components(["List", "forIn'"]);
        let list = self
            .environment
            .find(&list_name)
            .ok_or_else(|| unsupported("Array iteration requires List.forIn'"))?;
        let list_type = self.universe_instance(
            &list.constant_val().type_,
            &list.constant_val().level_params,
            &list_levels,
        )?;

        // Context: α, β, m, Monad m, as, init, f. Projecting field zero keeps
        // the public Array layout intact; its selected extern is model-checked.
        let list_arguments = [
            variable(6)?,
            variable(5)?,
            variable(4)?,
            variable(3)?,
            Expr::proj(Name::from_components(["Array"]), 0, variable(2)?),
            variable(1)?,
        ];
        let mut callback_type = list_type;
        for argument in &list_arguments {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = callback_type.node() else {
                return Err(unsupported("Array iteration List interface telescope"));
            };
            callback_type = self.substitution(body, argument)?;
        }
        let ExprNode::ForallE { binder_type, .. } = callback_type.node() else {
            return Err(unsupported("Array iteration List callback interface"));
        };
        let mut callback_type = binder_type.clone();
        let mut callback_binders = Vec::new();
        for _ in 0..3 {
            self.tick()?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = callback_type.node()
            else {
                return Err(unsupported("Array iteration membership callback telescope"));
            };
            reserve(&mut callback_binders, self.limits.max_context_depth)?;
            callback_binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
            callback_type = body.clone();
        }

        // Under a, List membership, accumulator: α is #9, as is #5, f is #3.
        // Array.Mem.mk takes α, as, a, then the proof of a ∈ as.toList.
        let membership = application(
            Expr::const_(Name::from_components(["Array", "Mem", "mk"]), member_levels),
            [variable(9)?, variable(5)?, variable(2)?, variable(1)?],
        );
        let mut callback = application(variable(3)?, [variable(2)?, membership, variable(0)?]);
        for (binder_name, binder_type, binder_info) in callback_binders.into_iter().rev() {
            self.tick()?;
            callback = Expr::lam(binder_name, binder_type, callback, binder_info);
        }
        let mut value = Expr::app(
            application(Expr::const_(list_name, list_levels), list_arguments),
            callback,
        );
        for (binder_name, binder_type, binder_info) in binders.into_iter().rev() {
            self.tick()?;
            value = Expr::lam(binder_name, binder_type, value, binder_info);
        }
        if value.has_loose_bvars() || value.has_fvar() || value.has_expr_mvar() {
            return Err(unsupported(
                "Array iteration adapter has an open executable body",
            ));
        }
        definition.base.name = private_name();
        definition.value = value;
        definition.hints = ReducibilityHints::Abbrev;
        definition.all.clear();
        let adapter = definition.base.name.clone();
        self.remember_array_iteration_definition(definition)?;
        // Only a fully checked and registered adapter is reusable. A failed
        // model, budget, or collision leaves no partial private callable.
        self.array_iteration.adapter = Some(adapter.clone());
        Ok(adapter)
    }

    /// The pin uses the same named universe variables in these helper
    /// interfaces, but their stored order need not match Array.forIn'.
    fn array_iteration_levels(
        &mut self,
        label: &str,
        parameters: &[Name],
    ) -> Result<Vec<Level>, IngressError> {
        let helper = self
            .environment
            .find(&Name::from_components(label.split('.')))
            .ok_or_else(|| unsupported("Array iteration helper is absent"))?;
        let mut levels = Vec::new();
        for parameter in &helper.constant_val().level_params {
            self.tick()?;
            if !parameters.contains(parameter) {
                return Err(unsupported("Array iteration helper universe interface"));
            }
            reserve(&mut levels, self.limits.max_context_depth)?;
            levels.push(Level::param(parameter.clone()));
        }
        Ok(levels)
    }
}

#[cfg(test)]
mod tests;
