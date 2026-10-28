//! Private executable bridges for the pin's List-backed Array representation.
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
    size: Option<Name>,
    get: Option<Name>,
}

#[derive(Clone, Copy)]
enum Access {
    Size,
    Get,
}

impl Access {
    fn from_name(requested: &Name) -> Option<Self> {
        if requested == &name("Array.size") {
            Some(Self::Size)
        } else if requested == &name("Array.getInternal") {
            Some(Self::Get)
        } else {
            None
        }
    }

    fn private_name(self) -> Name {
        name(match self {
            Self::Size => "_fln_runtime_array_size",
            Self::Get => "_fln_runtime_array_get",
        })
    }
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
    /// Source-only Array records still use the checked List adapters. Once
    /// the native family is authenticated, all production callers preserve
    /// its representation; the explicit logical recognizer remains available
    /// to exercise its independent compatibility contract.
    pub(super) fn legacy_array_access_target(
        &mut self,
        requested: &Name,
    ) -> Result<Option<Name>, IngressError> {
        if Access::from_name(requested).is_none() || self.native_arrays_enabled()? {
            return Ok(None);
        }
        self.native_array_access_target(requested)
    }

    /// The admitted Array is a List wrapper. Authorize explicit representation
    /// templates only after checking the complete logical and selected models.
    /// No constructor is passed to the native Array ABI, and no failed native
    /// contract falls back to a logical body. Index proofs retain the original
    /// telescope and enter List.get through its checked Fin interface.
    pub(super) fn native_array_access_target(
        &mut self,
        requested: &Name,
    ) -> Result<Option<Name>, IngressError> {
        let Some(access) = Access::from_name(requested) else {
            return Ok(None);
        };
        let cached = match access {
            Access::Size => &self.array_iteration.size,
            Access::Get => &self.array_iteration.get,
        };
        if let Some(adapter) = cached {
            let adapter = adapter.clone();
            self.tick()?;
            return Ok(Some(adapter));
        }
        source_intrinsics::read_extern_attributes(
            self.environment,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        if !self
            .externs
            .as_ref()
            .is_some_and(|table| table.get(requested).is_some())
        {
            return Ok(None);
        }
        self.implementations()?;
        let implementations = self
            .implementations
            .as_ref()
            .expect("checked implementation journal");
        match access {
            Access::Size => source_intrinsics::array_iteration::size_matches(
                self.environment,
                implementations,
                self.runtime_initializers,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?,
            Access::Get => source_intrinsics::array_iteration::get_matches(
                self.environment,
                implementations,
                self.runtime_initializers,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?,
        }
        let Some(ConstantInfo::Defn(original)) = self.environment.find(requested) else {
            return Err(unsupported("Array access requires its checked interface"));
        };
        let mut definition = original.clone();
        let mut telescope = definition.base.type_.clone();
        let mut binders = Vec::new();
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = telescope.node()
        {
            self.tick()?;
            reserve(&mut binders, self.limits.max_context_depth)?;
            binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
            telescope = body.clone();
        }
        let (arity, result, helper) = match access {
            Access::Size => (2, Expr::const_(name("Nat"), vec![]), "List.length"),
            Access::Get => (4, variable(3)?, "List.get"),
        };
        if binders.len() != arity || telescope != result {
            return Err(unsupported("Array access interface telescope"));
        }
        // These interfaces each quantify one element universe, but the pin
        // names those parameters differently. Instantiate the helper with the
        // caller's universe and check the actual element-type domain instead
        // of treating a hygienic parameter spelling as a correspondence.
        let list = self
            .environment
            .find(&name(helper))
            .ok_or_else(|| unsupported("Array access requires its checked List helper"))?;
        if definition.base.level_params.len() != 1 || list.constant_val().level_params.len() != 1 {
            return Err(unsupported("Array access helper universe interface"));
        }
        let levels = vec![Level::param(definition.base.level_params[0].clone())];
        let list_type = self.universe_instance(
            &list.constant_val().type_,
            &list.constant_val().level_params,
            &levels,
        )?;
        if !matches!(list_type.node(), ExprNode::ForallE { binder_type, .. }
            if binder_type == &binders[0].1)
        {
            return Err(unsupported("Array access helper element universe"));
        }
        let mut value = match access {
            Access::Size => application(
                Expr::const_(name(helper), levels),
                [variable(1)?, Expr::proj(name("Array"), 0, variable(0)?)],
            ),
            Access::Get => {
                // Context: α, array, index, bound proof. The Fin bound is
                // definitionally the original Array.size by the pinned model;
                // ordinary codegen erases the proof, not the element or index.
                let storage = Expr::proj(name("Array"), 0, variable(2)?);
                let bound = application(
                    Expr::const_(name("List.length"), levels.clone()),
                    [variable(3)?, storage.clone()],
                );
                let index = application(
                    Expr::const_(name("Fin.mk"), vec![]),
                    [bound, variable(1)?, variable(0)?],
                );
                application(
                    Expr::const_(name(helper), levels),
                    [variable(3)?, storage, index],
                )
            }
        };
        for (binder_name, binder_type, binder_info) in binders.into_iter().rev() {
            self.tick()?;
            value = Expr::lam(binder_name, binder_type, value, binder_info);
        }
        definition.base.name = access.private_name();
        definition.value = value;
        definition.hints = ReducibilityHints::Abbrev;
        definition.all.clear();
        let adapter = definition.base.name.clone();
        self.remember_array_definition(definition)?;
        match access {
            Access::Size => self.array_iteration.size = Some(adapter.clone()),
            Access::Get => self.array_iteration.get = Some(adapter.clone()),
        }
        Ok(Some(adapter))
    }

    pub(super) fn array_access_call(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: requested,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if Access::from_name(requested).is_none() {
            return Ok(None);
        }
        if let Some(replacement) = self.implemented_by_call(head, arguments)? {
            return Ok(Some(replacement));
        }
        Ok(self.legacy_array_access_target(requested)?.map(|target| {
            application(
                Expr::const_(target, levels.clone()),
                arguments.iter().cloned(),
            )
        }))
    }

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
        self.remember_array_definition(definition)?;
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
pub(super) mod tests;
