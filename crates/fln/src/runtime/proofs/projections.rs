//! Recover the original field type, not its erased runtime representation.
//! Dependent proof predicates use syntactic projections of the original receiver;
//! no receiver is evaluated here. Classification must precede representation.
use super::*;

impl Preparation<'_> {
    /// The pin inlines generated projection functions before visiting operands
    /// (ToLCNF.visitProjFn). Only their datatype parameters disappear: the
    /// receiver occurs once, and an overapplied callable field keeps every arg.
    /// Partial application retains the remaining typed lambda telescope.
    pub(in crate::runtime) fn inline_generated_projection(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let environment = self.environment;
        let Some(ConstantInfo::Defn(definition)) = environment.find(name) else {
            return Ok(None);
        };
        if arguments.is_empty() || definition.base.level_params.len() != levels.len() {
            return Ok(None);
        }
        let Some(parameters) =
            fln_elab::records::generated_projection_parameters(environment, definition, || {
                self.tick()
            })?
        else {
            return Ok(None);
        };
        if parameters == 0 || self.has_implementation(name)? {
            return Ok(None);
        }
        // A class projection (`Pure.pure`, `Bind.bind`, `OfScientific.ofScientific`) takes
        // its structure as an instance-implicit argument, and stays an application, as it was
        // before this inlining. Inlined, it left `inst.1` for ingress, which lowers a class
        // method through the application and not through the instance's field:
        // `def main : IO Unit := pure ()` was refused (`structure projection `Pure` field 0
        // … is absent`), and `(1.5 : Float)` reached `Float.ofScientific` as an unknown
        // constant. The pin's `ToLCNF.visitProjFn` inlines these too; this runtime does not
        // lower the result yet.
        let mut type_ = &definition.base.type_;
        for _ in 0..parameters {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return Ok(None);
            };
            type_ = body;
        }
        if matches!(
            type_.node(),
            ExprNode::ForallE {
                binder_info: BinderInfo::InstImplicit,
                ..
            }
        ) {
            return Ok(None);
        }
        // An explicit extern owns the executable semantics, even for a
        // generated field. Do not turn its logical body into a fallback.
        source_intrinsics::check_selected_extern_attribute(
            environment,
            name,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        if self
            .externs
            .as_ref()
            .is_some_and(|table| table.get(name).is_some())
        {
            return Ok(None);
        }
        let mut body =
            self.universe_instance(&definition.value, &definition.base.level_params, levels)?;
        for (index, argument) in arguments.iter().enumerate() {
            self.tick()?;
            if index <= parameters {
                let ExprNode::Lam { body: next, .. } = body.node() else {
                    return Err(unsupported("generated projection telescope"));
                };
                body = self.substitution(next, argument)?;
            } else {
                body = Expr::app(body, argument.clone());
            }
        }
        Ok(Some(body))
    }

    pub(in crate::runtime) fn original_projection_type(
        &mut self,
        receiver_type: &Expr,
        structure: &Name,
        index: u64,
        receiver: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        let source = self.normalize_type(receiver_type)?;
        let (head, parameters) = self.spine(&source)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(family)) = self.environment.find(name) else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.is_rec
            || family.num_indices != 0
            || family.ctors.len() != 1
            || family.num_params as usize != parameters.len()
            || family.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        // A second preparation pass may see a private projection key, but it
        // must be bound to this exact previously discovered source family.
        // Layouts are keyed by the runtime type, in which value parameters
        // are erased; the original parameters are still used below.
        if name != structure {
            let key = self.erase_data_indices(&source)?;
            if self.data_shapes.get(&key).map(|shape| &shape.name) != Some(structure) {
                return Err(unsupported("projection receiver family mismatch"));
            }
        }
        let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(&family.ctors[0]) else {
            return Ok(None);
        };
        if ctor.is_unsafe
            || ctor.induct != *name
            || ctor.num_params != family.num_params
            || ctor.base.level_params != family.base.level_params
        {
            return Ok(None);
        }
        if index >= u64::from(ctor.num_fields) {
            return Err(unsupported(
                "projection field outside constructor telescope",
            ));
        }
        let mut type_ =
            self.universe_instance(&ctor.base.type_, &ctor.base.level_params, levels)?;
        for parameter in &parameters {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE { body, .. } = normal.node() else {
                return Ok(None);
            };
            type_ = self.substitution(body, parameter)?;
        }
        for field in 0..=index {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            if field == index {
                return Ok(Some(binder_type.clone()));
            }
            let projection = Expr::proj(name.clone(), field, receiver.clone());
            type_ = self.substitution(body, &projection)?;
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests;
