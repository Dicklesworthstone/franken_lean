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
        // A dynamic class receiver still needs its catalog-backed calling
        // interface. A known factory can instead expose its actual method
        // before specialization creates a value-dependent dictionary function.
        let mut type_ = &definition.base.type_;
        for _ in 0..parameters {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = type_.node() else {
                return Ok(None);
            };
            type_ = body;
        }
        let class_receiver = matches!(
            type_.node(),
            ExprNode::ForallE {
                binder_info: BinderInfo::InstImplicit,
                ..
            }
        );
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
        if class_receiver {
            if arguments.len() <= parameters {
                return Ok(None);
            }
            for (index, argument) in arguments[..=parameters].iter().enumerate() {
                self.tick()?;
                if index < parameters && !self.inert_projection_argument(argument)? {
                    return Ok(None);
                }
                let ExprNode::Lam { body: next, .. } = body.node() else {
                    return Err(unsupported("generated class projection telescope"));
                };
                body = self.substitution(next, argument)?;
            }
            let ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } = body.node()
            else {
                return Ok(None);
            };
            let Some(method) = self.known_instance_method(struct_name, *idx, expr)? else {
                return Ok(None);
            };
            return Ok(Some(
                arguments[parameters + 1..]
                    .iter()
                    .cloned()
                    .fold(method, Expr::app),
            ));
        }
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

    /// An already-bound local and a lambda are values even when their syntax
    /// mentions the caller's telescope. Applications that could perform work
    /// still need the existing closed, inert factory check.
    fn inert_projection_argument(&mut self, expression: &Expr) -> Result<bool, IngressError> {
        self.tick()?;
        let (head, arguments) = self.spine(expression)?;
        if arguments.is_empty()
            && matches!(
                head.node(),
                ExprNode::BVar { .. }
                    | ExprNode::Lam { .. }
                    | ExprNode::ForallE { .. }
                    | ExprNode::Sort { .. }
                    | ExprNode::Lit { .. }
            )
        {
            return Ok(true);
        }
        if let ExprNode::Const { name, levels } = head.node()
            && let Some(ConstantInfo::Induct(family)) = self.environment.find(name)
            && !family.is_unsafe
            && family.base.level_params.len() == levels.len()
        {
            // A checked type value does not execute its indices, including
            // an index referring to the surrounding runtime telescope.
            return Ok(true);
        }
        Ok(self.instance_factory_value(expression)?.is_some())
    }

    /// Select a method only through administrative factory reductions. Every
    /// discarded argument and constructor operand must be inert. Strict lets,
    /// computed fields, native allocations and external implementations stay
    /// on their ordinary execution paths; no receiver computation runs here.
    fn known_instance_method(
        &mut self,
        family: &Name,
        index: u64,
        receiver: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        if self.st_ref_record_forbidden(family)?
            || self.array_record_forbidden(family)?
            || self.thunk_record_forbidden(family)?
            || self.task_record_forbidden(family)?
        {
            return Ok(None);
        }
        let mut value = receiver.clone();
        loop {
            self.tick()?;
            let (head, arguments) = self.spine(&value)?;
            match head.node() {
                ExprNode::Const { name, levels } => {
                    self.check_noncomputable_head(&head)?;
                    if self.has_implementation(name)? || self.has_extern_attribute(name)? {
                        return Ok(None);
                    }
                    if let Some(ConstantInfo::Ctor(constructor)) = self.environment.find(name) {
                        if constructor.is_unsafe
                            || constructor.induct != *family
                            || constructor.base.level_params.len() != levels.len()
                            || arguments.len()
                                != constructor.num_params as usize + constructor.num_fields as usize
                        {
                            return Ok(None);
                        }
                        let position = usize::try_from(index)
                            .ok()
                            .filter(|&i| i < constructor.num_fields as usize)
                            .and_then(|i| i.checked_add(constructor.num_params as usize));
                        let Some(method) = position.and_then(|i| arguments.get(i)).cloned() else {
                            return Ok(None);
                        };
                        let (method_head, method_arguments) = self.spine(&method)?;
                        if !method_arguments.is_empty()
                            || !matches!(method_head.node(), ExprNode::Lam { .. })
                        {
                            return Ok(None);
                        }
                        for argument in &arguments {
                            if !self.inert_projection_argument(argument)? {
                                return Ok(None);
                            }
                        }
                        return Ok(Some(method));
                    }
                    let definition = match self.environment.find(name) {
                        Some(ConstantInfo::Defn(definition)) => Some(definition.clone()),
                        _ => self.specialized_definition(name),
                    };
                    let Some(definition) = definition.filter(|definition| {
                        definition.safety == fln_env::constants::DefinitionSafety::Safe
                            && definition.base.level_params.len() == levels.len()
                    }) else {
                        return Ok(None);
                    };
                    value = arguments.into_iter().fold(
                        self.universe_instance(
                            &definition.value,
                            &definition.base.level_params,
                            levels,
                        )?,
                        Expr::app,
                    );
                }
                ExprNode::Lam { body, .. } if !arguments.is_empty() => {
                    if !self.inert_projection_argument(&arguments[0])? {
                        return Ok(None);
                    }
                    value = arguments[1..]
                        .iter()
                        .cloned()
                        .fold(self.substitution(body, &arguments[0])?, Expr::app);
                }
                _ => return Ok(None),
            }
        }
    }

    pub(in crate::runtime) fn original_projection_type(
        &mut self,
        receiver_type: &Expr,
        structure: &Name,
        index: u64,
        receiver: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        // Recover only the admitted family head. Its original value and proof
        // parameters must survive verbatim: normalizing their children here
        // can unfold large runtime computations merely to classify a field.
        // The constructor telescope below supplies the exact dependent type.
        let source = self.type_head(receiver_type)?;
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
