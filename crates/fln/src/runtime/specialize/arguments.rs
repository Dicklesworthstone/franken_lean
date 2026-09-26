//! Specialize static arguments at their actual positions in a lambda telescope.
//!
//! Retained values are parameters, not constants to substitute or cache. Static
//! selection never crosses a strict let or a computed function-return stage.
//! The generated declarations are private compiler inputs, not logical facts.
use super::*;

mod factories;

pub(super) type InstanceKey = (Name, Vec<Level>, Vec<(usize, Expr)>);

struct RetainedBinder {
    type_name: Name,
    type_domain: Expr,
    type_info: BinderInfo,
    value_name: Name,
    value_domain: Expr,
    value_info: BinderInfo,
}

struct PreparedArguments {
    type_: Expr,
    value: Expr,
    static_arguments: Vec<(usize, Expr)>,
    runtime_arguments: Vec<Expr>,
}

impl Preparation<'_> {
    fn specialize_arguments(
        &mut self,
        initial_type: Expr,
        initial_value: Expr,
        args: &[Expr],
    ) -> Result<PreparedArguments, IngressError> {
        if args.len() > self.limits.max_application_args {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ApplicationArguments,
                limit: self.limits.max_application_args,
                observed: args.len(),
            });
        }
        let mut type_ = initial_type.clone();
        let mut value = initial_value.clone();
        let mut retained = Vec::new();
        let mut static_arguments = Vec::new();
        let mut last_static = None;
        for (index, argument) in args.iter().enumerate() {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = normal.node()
            else {
                break;
            };
            // This exposes only already inert aliases, never an initializer or
            // a call which computes a callback. The actual lambda must exist.
            value = self.static_head(&value)?;
            let ExprNode::Lam {
                binder_name: value_name,
                binder_type: value_domain,
                body: value_body,
                binder_info: value_info,
            } = value.node()
            else {
                break;
            };
            // A dictionary indexed by an earlier retained value is not a
            // global specialization, even when this caller supplies a literal.
            // Closed static arguments with independent domains need no lift
            // when substituted under the retained runtime binders.
            let selected = if binder_type.has_loose_bvars() || !closed(argument) {
                None
            } else if self.type_parameter(binder_type)? {
                Some(argument.clone())
            } else if *binder_info == BinderInfo::InstImplicit {
                self.instance_factory_value(argument)?
            } else {
                None
            };
            if let Some(selected) = selected {
                let next_type = self.substitution(body, &selected)?;
                let next_value = self.substitution(value_body, &selected)?;
                reserve(&mut static_arguments, self.limits.max_application_args)?;
                // Keep the exact source argument in the key; only the private
                // compiler body receives the proven-inert factory result.
                static_arguments.push((index, argument.clone()));
                type_ = next_type;
                value = next_value;
                // Trailing runtime arguments must not change the cached body.
                // Remember the exact boundary after the last erased argument;
                // a partial and a saturated use then share one specialization.
                last_static = Some((type_.clone(), value.clone(), retained.len()));
            } else {
                reserve(&mut retained, self.limits.max_context_depth)?;
                retained.push(RetainedBinder {
                    type_name: binder_name.clone(),
                    type_domain: binder_type.clone(),
                    type_info: *binder_info,
                    value_name: value_name.clone(),
                    value_domain: value_domain.clone(),
                    value_info: *value_info,
                });
                type_ = body.clone();
                value = value_body.clone();
            }
        }
        let (type_, value) = if let Some((mut type_, mut value, count)) = last_static {
            retained.truncate(count);
            for binder in retained.into_iter().rev() {
                self.tick()?;
                type_ = Expr::forall_e(
                    binder.type_name,
                    binder.type_domain,
                    type_,
                    binder.type_info,
                );
                value = Expr::lam(
                    binder.value_name,
                    binder.value_domain,
                    value,
                    binder.value_info,
                );
            }
            (type_, value)
        } else {
            (initial_type, initial_value)
        };
        let mut runtime_arguments = Vec::new();
        let mut selected = static_arguments.iter().peekable();
        for (index, argument) in args.iter().enumerate() {
            self.tick()?;
            if selected
                .peek()
                .is_some_and(|(position, _)| *position == index)
            {
                selected.next();
            } else {
                reserve(&mut runtime_arguments, self.limits.max_application_args)?;
                runtime_arguments.push(argument.clone());
            }
        }
        Ok(PreparedArguments {
            type_,
            value,
            static_arguments,
            runtime_arguments,
        })
    }

    /// Erase closed type and inert dictionary arguments without requiring them
    /// to precede every runtime parameter. Argument positions are part of the
    /// cache identity; ordinary argument values never are.
    pub(in crate::runtime) fn specialize_call(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: original,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if self.specializations.definitions.contains_key(original) {
            return Ok(None);
        }
        let Some(mut definition) = self.definition(original) else {
            return Ok(None);
        };
        if definition.base.level_params.len() != levels.len()
            || levels.iter().any(|l| l.has_mvar() || l.has_param())
        {
            return Ok(None);
        }
        let type_ = self.universe_instance(
            &definition.base.type_,
            &definition.base.level_params,
            levels,
        )?;
        let value =
            self.universe_instance(&definition.value, &definition.base.level_params, levels)?;
        let prepared = self.specialize_arguments(type_, value, args)?;
        if prepared.static_arguments.is_empty() && levels.is_empty() {
            return Ok(None);
        }
        let key = (original.clone(), levels.clone(), prepared.static_arguments);
        let name = if let Some(name) = self.specializations.instances.get(&key) {
            name.clone()
        } else {
            let count = self.specializations.definitions.len();
            if count >= self.limits.fir.max_functions {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::ProgramTables,
                    limit: self.limits.fir.max_functions,
                    observed: count.saturating_add(1),
                });
            }
            let serial =
                u64::try_from(count).map_err(|_| unsupported("specialization identity"))?;
            let name = Name::num(
                Name::from_components(["_fln_runtime_specialization"]),
                serial,
            );
            if self.environment.contains(&name) {
                return Err(unsupported("runtime specialization name collision"));
            }
            definition.base.name = name.clone();
            definition.base.level_params.clear();
            definition.base.type_ = prepared.type_;
            definition.value = prepared.value;
            definition.all.clear();
            self.specializations.instances.try_reserve(1).map_err(|_| {
                IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: count.saturating_add(1),
                }
            })?;
            self.specializations.instances.insert(key, name.clone());
            self.specializations
                .definitions
                .insert(name.clone(), definition);
            name
        };
        Ok(Some(application(
            Expr::const_(name, vec![]),
            prepared.runtime_arguments,
        )))
    }
}

#[cfg(test)]
mod tests;
