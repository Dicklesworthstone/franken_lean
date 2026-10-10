//! Compile Partial function producers at their real lambda-prefix arity.
//!
//! A stable private global returns the suffix closure. Calls bind that result
//! before applying later arguments, so recursive prefix work is neither copied
//! during compilation nor delayed beneath invented lambdas. These entries
//! remain compiler inputs and pass the ordinary catalog and FIR checks.
use super::*;
use std::collections::HashMap;

#[derive(Clone)]
struct Parameter {
    name: Name,
    type_: Expr,
    info: BinderInfo,
}

#[derive(Clone)]
struct Entry {
    name: Name,
    type_: Expr,
    parameters: Vec<Parameter>,
    parameter_types: Vec<ValueType>,
    suffix: Expr,
    result: ValueType,
    body: Expr,
}

#[derive(Default)]
pub(in crate::runtime) struct Store {
    entries: Vec<Entry>,
    origins: HashMap<Name, usize>,
    names: HashMap<Name, usize>,
}

impl Preparation<'_> {
    pub(in crate::runtime) fn is_partial_stage(&self, name: &Name) -> bool {
        self.partial_stages.names.contains_key(name)
    }

    pub(in crate::runtime) fn partial_stage_type(&self, name: &Name) -> Option<Expr> {
        let index = *self.partial_stages.names.get(name)?;
        Some(self.partial_stages.entries[index].type_.clone())
    }

    pub(crate) fn partial_stage_signature(
        &mut self,
        name: &Name,
    ) -> Result<Option<ExecutableSignature>, IngressError> {
        self.tick()?;
        let Some(&index) = self.partial_stages.names.get(name) else {
            return Ok(None);
        };
        let entry = &self.partial_stages.entries[index];
        Ok(Some(ExecutableSignature {
            parameters: entry.parameter_types.clone(),
            result: entry.result,
            result_ownership: result_ownership(entry.result),
            body: entry.body.clone(),
        }))
    }

    fn partial_stage(&mut self, name: &Name) -> Result<Option<Entry>, IngressError> {
        self.tick()?;
        if self.is_partial_stage(name) {
            return Ok(None);
        }
        if let Some(&index) = self.partial_stages.origins.get(name) {
            return Ok(Some(self.partial_stages.entries[index].clone()));
        }
        match self.environment.find(name) {
            Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Partial => {}
            Some(_) => return Ok(None),
            None => {
                if !self
                    .specialized_definition(name)
                    .is_some_and(|value| value.safety == DefinitionSafety::Partial)
                {
                    return Ok(None);
                }
            }
        }
        let Some(definition) = self.executable_definition(name)? else {
            return Ok(None);
        };
        if definition.safety != DefinitionSafety::Partial
            || !definition.base.level_params.is_empty()
            || definition.base.name != *name
        {
            // Executable-head selection must already have resolved the logical
            // parent's attributes and complete companion linkage. This also
            // keeps a native parent from reaching its ignored companion here.
            return Ok(None);
        }
        let mut body = definition.value.clone();
        let mut type_ = definition.base.type_.clone();
        let mut depth = 0usize;
        loop {
            self.tick()?;
            if let ExprNode::MData { expr, .. } = body.node() {
                body = expr.clone();
                continue;
            }
            let ExprNode::Lam { body: next, .. } = body.node() else {
                break;
            };
            depth = depth.saturating_add(1);
            self.producer_depth(depth)?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE { body: result, .. } = normal.node() else {
                return Ok(None);
            };
            type_ = result.clone();
            body = next.clone();
        }
        if !matches!(self.type_head(&type_)?.node(), ExprNode::ForallE { .. }) {
            return Ok(None);
        }
        let observed = self.partial_stages.entries.len().saturating_add(1);
        if observed > self.limits.fir.max_functions {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ProgramTables,
                limit: self.limits.fir.max_functions,
                observed,
            });
        }
        let mut definition = self.normalize_definition_signature(&definition)?;
        if !specialize::closed(&definition.base.type_) {
            return Ok(None);
        }
        let mut type_ = definition.base.type_.clone();
        let mut body = definition.value.clone();
        let mut parameters = Vec::new();
        loop {
            self.tick()?;
            if let ExprNode::MData { expr, .. } = body.node() {
                body = expr.clone();
                continue;
            }
            let ExprNode::Lam {
                binder_name,
                binder_type,
                body: next,
                binder_info,
            } = body.node()
            else {
                break;
            };
            let ExprNode::ForallE {
                binder_type: domain,
                body: result,
                ..
            } = type_.node()
            else {
                return Ok(None);
            };
            if binder_type != domain || domain.has_loose_bvars() || result.has_loose_bvars() {
                return Ok(None);
            }
            self.producer_depth(parameters.len().saturating_add(1))?;
            reserve(&mut parameters, self.limits.max_context_depth)?;
            parameters.push(Parameter {
                name: binder_name.clone(),
                type_: domain.clone(),
                info: *binder_info,
            });
            type_ = result.clone();
            body = next.clone();
        }
        if !matches!(type_.node(), ExprNode::ForallE { .. }) {
            return Ok(None);
        }
        let Some(result @ ValueType::Closure(_)) = self.value_type(&type_)? else {
            return Ok(None);
        };
        // This annotation reaches real return lambdas inside strict lets and
        // case branches. It neither constructs nor invokes the returned value.
        body = self.typed_callable_result(body, type_.clone(), result)?;
        let mut value = body.clone();
        for parameter in parameters.iter().rev() {
            self.tick()?;
            value = Expr::lam(
                parameter.name.clone(),
                parameter.type_.clone(),
                value,
                parameter.info,
            );
        }
        definition.value = value;
        let parameter_types = if parameters.is_empty() {
            // A zero-argument producer runs before returning its closure too.
            // The catalog supports this directly; local lambda registration
            // intentionally requires at least one actual lambda instead.
            Vec::new()
        } else {
            let Some(signature) = self.prepared_signature(&definition, false)? else {
                return Ok(None);
            };
            if signature.parameters.len() != parameters.len() || signature.result != result {
                return Ok(None);
            }
            signature.parameters
        };
        let serial = u64::try_from(self.partial_stages.entries.len())
            .map_err(|_| unsupported("partial stage identity"))?;
        let entry_name = Name::num(name_of_stages(), serial);
        if self.environment.contains(&entry_name) || self.has_private_callable(&entry_name) {
            return Err(unsupported("partial stage name collision"));
        }
        let entry = Entry {
            name: entry_name.clone(),
            type_: definition.base.type_,
            parameters,
            parameter_types,
            suffix: type_,
            result,
            body,
        };
        reserve(
            &mut self.partial_stages.entries,
            self.limits.fir.max_functions,
        )?;
        for map in [
            &mut self.partial_stages.origins,
            &mut self.partial_stages.names,
        ] {
            map.try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: observed,
                })?;
        }
        let index = self.partial_stages.entries.len();
        self.partial_stages.origins.insert(name.clone(), index);
        self.partial_stages.names.insert(entry_name, index);
        self.partial_stages.entries.push(entry.clone());
        Ok(Some(entry))
    }

    pub(super) fn partial_stage_call(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        if args.len() > self.limits.max_application_args {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ApplicationArguments,
                limit: self.limits.max_application_args,
                observed: args.len(),
            });
        }
        let Some(entry) = self.partial_stage(name)? else {
            return Ok(None);
        };
        let prefix = entry.parameters.len();
        let supplied = args.len().min(prefix);
        let mut value = Expr::const_(entry.name, Vec::new());
        for index in (0..prefix).rev() {
            self.tick()?;
            value = Expr::app(value, variable(index)?);
        }
        value = if args.len() > prefix {
            let Some(applied) =
                self.apply_producer(value, entry.suffix, &args[prefix..], prefix)?
            else {
                return Ok(None);
            };
            applied
        } else {
            self.typed_callable_result(value, entry.suffix, entry.result)?
        };
        if supplied < prefix {
            for parameter in entry.parameters[supplied..].iter().rev() {
                self.tick()?;
                value = Expr::lam(
                    parameter.name.clone(),
                    parameter.type_.clone(),
                    value,
                    parameter.info,
                );
            }
            let mut remaining = entry.type_.clone();
            for _ in 0..supplied {
                let ExprNode::ForallE { body, .. } = remaining.node() else {
                    return Err(unsupported("partial stage supplied telescope"));
                };
                remaining = body.clone();
            }
            let Some(callback @ ValueType::Closure(_)) = self.value_type(&remaining)? else {
                return Err(unsupported("partial stage remaining representation"));
            };
            value = self.typed_callable_result(value, remaining, callback)?;
        }
        for (index, (parameter, argument)) in entry.parameters[..supplied]
            .iter()
            .zip(args)
            .enumerate()
            .rev()
        {
            self.tick()?;
            let offset = self.producer_depth(index)?;
            value = Expr::let_e(
                parameter.name.clone(),
                parameter.type_.clone(),
                self.lift(argument, offset)?,
                value,
                false,
            );
        }
        Ok(Some(value))
    }
}

fn name_of_stages() -> Name {
    Name::from_components(["_fln_runtime_partial_stage"])
}

#[cfg(test)]
mod tests;
