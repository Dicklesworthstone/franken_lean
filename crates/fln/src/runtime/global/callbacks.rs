//! Specialize a known staged callback at a checked call site rather than cast
//! it to a flat ABI. Literal lambdas are values: only their syntax is copied.
//! Every other supplied operand keeps one strict binding in source order.
use super::*;

impl Preparation<'_> {
    /// Typed identity lets can hide a literal consumer or callback after
    /// dictionary projection. Expose only lambda construction, its aliases,
    /// and checked administrative field selection. A computed initializer still
    /// takes the ordinary strict path. Retain each checked annotation at the
    /// real lambda's return stages before removing its administrative binding.
    pub(in crate::runtime) fn inert_callable(
        &mut self,
        input: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        let mut value = input.clone();
        let mut bindings = Vec::new();
        loop {
            self.tick()?;
            match value.node() {
                ExprNode::MData { expr, .. } => value = expr.clone(),
                ExprNode::LetE {
                    type_,
                    value: initializer,
                    body,
                    ..
                } => {
                    self.producer_depth(bindings.len().saturating_add(1))?;
                    reserve(&mut bindings, self.limits.max_context_depth)?;
                    bindings.push((type_.clone(), body.clone()));
                    value = initializer.clone();
                }
                ExprNode::Lam { .. } => {
                    let Some((type_, body)) = bindings.pop() else {
                        return Ok(Some(value));
                    };
                    let literal = self.annotate_callable_tail(&value, &type_)?;
                    value = self.substitution(&body, &literal)?;
                }
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    let Some(projected) = self.executable_projection(struct_name, *idx, expr)?
                    else {
                        return Ok(None);
                    };
                    value = projected;
                }
                ExprNode::App { .. } => {
                    let (head, arguments) = self.spine(&value)?;
                    let selected = match self.projection_call(&head, &arguments)? {
                        Some(projected) => Some(projected),
                        None => self.static_callable_instance(&head, &arguments)?,
                    };
                    let Some(projected) = selected else {
                        return Ok(None);
                    };
                    value = projected;
                }
                _ => return Ok(None),
            }
        }
    }

    /// A global method applied only to its checked static arguments is still
    /// lambda construction. Expose the existing specialization's literal body
    /// before an administrative alias registers a flat wrapper around it. Any
    /// runtime operand or computed initializer keeps the ordinary strict path.
    fn static_callable_instance(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        if !matches!(self.environment.find(name),
            Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe)
        {
            return Ok(None);
        }
        let Some(specialized) = self.specialize_call(head, arguments)? else {
            return Ok(None);
        };
        let (selected, runtime_arguments) = self.spine(&specialized)?;
        if !runtime_arguments.is_empty() {
            return Ok(None);
        }
        let ExprNode::Const {
            name: selected,
            levels,
        } = selected.node()
        else {
            return Ok(None);
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        let Some(definition) = self.specialized_definition(selected) else {
            return Ok(None);
        };
        if definition.safety != DefinitionSafety::Safe
            || !matches!(definition.value.node(), ExprNode::Lam { .. })
        {
            return Ok(None);
        }
        source_intrinsics::check_selected_extern_attribute(
            self.environment,
            name,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        let definition = self.normalize_definition_signature(&definition)?;
        self.annotate_callable_tail(&definition.value, &definition.base.type_)
            .map(Some)
    }

    /// Keep a known higher-order consumer visible until its actual callback
    /// operands are available. Strict producer prefixes remain outside the
    /// substituted literal, in their original order and evaluated once.
    /// This runs before either initializer or body registers local closures.
    pub(in crate::runtime) fn expose_callable_binding(
        &mut self,
        type_: &Expr,
        initializer: &Expr,
        body: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        let mut result = body;
        while let ExprNode::MData { expr, .. } = result.node() {
            self.tick()?;
            result = expr;
        }
        if matches!(result.node(), ExprNode::BVar { idx: 0 }) {
            // This binding is the checked type anchor of a returned closure.
            return Ok(None);
        }
        let mut value = initializer.clone();
        let mut prefix = Vec::new();
        loop {
            self.tick()?;
            if let Some(literal) = self.inert_callable(&value)? {
                value = literal;
                break;
            }
            match value.node() {
                ExprNode::MData { expr, .. } => value = expr.clone(),
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value: init,
                    body,
                    non_dep,
                } => {
                    self.producer_depth(prefix.len().saturating_add(1))?;
                    reserve(&mut prefix, self.limits.max_context_depth)?;
                    prefix.push((decl_name.clone(), type_.clone(), init.clone(), *non_dep));
                    value = body.clone();
                }
                ExprNode::App { .. } => {
                    let (head, args) = self.spine(&value)?;
                    let reduced = match self.projection_call(&head, &args)? {
                        Some(projected) => Some(projected),
                        None => match self.static_apply(&head, &args)? {
                            Some(applied) => Some(applied),
                            None => self.static_callable_instance(&head, &args)?,
                        },
                    };
                    let Some(reduced) = reduced else {
                        return Ok(None);
                    };
                    if reduced == value {
                        return Ok(None);
                    }
                    value = reduced;
                }
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    let Some(projected) = self.executable_projection(struct_name, *idx, expr)?
                    else {
                        return Ok(None);
                    };
                    value = projected;
                }
                ExprNode::Lam { .. } => break,
                _ => {
                    return Ok(None);
                }
            }
        }
        let depth = self.producer_depth(prefix.len())?;
        let shifted_type = self.lift(type_, depth)?;
        let mut selected = self.staged_callback(&value, &shifted_type)?;
        if !selected {
            let mut consumer = false;
            let mut remaining = self.normalize_type(&shifted_type)?;
            let mut lambda = value.clone();
            while let (
                ExprNode::Lam { body: next, .. },
                ExprNode::ForallE {
                    binder_type, body, ..
                },
            ) = (lambda.node(), remaining.node())
            {
                self.tick()?;
                // Ordinary first-order local functions retain shared closure
                // bindings. Only generic templates and actual callable
                // consumers need this call-site exposure.
                if self.type_parameter(binder_type)? {
                    selected = true;
                    break;
                }
                consumer |= !binder_type.has_loose_bvars()
                    && matches!(self.value_type(binder_type)?, Some(ValueType::Closure(_)));
                lambda = next.clone();
                remaining = self.type_head(body)?;
            }
            // A flat callback used as a value needs this outer checked type.
            // Inlining it into an ordinary global call recreates annotate_call's
            // input; inlining it into a local call loses its signature entirely.
            // Expose a consumer only when every runtime occurrence is called.
            selected |= consumer && self.only_callee_uses(body)?;
        }
        if !selected {
            return Ok(None);
        }
        let literal = self.annotate_callable_tail(&value, &shifted_type)?;
        let literal = self.retain_staged_callable_type(literal, &shifted_type)?;
        // Lifting a lambda keeps the bound function slot at zero while
        // shifting every outer capture beneath the retained strict prefix.
        let scoped_body = self.lift(
            &Expr::lam(
                Name::anonymous(),
                type_.clone(),
                body.clone(),
                BinderInfo::Default,
            ),
            depth,
        )?;
        let ExprNode::Lam { body, .. } = scoped_body.node() else {
            return Err(unsupported("known callback binding scope"));
        };
        let mut result = self.substitution(body, &literal)?;
        for (name, type_, value, non_dep) in prefix.into_iter().rev() {
            self.tick()?;
            result = Expr::let_e(name, type_, value, result, non_dep);
        }
        Ok(Some(result))
    }

    /// A staged literal may remain a value after substitution, for example as
    /// an argument to a local consumer. Its returned stages are annotated by
    /// `annotate_callable_tail`, but the outer stage needs its checked type as
    /// well. Keep an identity let which ordinary local registration consumes;
    /// known applications can still inspect the literal via `inert_callable`.
    pub(in crate::runtime) fn retain_staged_callable_type(
        &mut self,
        value: Expr,
        type_: &Expr,
    ) -> Result<Expr, IngressError> {
        if !self.staged_callback(&value, type_)? {
            return Ok(value);
        }
        let type_ = self.normalize_type(type_)?;
        let Some(result @ ValueType::Closure(_)) = self.value_type(&type_)? else {
            return Ok(value);
        };
        self.typed_callable_result(value, type_, result)
    }

    /// Substituting an inert function argument can forward it to a runtime
    /// consumer whose type is no longer available to expression preparation.
    /// Preserve the checked outer type at such value occurrences, including
    /// ordinary flat callbacks. Direct callee uses still expose their literal
    /// syntax, while staged callbacks retain their existing return annotations.
    pub(in crate::runtime) fn retain_substituted_callable_type(
        &mut self,
        value: Expr,
        type_: &Expr,
        body: &Expr,
    ) -> Result<Expr, IngressError> {
        if !self.type_parameter(type_)? {
            let type_ = self.normalize_type(type_)?;
            if let Some(result @ ValueType::Closure(_)) = self.value_type(&type_)?
                && !self.only_callee_uses(body)?
            {
                return self.typed_callable_result(value, type_, result);
            }
        }
        self.retain_staged_callable_type(value, type_)
    }

    fn only_callee_uses(&mut self, body: &Expr) -> Result<bool, IngressError> {
        let mut pending = vec![(body.clone(), 0usize, false)];
        let mut used = false;
        while let Some((expr, depth, callee)) = pending.pop() {
            self.tick()?;
            // The cached range includes every loose variable, including those
            // in types. If this slot is absent, the subtree cannot change the
            // answer. Still retain the original binder-depth refusals: only an
            // unsaturated structural height can prove every skipped descent
            // fits the checked context and the producer's u32 depth bound.
            let height = expr.approx_depth();
            if usize::try_from(expr.loose_bvar_range()).is_ok_and(|range| range <= depth)
                && height < u8::MAX
                && depth.checked_add(usize::from(height)).is_some_and(|end| {
                    end <= self.limits.max_context_depth && u32::try_from(end).is_ok()
                })
            {
                continue;
            }
            match expr.node() {
                ExprNode::BVar { idx } if usize::try_from(*idx).ok() == Some(depth) => {
                    if !callee {
                        return Ok(false);
                    }
                    used = true;
                }
                ExprNode::App { f, a } => {
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((a.clone(), depth, false));
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((f.clone(), depth, true));
                }
                ExprNode::Lam { body, .. } => {
                    let nested = depth.saturating_add(1);
                    self.producer_depth(nested)?;
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((body.clone(), nested, false));
                }
                ExprNode::LetE { value, body, .. } => {
                    let nested = depth.saturating_add(1);
                    self.producer_depth(nested)?;
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((body.clone(), nested, callee));
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((value.clone(), depth, false));
                }
                ExprNode::MData { expr, .. } => {
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((expr.clone(), depth, callee));
                }
                ExprNode::Proj { expr, .. } => {
                    reserve(&mut pending, self.limits.max_nodes)?;
                    pending.push((expr.clone(), depth, false));
                }
                // Binder domains and let annotations are checked source types,
                // not runtime value occurrences. Their erasure is unchanged.
                _ => {}
            }
        }
        Ok(used)
    }

    fn staged_callback(&mut self, input: &Expr, type_: &Expr) -> Result<bool, IngressError> {
        let Some(mut value) = self.inert_callable(input)? else {
            return Ok(false);
        };
        let mut type_ = self.normalize_type(type_)?;
        let mut depth = 0usize;
        loop {
            self.tick()?;
            if let ExprNode::MData { expr, .. } = value.node() {
                value = expr.clone();
                continue;
            }
            let (ExprNode::Lam { body, .. }, ExprNode::ForallE { body: result, .. }) =
                (value.node(), type_.node())
            else {
                return Ok(depth != 0 && matches!(type_.node(), ExprNode::ForallE { .. }));
            };
            depth = depth.saturating_add(1);
            self.producer_depth(depth)?;
            value = body.clone();
            type_ = result.clone();
        }
    }

    /// This is a bounded higher-order specialization, not a general closure
    /// conversion between different interfaces. An opaque/dynamic callback is
    /// never reinterpreted, and a strict callback-producing operand is not
    /// treated as an inert lambda. The normal FIR checker still sees every call.
    pub(super) fn specialize_staged_callback(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if args.is_empty() {
            return Ok(None);
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let definition = match self.environment.find(name) {
            Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe => {
                Some(definition.clone())
            }
            Some(_) => None,
            None => self
                .specialized_definition(name)
                .filter(|definition| definition.safety == DefinitionSafety::Safe),
        };
        let Some(mut definition) = definition else {
            return Ok(None);
        };
        if definition.base.level_params.len() != levels.len()
            || levels
                .iter()
                .any(|level| level.has_mvar() || level.has_param())
        {
            return Ok(None);
        }
        if args.len() > self.limits.max_application_args {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ApplicationArguments,
                limit: self.limits.max_application_args,
                observed: args.len(),
            });
        }
        let mut literal = false;
        for argument in args {
            self.tick()?;
            if self.inert_callable(argument)?.is_some() {
                literal = true;
                break;
            }
        }
        if !literal {
            return Ok(None);
        }
        definition.base.type_ = self.universe_instance(
            &definition.base.type_,
            &definition.base.level_params,
            levels,
        )?;
        definition.value =
            self.universe_instance(&definition.value, &definition.base.level_params, levels)?;
        definition.base.level_params.clear();
        // Detect against original source types first. Ordinary flat callbacks
        // keep the existing catalog path and need no body/layout preparation.
        let mut type_ = definition.base.type_.clone();
        let mut value = definition.value.clone();
        let mut selected = false;
        for argument in args {
            self.tick()?;
            while let ExprNode::MData { expr, .. } = value.node() {
                self.tick()?;
                value = expr.clone();
            }
            let normal = self.type_head(&type_)?;
            let (
                ExprNode::Lam { body: next, .. },
                ExprNode::ForallE {
                    binder_type, body, ..
                },
            ) = (value.node(), normal.node())
            else {
                break;
            };
            selected |= self.staged_callback(argument, binder_type)?;
            type_ = self.substitution(body, argument)?;
            value = next.clone();
        }
        if !selected {
            return Ok(None);
        }
        // Inlining removes this constant before executable catalog discovery.
        // Its selected extern policy must still be checked before using the body.
        source_intrinsics::check_selected_extern_attribute(
            self.environment,
            name,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )?;
        let definition = self.normalize_definition_signature(&definition)?;
        self.inline_callback_arguments(definition, args)
    }

    fn inline_callback_arguments(
        &mut self,
        definition: DefinitionVal,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let mut value = definition.value;
        let mut type_ = definition.base.type_;
        let mut bindings = Vec::new();
        let mut consumed = 0;
        for argument in args {
            self.tick()?;
            while let ExprNode::MData { expr, .. } = value.node() {
                self.tick()?;
                value = expr.clone();
            }
            let normal = self.type_head(&type_)?;
            let (
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: domain,
                    body: result,
                    ..
                },
            ) = (value.node(), normal.node())
            else {
                break;
            };
            // No representation is guessed for a genuinely dependent runtime
            // parameter or a type argument not handled by monomorphization.
            if self.normalize_type(binder_type)? != self.normalize_type(domain)?
                || domain.has_loose_bvars()
                || result.has_loose_bvars()
                || self.value_type(domain)?.is_none()
            {
                return Ok(None);
            }
            let offset = self.producer_depth(bindings.len())?;
            let argument = self.lift(argument, offset)?;
            if let Some(lambda) = self.inert_callable(&argument)? {
                let lambda = self.retain_substituted_callable_type(lambda, domain, body)?;
                // Captures already name runtime values, not initializer code.
                // The charged capture-avoiding substitution adjusts both the
                // removed parameter and all retained strict argument slots.
                value = self.substitution(body, &lambda)?;
                type_ = self.substitution(result, &lambda)?;
            } else {
                self.producer_depth(bindings.len().saturating_add(1))?;
                reserve(&mut bindings, self.limits.max_context_depth)?;
                bindings.push(Binder {
                    name: binder_name.clone(),
                    domain: domain.clone(),
                    value: argument,
                });
                value = body.clone();
                type_ = result.clone();
            }
            consumed += 1;
        }
        if consumed < args.len() {
            let Some(applied) =
                self.apply_producer(value, type_, &args[consumed..], bindings.len())?
            else {
                return Ok(None);
            };
            value = applied;
        } else {
            value = self.annotate_execution_value(value, type_.clone())?;
            let Some(result) = self.value_type(&type_)? else {
                return Ok(None);
            };
            // A partially applied consumer still needs the actual remaining
            // lambda registered as a value, inside the retained arguments.
            value = self.typed_callable_result(value, type_, result)?;
        }
        for binding in bindings.into_iter().rev() {
            self.tick()?;
            value = Expr::let_e(binding.name, binding.domain, binding.value, value, false);
        }
        Ok(Some(value))
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod uses_tests;
