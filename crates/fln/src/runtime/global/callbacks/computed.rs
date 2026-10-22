//! Keep a computed staged callback local to its checked consumer. Unlike the
//! literal path, the producer stays in one strict binding; it is never copied
//! into callback occurrences or reinterpreted as a flat closure interface.
use super::*;

impl Preparation<'_> {
    pub(in crate::runtime) fn specialize_computed_callback(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if args.len() > self.limits.max_application_args {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ApplicationArguments,
                limit: self.limits.max_application_args,
                observed: args.len(),
            });
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
        // An ineligible callee cannot consume a staged callback. Check that
        // once before scanning a potentially long application spine.
        let mut computed = false;
        for argument in args {
            self.tick()?;
            if matches!(
                argument.node(),
                ExprNode::App { .. } | ExprNode::LetE { .. } | ExprNode::MData { .. }
            ) {
                computed = true;
                break;
            }
        }
        if !computed {
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
                // Never move an operand before a strict callee stage merely
                // to find a later callback parameter.
                break;
            };
            if matches!(
                argument.node(),
                ExprNode::App { .. } | ExprNode::LetE { .. } | ExprNode::MData { .. }
            ) && !binder_type.has_loose_bvars()
                && matches!(
                    self.type_head(binder_type)?.node(),
                    ExprNode::ForallE { .. }
                )
                && !self.type_parameter(binder_type)?
                && self.computed_callback_is_staged(argument, binder_type)?
                && matches!(self.value_type(binder_type)?, Some(ValueType::Closure(_)))
            {
                selected = true;
                break;
            }
            type_ = self.substitution(body, argument)?;
            value = next.clone();
        }
        if !selected {
            return Ok(None);
        }
        // Only the consumer disappears. The producer remains an ordinary
        // operand and retains its own extern/implemented_by selection later.
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

    /// Recognize the same shortened lambda spine as the existing global
    /// producer path, but do not run or substitute its runtime arguments.
    /// Arbitrary/dynamic factories stay unsupported. Static specialization is
    /// the ordinary checked, metered path, never guessed representation data.
    fn computed_callback_is_staged(
        &mut self,
        input: &Expr,
        expected: &Expr,
    ) -> Result<bool, IngressError> {
        let mut value = input.clone();
        let mut strict_depth = 0usize;
        loop {
            self.tick()?;
            match value.node() {
                ExprNode::MData { expr, .. } => {
                    value = expr.clone();
                    continue;
                }
                ExprNode::LetE { body, .. } => {
                    strict_depth = strict_depth.saturating_add(1);
                    self.producer_depth(strict_depth)?;
                    value = body.clone();
                    continue;
                }
                ExprNode::Lam { .. } => {
                    return Ok(strict_depth != 0 && self.staged_callback(&value, expected)?);
                }
                _ => {}
            }
            let (head, arguments) = self.spine(&value)?;
            if let Some(replacement) = self.implemented_by_call(&head, &arguments)? {
                value = replacement;
                continue;
            }
            if let Some(specialized) = self.specialize_call(&head, &arguments)?
                && specialized != value
            {
                value = specialized;
                continue;
            }
            let ExprNode::Const { name, levels } = head.node() else {
                return Ok(false);
            };
            let Some(definition) = self.executable_definition(name)? else {
                return Ok(false);
            };
            if !matches!(
                definition.safety,
                DefinitionSafety::Safe | DefinitionSafety::Partial
            ) {
                return Ok(false);
            }
            if definition.base.level_params.len() != levels.len()
                || levels
                    .iter()
                    .any(|level| level.has_mvar() || level.has_param())
            {
                return Ok(false);
            }
            let mut remaining = self.universe_instance(
                &definition.base.type_,
                &definition.base.level_params,
                levels,
            )?;
            let mut body = definition.value.clone();
            let mut prefix = 0usize;
            let mut result_type = None;
            while let ExprNode::Lam { body: next, .. } = body.node() {
                self.producer_depth(prefix.saturating_add(1))?;
                if prefix == arguments.len() {
                    result_type = Some(remaining.clone());
                }
                let normal = self.type_head(&remaining)?;
                let ExprNode::ForallE {
                    binder_type,
                    body: result,
                    ..
                } = normal.node()
                else {
                    return Ok(false);
                };
                // A value-dependent return telescope is outside this bounded
                // specialization. The original checked producer still owns it.
                if binder_type.has_loose_bvars() || result.has_loose_bvars() {
                    return Ok(false);
                }
                remaining = result.clone();
                body = next.clone();
                prefix = prefix.saturating_add(1);
            }
            let Some(result_type) = result_type else {
                return Ok(false);
            };
            let remaining = self.type_head(&remaining)?;
            return Ok(arguments.len() < prefix
                && matches!(remaining.node(), ExprNode::ForallE { .. })
                && self.same_computed_callback_type(&result_type, expected)?);
        }
    }

    /// Type normalization retains binder spelling, while a function's named
    /// argument and an arrow annotation may use different names. Compare the
    /// normalized logical structure modulo those labels only; this is not a
    /// runtime representation comparison or a conversion between stage ABIs.
    fn same_computed_callback_type(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, IngressError> {
        let left = self.normalize_type(left)?;
        let right = self.normalize_type(right)?;
        let mut pending = Vec::new();
        reserve(&mut pending, self.limits.max_nodes)?;
        pending.push((left, right));
        while let Some((left, right)) = pending.pop() {
            self.tick()?;
            if left == right {
                continue;
            }
            let pairs = match (left.node(), right.node()) {
                (
                    ExprNode::ForallE {
                        binder_type: ld,
                        body: lb,
                        binder_info: li,
                        ..
                    },
                    ExprNode::ForallE {
                        binder_type: rd,
                        body: rb,
                        binder_info: ri,
                        ..
                    },
                )
                | (
                    ExprNode::Lam {
                        binder_type: ld,
                        body: lb,
                        binder_info: li,
                        ..
                    },
                    ExprNode::Lam {
                        binder_type: rd,
                        body: rb,
                        binder_info: ri,
                        ..
                    },
                ) if li == ri => [(ld.clone(), rd.clone()), (lb.clone(), rb.clone())],
                (ExprNode::App { f: lf, a: la }, ExprNode::App { f: rf, a: ra }) => {
                    [(lf.clone(), rf.clone()), (la.clone(), ra.clone())]
                }
                _ => return Ok(false),
            };
            for pair in pairs {
                reserve(&mut pending, self.limits.max_nodes)?;
                pending.push(pair);
            }
        }
        Ok(true)
    }
}
