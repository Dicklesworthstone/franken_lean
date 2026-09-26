//! Recover a local callback's actual return stages from already prepared syntax.
//! This derives metadata; it never rewrites a call, substitutes a strict let, or
//! adapts a staged function to the flat interface of an external consumer.
use super::*;

mod captures;

impl Preparation<'_> {
    fn stage_interface(&mut self, signature: ClosureSignature) -> Result<ValueType, IngressError> {
        for index in 0..self.interfaces.len() {
            self.tick()?;
            if self.interfaces[index] == signature {
                let id = u32::try_from(index)
                    .map_err(|_| unsupported("local callback interface width"))?;
                return Ok(ValueType::Closure(ClosureTypeId::new(id)));
            }
        }
        reserve(&mut self.interfaces, self.limits.fir.max_closure_types)?;
        let index = u32::try_from(self.interfaces.len())
            .map_err(|_| unsupported("local callback interface width"))?;
        self.interfaces.push(signature);
        Ok(ValueType::Closure(ClosureTypeId::new(index)))
    }

    fn stage_apply(
        &mut self,
        mut value: ValueType,
        mut count: usize,
    ) -> Result<Option<ValueType>, IngressError> {
        while count != 0 {
            self.tick()?;
            let ValueType::Closure(id) = value else {
                return Ok(None);
            };
            let Some(signature) = self.interfaces.get(id.get() as usize).cloned() else {
                return Ok(None);
            };
            let arity = signature.parameters.len();
            if arity == 0 {
                return Ok(None);
            }
            if count < arity {
                return self
                    .stage_interface(ClosureSignature {
                        parameters: signature.parameters[count..].to_vec(),
                        parameter_ownership: signature.parameter_ownership[count..].to_vec(),
                        result: signature.result,
                        result_ownership: signature.result_ownership,
                    })
                    .map(Some);
            }
            count -= arity;
            value = signature.result;
        }
        Ok(Some(value))
    }

    /// Follow the result-producing path with a lexical type stack. Types of
    /// captures that lie outside this lambda are unknown, never guessed from a
    /// runtime value. Ordinary ingress remains the authority for every argument,
    /// capture and exact return interface.
    fn staged_result(
        &mut self,
        body: &Expr,
        parameters: &[ValueType],
    ) -> Result<Option<ValueType>, IngressError> {
        enum Work {
            Visit(Expr),
            Let(Expr, Expr),
            Leave,
            Apply(usize),
        }
        let mut work = vec![Work::Visit(body.clone())];
        let mut context: Vec<_> = parameters.iter().copied().map(Some).collect();
        let mut value = None;
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Work::Visit(expr) => match expr.node() {
                    ExprNode::BVar { idx } => {
                        value = usize::try_from(*idx)
                            .ok()
                            .and_then(|i| i.checked_add(1))
                            .and_then(|offset| context.len().checked_sub(offset))
                            .and_then(|i| context[i]);
                    }
                    ExprNode::MData { expr, .. } => {
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Visit(expr.clone()));
                    }
                    ExprNode::LetE {
                        type_,
                        value: init,
                        body,
                        ..
                    } => {
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Let(body.clone(), type_.clone()));
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Visit(init.clone()));
                    }
                    ExprNode::Lam { .. } => {
                        let mut signature = None;
                        for index in (0..self.lambdas.len()).rev() {
                            self.tick()?;
                            let lambda = &self.lambdas[index];
                            if lambda.lambda == expr {
                                signature = Some(ClosureSignature {
                                    parameters: lambda.parameters.clone(),
                                    parameter_ownership: lambda.parameter_ownership.clone(),
                                    result: lambda.result,
                                    result_ownership: lambda.result_ownership,
                                });
                                break;
                            }
                        }
                        value = signature.map(|s| self.stage_interface(s)).transpose()?;
                    }
                    ExprNode::App { .. } => {
                        let (head, args) = self.spine(&expr)?;
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Apply(args.len()));
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Visit(head));
                    }
                    ExprNode::Const { .. } => {
                        value = if let Some(type_) = self.callable_type(&expr)? {
                            self.value_type(&type_)?
                        } else {
                            None
                        };
                    }
                    _ => value = None,
                },
                Work::Let(body, type_) => {
                    // A scalar/ordinary callback annotation is a fallback only
                    // for a result whose staging was not discovered. Known
                    // staged values, including aliases, keep their exact type.
                    if value.is_none() {
                        value = self.value_type(&type_)?;
                    }
                    reserve(&mut context, self.limits.max_context_depth)?;
                    context.push(value);
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Leave);
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Visit(body));
                }
                Work::Leave => {
                    context.pop();
                }
                Work::Apply(count) => {
                    value = match value {
                        Some(v) => self.stage_apply(v, count)?,
                        None => None,
                    };
                }
            }
        }
        Ok(value)
    }

    /// Only return-stage grouping may differ. Parameter representations are
    /// still exact. In particular, this is not a representation-changing cast
    /// and does not relax fixed callable arguments or constructor fields.
    fn same_stage_telescope(&mut self, a: ValueType, b: ValueType) -> Result<bool, IngressError> {
        fn expand(
            preparation: &mut Preparation<'_>,
            mut ty: ValueType,
        ) -> Result<
            (
                Vec<(ValueType, fln_comp::flbc::ArgumentOwnership)>,
                ValueType,
            ),
            IngressError,
        > {
            let mut parameters = Vec::new();
            let mut seen = HashSet::new();
            while let ValueType::Closure(id) = ty {
                preparation.tick()?;
                seen.try_reserve(1)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::ProgramTables,
                        requested: seen.len().saturating_add(1),
                    })?;
                if !seen.insert(id) {
                    return Err(unsupported("cyclic callback stages"));
                }
                let Some(signature) = preparation.interfaces.get(id.get() as usize).cloned() else {
                    return Err(unsupported("unknown callback stage"));
                };
                if signature.result_ownership != result_ownership(signature.result)
                    || signature.parameters.len() != signature.parameter_ownership.len()
                {
                    return Err(unsupported("callback stage ownership"));
                }
                for parameter in signature
                    .parameters
                    .into_iter()
                    .zip(signature.parameter_ownership)
                {
                    preparation.tick()?;
                    reserve(&mut parameters, preparation.limits.max_context_depth)?;
                    parameters.push(parameter);
                }
                ty = signature.result;
            }
            Ok((parameters, ty))
        }
        Ok(expand(self, a)? == expand(self, b)?)
    }

    pub(crate) fn refine_local_result(
        &mut self,
        signature: &mut ExecutableSignature,
        prepared: &Expr,
    ) -> Result<(), IngressError> {
        if !matches!(signature.result, ValueType::Closure(_)) {
            return Ok(());
        }
        // Signature derivation normalizes types and may substitute local
        // templates in its copy of the expression. Closure annotations belong
        // to the exact, already prepared lambdas, so recover the return stage
        // from the body the compiler will actually receive.
        let mut body = prepared;
        for _ in &signature.parameters {
            self.tick()?;
            let ExprNode::Lam { body: inner, .. } = body.node() else {
                return Err(unsupported("prepared callback lambda spine"));
            };
            body = inner;
        }
        if let Some(actual @ ValueType::Closure(_)) =
            self.staged_result(body, &signature.parameters)?
            && actual != signature.result
            && self.same_stage_telescope(actual, signature.result)?
        {
            signature.result = actual;
            signature.result_ownership = result_ownership(actual);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
