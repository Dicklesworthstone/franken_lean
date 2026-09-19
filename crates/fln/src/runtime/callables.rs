//! Derive runtime callback interfaces from admitted, nondependent function
//! types. Source-local ids are resolved only after every lambda (including
//! lazy branches and recursors) is known. The compiler independently validates
//! the resulting canonical signature table, captures, ownership, and calls.
use super::*;
use fln_comp::{fir::ClosureTypeId, ingress::ClosureSignature};

impl Preparation<'_> {
    /// Use a heap stack for nested higher-order domains. Function values carry
    /// no new source declarations, axioms, or trusted type-conversion rules.
    pub(super) fn function_value_type(
        &mut self,
        source: &Expr,
    ) -> Result<Option<ValueType>, IngressError> {
        enum Work {
            Enter(Expr),
            Finish { source: Expr, parameters: usize },
        }
        let mut work = vec![Work::Enter(source.clone())];
        let mut values = Vec::new();
        while let Some(item) = work.pop() {
            self.tick()?;
            match item {
                Work::Enter(source) => {
                    if let Some(&value) = self.value_types.closures.get(&source) {
                        reserve(&mut values, self.limits.max_nodes)?;
                        values.push(value);
                        continue;
                    }
                    if !matches!(source.node(), ExprNode::ForallE { .. }) {
                        let Some(value) = self.value_type(&source)? else {
                            return Ok(None);
                        };
                        reserve(&mut values, self.limits.max_nodes)?;
                        values.push(value);
                        continue;
                    }
                    let mut remaining = &source;
                    let mut domains = Vec::new();
                    while let ExprNode::ForallE {
                        binder_type, body, ..
                    } = remaining.node()
                    {
                        self.tick()?;
                        // A type parameter or value-dependent representation is
                        // not an erased scalar or callback interface.
                        if body.has_loose_bvars() {
                            return Ok(None);
                        }
                        reserve(&mut domains, self.limits.max_context_depth)?;
                        domains.push(binder_type.clone());
                        remaining = body;
                    }
                    let result = remaining.clone();
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Finish {
                        source,
                        parameters: domains.len(),
                    });
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Enter(result));
                    for domain in domains.into_iter().rev() {
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Enter(domain));
                    }
                }
                Work::Finish { source, parameters } => {
                    let result = values
                        .pop()
                        .ok_or_else(|| unsupported("callback result stack"))?;
                    let start = values
                        .len()
                        .checked_sub(parameters)
                        .ok_or_else(|| unsupported("callback parameter stack"))?;
                    let mut arguments = Vec::new();
                    for value in values.drain(start..) {
                        reserve(&mut arguments, self.limits.max_context_depth)?;
                        arguments.push(value);
                    }
                    reserve(&mut self.interfaces, self.limits.fir.max_closure_types)?;
                    let id = u32::try_from(self.interfaces.len())
                        .map_err(|_| unsupported("callback interface identity"))?;
                    self.interfaces.push(ClosureSignature {
                        parameter_ownership: borrowed_runtime_parameters(arguments.len())?,
                        parameters: arguments,
                        result,
                        result_ownership: result_ownership(result),
                    });
                    let value = ValueType::Closure(ClosureTypeId::new(id));
                    self.value_types.closures.try_reserve(1).map_err(|_| {
                        IngressError::AllocationFailure {
                            resource: IngressResource::ProgramTables,
                            requested: self.value_types.closures.len().saturating_add(1),
                        }
                    })?;
                    self.value_types.closures.insert(source, value);
                    reserve(&mut values, self.limits.max_nodes)?;
                    values.push(value);
                }
            }
        }
        if values.len() != 1 {
            return Err(unsupported("callback type stack"));
        }
        Ok(values.pop())
    }

    /// Resolve source-local callback ids to the exact canonical FIR ids. The
    /// source types form a finite acyclic graph; rank refinement reaches the
    /// structural order after at most one pass per interface dependency. Every
    /// signature visit is charged, including suffix construction and retries.
    pub(crate) fn finalize_callables(
        &mut self,
        functions: &mut [FunctionBinding],
    ) -> Result<Vec<ClosureSignature>, IngressError> {
        if self.interfaces.is_empty() {
            return Ok(Vec::new());
        }
        let mut signatures = Vec::new();
        for (index, signature) in self.interfaces.iter().enumerate() {
            add_suffixes(
                &mut signatures,
                signature,
                Some(index),
                self.limits,
                &mut self.visited,
            )?;
        }
        for lambda in &self.lambdas {
            let signature = ClosureSignature {
                parameters: lambda.parameters.clone(),
                parameter_ownership: lambda.parameter_ownership.clone(),
                result: lambda.result,
                result_ownership: lambda.result_ownership,
            };
            add_suffixes(
                &mut signatures,
                &signature,
                None,
                self.limits,
                &mut self.visited,
            )?;
        }
        let mut ranks = (0..self.interfaces.len())
            .map(|index| u32::try_from(index).map_err(|_| unsupported("callback rank width")))
            .collect::<Result<Vec<_>, _>>()?;
        let mut settled = false;
        for _ in 0..=self.interfaces.len() {
            let mut ordered = Vec::new();
            for (owner, signature) in &signatures {
                self.tick()?;
                let signature = remap_signature(signature, &ranks)?;
                reserve(&mut ordered, self.limits.fir.max_closure_types)?;
                ordered.push((*owner, signature));
            }
            // Charge the comparison/operand envelope before sorting. The bound
            // is conservative and deterministic, not wall-clock fuel.
            let width = ordered.len().max(1).ilog2() as usize + 1;
            let cells = ordered
                .iter()
                .try_fold(0usize, |sum, (_, item)| {
                    sum.checked_add(item.parameters.len().saturating_add(1))
                })
                .and_then(|sum| sum.checked_mul(width))
                .ok_or_else(|| unsupported("callback sort work overflow"))?;
            for _ in 0..cells {
                self.tick()?;
            }
            ordered.sort_by(|(_, a), (_, b)| signature_order(a, b));
            let mut next = vec![0; ranks.len()];
            let mut rank = 0u32;
            for (index, (owner, signature)) in ordered.iter().enumerate() {
                self.tick()?;
                if index != 0 && signature != &ordered[index - 1].1 {
                    rank = rank
                        .checked_add(1)
                        .ok_or_else(|| unsupported("callback rank width"))?;
                }
                if let Some(owner) = owner {
                    next[*owner] = rank;
                }
            }
            if ranks == next {
                settled = true;
                break;
            }
            ranks = next;
        }
        if !settled {
            return Err(unsupported("cyclic callback signature ranks"));
        }
        for function in functions {
            for parameter in &mut function.parameters {
                *parameter = remap_type(*parameter, &ranks)?;
            }
            function.result = remap_type(function.result, &ranks)?;
        }
        for lambda in &mut self.lambdas {
            for parameter in &mut lambda.parameters {
                *parameter = remap_type(*parameter, &ranks)?;
            }
            lambda.result = remap_type(lambda.result, &ranks)?;
        }
        self.interfaces
            .iter()
            .map(|signature| remap_signature(signature, &ranks))
            .collect()
    }
}

fn signature_order(a: &ClosureSignature, b: &ClosureSignature) -> std::cmp::Ordering {
    a.parameters
        .cmp(&b.parameters)
        .then_with(|| a.parameter_ownership.cmp(&b.parameter_ownership))
        .then_with(|| a.result.cmp(&b.result))
        .then_with(|| a.result_ownership.cmp(&b.result_ownership))
}

fn remap_type(value: ValueType, ranks: &[u32]) -> Result<ValueType, IngressError> {
    match value {
        ValueType::Closure(id) => ranks
            .get(id.get() as usize)
            .copied()
            .map(|rank| ValueType::Closure(ClosureTypeId::new(rank)))
            .ok_or_else(|| unsupported("unknown callback type identity")),
        value => Ok(value),
    }
}

fn remap_signature(
    value: &ClosureSignature,
    ranks: &[u32],
) -> Result<ClosureSignature, IngressError> {
    Ok(ClosureSignature {
        parameters: value
            .parameters
            .iter()
            .map(|&value| remap_type(value, ranks))
            .collect::<Result<_, _>>()?,
        parameter_ownership: value.parameter_ownership.clone(),
        result: remap_type(value.result, ranks)?,
        result_ownership: value.result_ownership,
    })
}

fn add_suffixes(
    output: &mut Vec<(Option<usize>, ClosureSignature)>,
    value: &ClosureSignature,
    owner: Option<usize>,
    limits: IngressLimits,
    visited: &mut usize,
) -> Result<(), IngressError> {
    for start in 0..value.parameters.len() {
        charge_catalog_node(visited, limits)?;
        for _ in start..value.parameters.len() {
            charge_catalog_node(visited, limits)?;
        }
        reserve(output, limits.fir.max_closure_types)?;
        output.push((
            if start == 0 { owner } else { None },
            ClosureSignature {
                parameters: value.parameters[start..].to_vec(),
                parameter_ownership: value.parameter_ownership[start..].to_vec(),
                result: value.result,
                result_ownership: value.result_ownership,
            },
        ));
    }
    Ok(())
}
