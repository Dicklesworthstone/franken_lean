//! Derive runtime callback interfaces from admitted, nondependent function
//! types. Source-local ids are resolved only after every lambda (including
//! lazy branches and recursors) is known. The compiler independently validates
//! the resulting canonical signature table, captures, ownership, and calls.
mod stages;

use super::*;
use fln_comp::{fir::ClosureTypeId, ingress::ClosureSignature};

impl Preparation<'_> {
    /// Keep an application of a data eliminator's returned closure distinct
    /// from the eliminator's own arguments. The let evaluates the selected
    /// function once, before its arguments, without evaluating either branch.
    pub(super) fn overapplied_data_recursor(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(name) else {
            return Ok(None);
        };
        if rec.is_unsafe || rec.num_motives as usize != rec.all.len() || rec.all.is_empty() {
            return Ok(None);
        }
        let Some(rule) = rec.rules.first() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(&rule.ctor) else {
            return Ok(None);
        };
        let Some(selected) = rec.all.iter().position(|name| name == &ctor.induct) else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(family)) = self.environment.find(&ctor.induct) else {
            return Ok(None);
        };
        if (family.is_rec || rec.num_indices != 0) && rec.all.len() == 1 {
            // The recursive paths flatten motives into recursive parameters.
            return Ok(None);
        }
        let parameters = rec.num_params as usize;
        let arity = parameters
            .checked_add(rec.num_minors as usize)
            .and_then(|n| n.checked_add(rec.num_motives as usize))
            .and_then(|n| n.checked_add(rec.num_indices as usize))
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| unsupported("eliminator arity"))?;
        if args.len() <= arity {
            return Ok(None);
        }
        // Apply only the static motive to recover the result annotation.
        // Its logical dependence on scalar indices (including the major of a
        // Bool case) can disappear after representation erasure. The original
        // recursor application below still evaluates all actual arguments.
        let mut type_ = args[parameters + selected].clone();
        for arg in &args[arity - 1 - rec.num_indices as usize..arity] {
            self.tick()?;
            type_ = self.minor_apply(type_, arg.clone())?;
        }
        let type_ = self.erase_runtime_type(&type_)?;
        let mut function = head.clone();
        for argument in &args[..arity] {
            self.tick()?;
            function = Expr::app(function, argument.clone());
        }
        let mut body = Expr::bvar(0).map_err(|_| unsupported("eliminator result scope"))?;
        for argument in &args[arity..] {
            self.tick()?;
            body = Expr::app(body, self.lift(argument, 1)?);
        }
        Ok(Some(Expr::let_e(
            Name::anonymous(),
            type_,
            function,
            body,
            false,
        )))
    }

    /// A function-valued minor can be a literal lambda. Retain its checked
    /// motive as a local type so ordinary closure conversion owns its captures.
    pub(super) fn typed_callable_result(
        &mut self,
        value: Expr,
        type_: Expr,
        result: ValueType,
    ) -> Result<Expr, IngressError> {
        if !matches!(result, ValueType::Closure(_)) {
            return Ok(value);
        }
        // Source case elaboration can retain constructor aliases as leading
        // lets. Place the annotation at their result, not outside the whole
        // telescope; otherwise a literal result lambda has no local type when
        // the ordinary closure converter visits it. All strict lets survive.
        let mut value = value;
        let mut bindings = Vec::new();
        loop {
            self.tick()?;
            match value.node() {
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value: local,
                    body,
                    non_dep,
                } => {
                    reserve(&mut bindings, self.limits.max_context_depth)?;
                    bindings.push((decl_name.clone(), type_.clone(), local.clone(), *non_dep));
                    value = body.clone();
                }
                ExprNode::MData { expr, .. } => value = expr.clone(),
                _ => break,
            }
        }
        let depth =
            u32::try_from(bindings.len()).map_err(|_| unsupported("branch result depth"))?;
        let mut result = Expr::let_e(
            Name::anonymous(),
            self.lift(&type_, depth)?,
            value,
            Expr::bvar(0).map_err(|_| unsupported("branch result scope"))?,
            false,
        );
        for (name, type_, value, nondep) in bindings.into_iter().rev() {
            self.tick()?;
            result = Expr::let_e(name, type_, value, result, nondep);
        }
        Ok(result)
    }

    /// A real lambda spine may end before its Pi telescope: applying that
    /// prefix computes a callback, rather than consuming all of its arguments.
    /// Retain the suffix type inside the prefix, before visiting its body. A
    /// strict let between stages must not be eta-expanded across the boundary.
    pub(super) fn annotate_callable_tail(
        &mut self,
        value: &Expr,
        type_: &Expr,
    ) -> Result<Expr, IngressError> {
        if !matches!(value.node(), ExprNode::Lam { .. }) {
            return Ok(value.clone());
        }
        let mut body = value.clone();
        let mut result_type = self.normalize_type(type_)?;
        let mut binders = Vec::new();
        while let (
            ExprNode::Lam {
                binder_name,
                binder_type,
                body: next_body,
                binder_info,
            },
            ExprNode::ForallE {
                binder_type: domain,
                body: next_type,
                ..
            },
        ) = (body.node(), result_type.node())
        {
            self.tick()?;
            if self.normalize_type(binder_type)? != self.normalize_type(domain)? {
                return Ok(value.clone());
            }
            reserve(&mut binders, self.limits.max_context_depth)?;
            binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
            body = next_body.clone();
            result_type = next_type.clone();
        }
        if binders.is_empty() || !matches!(result_type.node(), ExprNode::ForallE { .. }) {
            return Ok(value.clone());
        }
        let Some(result @ ValueType::Closure(_)) = self.value_type(&result_type)? else {
            return Ok(value.clone());
        };
        body = self.typed_callable_result(body, result_type, result)?;
        for (name, type_, info) in binders.into_iter().rev() {
            self.tick()?;
            body = Expr::lam(name, type_, body, info);
        }
        Ok(body)
    }

    /// Register an interface after the shared data/function worklist has
    /// resolved all of its dependencies. Discovery never reenters itself.
    pub(super) fn register_function_type(
        &mut self,
        source: Expr,
        parameters: Vec<ValueType>,
        result: ValueType,
    ) -> Result<ValueType, IngressError> {
        reserve(&mut self.interfaces, self.limits.fir.max_closure_types)?;
        let id = u32::try_from(self.interfaces.len())
            .map_err(|_| unsupported("callback interface identity"))?;
        self.interfaces.push(ClosureSignature {
            parameter_ownership: borrowed_runtime_parameters(parameters.len())?,
            parameters,
            result,
            result_ownership: result_ownership(result),
        });
        let value = ValueType::Closure(ClosureTypeId::new(id));
        self.value_types
            .closures
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.value_types.closures.len().saturating_add(1),
            })?;
        self.value_types.closures.insert(source, value);
        Ok(value)
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
        // Object fields participate in the very same canonical interface
        // table as calls and lambdas. Discovery order is not a runtime ABI.
        for constructor in &mut self.constructors {
            for field in &mut constructor.fields {
                charge_catalog_node(&mut self.visited, self.limits)?;
                *field = remap_type(*field, &ranks)?;
            }
        }
        for case in &mut self.cases {
            case.result = remap_type(case.result, &ranks)?;
        }
        for case in &mut self.variant_cases {
            case.result = remap_type(case.result, &ranks)?;
        }
        for case in &mut self.empty_cases {
            case.result = remap_type(case.result, &ranks)?;
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
