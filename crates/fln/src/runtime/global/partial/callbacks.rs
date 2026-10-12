//! Preserve a known callback's real application stages through a recursive
//! Partial consumer. Only its interface is specialized; its value and captures
//! remain ordinary runtime operands. Every self edge must forward those exact
//! parameters, and the cloned body still passes ordinary catalog/FIR checking.
use super::*;
use fln_comp::ingress::ClosureSignature;
use fln_env::constants::{ConstantVal, ReducibilityHints};

impl Preparation<'_> {
    pub(super) fn partial_callback_stage(
        &mut self,
        origin: &Name,
        entry: Entry,
        arguments: &[Expr],
    ) -> Result<Entry, IngressError> {
        let mut parameters = entry.parameter_types.clone();
        let mut selected = Vec::new();
        for (index, (parameter, argument)) in entry.parameters.iter().zip(arguments).enumerate() {
            self.tick()?;
            if !matches!(parameters[index], ValueType::Closure(_)) {
                continue;
            }
            let Some(literal) = self.inert_callable(argument)? else {
                continue;
            };
            let literal = self.administrative_callable_value(&literal)?;
            let definition = DefinitionVal {
                base: ConstantVal {
                    name: Name::anonymous(),
                    level_params: Vec::new(),
                    type_: parameter.type_.clone(),
                },
                value: literal,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: Vec::new(),
            };
            let Some(signature) = self.signature(&definition, false)? else {
                continue;
            };
            if signature.parameters.is_empty() {
                continue;
            }
            let actual = self.stage_interface(ClosureSignature {
                parameter_ownership: borrowed_runtime_parameters(signature.parameters.len())?,
                parameters: signature.parameters,
                result: signature.result,
                result_ownership: signature.result_ownership,
            })?;
            if actual == parameters[index] {
                continue;
            }
            if !self.same_stage_telescope(actual, parameters[index])? {
                return Err(unsupported("partial callback telescope"));
            }
            reserve(&mut selected, self.limits.max_context_depth)?;
            selected.push(index);
            parameters[index] = actual;
        }
        if selected.is_empty() {
            return Ok(entry);
        }
        let key = (origin.clone(), parameters.clone());
        if let Some(index) = self.partial_stages.callbacks.get(&key) {
            return Ok(self.partial_stages.entries[*index].clone());
        }

        // Static specialization retains the admitted executable provenance.
        // Restrict this extension to one complete recursive member: routing a
        // peer through its old flat ABI would lose the callback's real stages.
        let source = self.partial_callback_origin(origin)?;
        let Some(definition) = self.executable_definition(&source)? else {
            return Err(unsupported("partial callback executable origin"));
        };
        if definition.safety != DefinitionSafety::Partial
            || definition.base.name != source
            || definition.all.as_slice() != std::slice::from_ref(&source)
        {
            return Err(unsupported("partial callback recursive group"));
        }
        let observed = self.partial_stages.entries.len().saturating_add(1);
        if observed > self.limits.fir.max_functions {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ProgramTables,
                limit: self.limits.fir.max_functions,
                observed,
            });
        }
        let serial = u64::try_from(self.partial_stages.entries.len())
            .map_err(|_| unsupported("partial callback identity"))?;
        let name = Name::num(name_of_stages(), serial);
        if self.environment.contains(&name) || self.has_private_callable(&name) {
            return Err(unsupported("partial stage name collision"));
        }
        let mut specialized = entry;
        specialized.name = name.clone();
        specialized.parameter_types = parameters;
        specialized.body = self.partial_callback_body(&specialized, origin, &source, &selected)?;

        // No private executable is published until every recursive forwarding
        // edge and the complete bounded body traversal have succeeded.
        reserve(
            &mut self.partial_stages.entries,
            self.limits.fir.max_functions,
        )?;
        self.partial_stages.callbacks.try_reserve(1).map_err(|_| {
            IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: observed,
            }
        })?;
        self.partial_stages
            .names
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: observed,
            })?;
        let index = self.partial_stages.entries.len();
        self.partial_stages.callbacks.insert(key, index);
        self.partial_stages.names.insert(name, index);
        self.partial_stages.entries.push(specialized.clone());
        Ok(specialized)
    }

    /// Follow only recorded static-specialization edges. Runtime values never
    /// enter those keys and therefore never become embedded callback captures.
    fn partial_callback_origin(&mut self, name: &Name) -> Result<Name, IngressError> {
        let mut current = name.clone();
        let mut seen = HashSet::new();
        loop {
            self.tick()?;
            if self.environment.contains(&current) {
                return Ok(current);
            }
            seen.try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: seen.len().saturating_add(1),
                })?;
            if !seen.insert(current.clone()) {
                return Err(unsupported("cyclic partial callback origin"));
            }
            let mut previous = None;
            for ((origin, _, _), selected) in &self.specializations.instances {
                charge_catalog_node(&mut self.visited, self.limits)?;
                if selected == &current && previous.replace(origin.clone()).is_some() {
                    return Err(unsupported("ambiguous partial callback origin"));
                }
            }
            let Some(previous) = previous else {
                return Ok(current);
            };
            current = previous;
        }
    }

    /// Resolve the same checked attribute/static-argument path used at the
    /// original call. A recursive call selecting different static arguments
    /// cannot silently enter the unspecialized callback ABI.
    fn partial_callback_recursion(
        &mut self,
        expression: &Expr,
        origin: &Name,
        source: &Name,
    ) -> Result<Option<Vec<Expr>>, IngressError> {
        let (head, _) = self.spine(expression)?;
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        let Some(definition) = self.executable_definition(name)? else {
            return Ok(None);
        };
        if self.partial_callback_origin(&definition.base.name)? != *source {
            return Ok(None);
        }
        let mut expression = expression.clone();
        loop {
            self.tick()?;
            let (head, arguments) = self.spine(&expression)?;
            if matches!(head.node(), ExprNode::Const { name, levels }
                if name == origin && levels.is_empty())
            {
                return Ok(Some(arguments));
            }
            let next = match self.implemented_by_call(&head, &arguments)? {
                Some(next) => Some(next),
                None => self.specialize_call(&head, &arguments)?,
            };
            let Some(next) = next else {
                return Err(unsupported("partial callback recursive specialization"));
            };
            if next == expression {
                return Err(unsupported("partial callback recursive specialization"));
            }
            expression = next;
        }
    }

    fn partial_callback_body(
        &mut self,
        entry: &Entry,
        origin: &Name,
        source: &Name,
        selected: &[usize],
    ) -> Result<Expr, IngressError> {
        enum Work {
            Visit(Expr, usize),
            Apply(usize, bool),
            Lam(Name, Expr, BinderInfo),
            Let(Name, Expr, bool),
            Proj(Name, u64),
            Metadata(KVMap),
        }
        let mut work = vec![Work::Visit(entry.body.clone(), 0)];
        let mut values = Vec::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Work::Visit(expression, depth) => {
                    if matches!(
                        expression.node(),
                        ExprNode::App { .. } | ExprNode::Const { .. }
                    ) && let Some(arguments) =
                        self.partial_callback_recursion(&expression, origin, source)?
                    {
                        for &position in selected {
                            self.tick()?;
                            let expected = entry
                                .parameters
                                .len()
                                .checked_sub(position.saturating_add(1))
                                .and_then(|slot| slot.checked_add(depth))
                                .ok_or_else(|| unsupported("partial callback forwarding scope"))?;
                            let mut argument = arguments.get(position).ok_or_else(|| {
                                unsupported("partial callback recursive forwarding")
                            })?;
                            while let ExprNode::MData { expr, .. } = argument.node() {
                                self.tick()?;
                                argument = expr;
                            }
                            if !matches!(argument.node(), ExprNode::BVar { idx }
                                if usize::try_from(*idx).ok() == Some(expected))
                            {
                                return Err(unsupported("partial callback recursive forwarding"));
                            }
                        }
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Apply(arguments.len(), true));
                        for argument in arguments.into_iter().rev() {
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Visit(argument, depth));
                        }
                        continue;
                    }
                    match expression.node() {
                        ExprNode::App { .. } => {
                            let (head, arguments) = self.spine(&expression)?;
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Apply(arguments.len(), false));
                            for argument in arguments.into_iter().rev() {
                                reserve(&mut work, self.limits.max_nodes)?;
                                work.push(Work::Visit(argument, depth));
                            }
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Visit(head, depth));
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            let nested = depth.saturating_add(1);
                            self.producer_depth(nested)?;
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Lam(
                                binder_name.clone(),
                                binder_type.clone(),
                                *binder_info,
                            ));
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Visit(body.clone(), nested));
                        }
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } => {
                            let nested = depth.saturating_add(1);
                            self.producer_depth(nested)?;
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Let(decl_name.clone(), type_.clone(), *non_dep));
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Visit(body.clone(), nested));
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Visit(value.clone(), depth));
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => {
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Proj(struct_name.clone(), *idx));
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Visit(expr.clone(), depth));
                        }
                        ExprNode::MData { data, expr } => {
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Metadata(data.clone()));
                            reserve(&mut work, self.limits.max_nodes)?;
                            work.push(Work::Visit(expr.clone(), depth));
                        }
                        _ => {
                            reserve(&mut values, self.limits.max_nodes)?;
                            values.push(expression);
                        }
                    }
                }
                Work::Apply(count, recursive) => {
                    let width = count.saturating_add(usize::from(!recursive));
                    let start = values
                        .len()
                        .checked_sub(width)
                        .ok_or_else(|| unsupported("partial callback application stack"))?;
                    let mut parts = values.drain(start..);
                    let value = if recursive {
                        let mut arguments = Vec::new();
                        arguments.try_reserve_exact(count).map_err(|_| {
                            IngressError::AllocationFailure {
                                resource: IngressResource::ProgramTables,
                                requested: count,
                            }
                        })?;
                        arguments.extend(parts);
                        self.apply_partial_stage(entry, &arguments)?
                            .ok_or_else(|| unsupported("partial callback recursive application"))?
                    } else {
                        let head = parts
                            .next()
                            .ok_or_else(|| unsupported("partial callback application head"))?;
                        parts.fold(head, Expr::app)
                    };
                    reserve(&mut values, self.limits.max_nodes)?;
                    values.push(value);
                }
                Work::Lam(name, type_, info) => {
                    let body = pop(&mut values)?;
                    values.push(Expr::lam(name, type_, body, info));
                }
                Work::Let(name, type_, non_dep) => {
                    let body = pop(&mut values)?;
                    let value = pop(&mut values)?;
                    values.push(Expr::let_e(name, type_, value, body, non_dep));
                }
                Work::Proj(name, index) => {
                    let value = pop(&mut values)?;
                    values.push(Expr::proj(name, index, value));
                }
                Work::Metadata(data) => {
                    let value = pop(&mut values)?;
                    values.push(Expr::mdata(data, value));
                }
            }
        }
        if values.len() != 1 {
            return Err(unsupported("partial callback body stack"));
        }
        pop(&mut values)
    }
}
