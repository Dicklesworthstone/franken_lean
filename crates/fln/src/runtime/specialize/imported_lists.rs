//! Reduce an admitted List course-of-values call to its observable fold.
//!
//! The complete logical scaffold is checked before this transformation. Both
//! branches are derived from the actual functional, including its callbacks;
//! no library operation is replaced by a seed body. A symbolic tail stands
//! for the inaccessible rest of the history. Reduction succeeds only when all
//! such symbols disappear, so escaping or deeper history remains unsupported.
use super::*;
use fln_core::expr::FVarId;

enum Work {
    Visit(Expr),
    Apply(usize),
    Lambda(Name, Expr, BinderInfo),
    Let(Name, Expr, bool),
    Projection(Name, u64),
}

fn named(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn constant(label: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(named(label), levels)
}

fn variable(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("List history binder scope"))
}

impl Preparation<'_> {
    pub(in crate::runtime) fn imported_list_recursion(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        if name != &named("List.brecOn")
            || levels.len() != 2
            || levels
                .iter()
                .any(|level| level.has_param() || level.has_mvar())
            || args.len() < 4
            || !closed(&args[0])
            || !closed(&args[1])
            || args.iter().any(Expr::has_fvar)
        {
            return Ok(None);
        }
        if !self.specializations.list_recursion_checked {
            if !crate::source_intrinsics::imported_list_recursion_matches(
                self.environment,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            self.specializations.list_recursion_checked = true;
        }
        let family = Expr::app(constant("List", vec![levels[1].clone()]), args[0].clone());
        // Static element types can carry metadata from a caller. Compare both
        // motive domains after the same type erasure, while retaining the
        // original family and operands in the emitted fold.
        let motive_family = self.erase_runtime_type(&family)?;
        let Some(result_type) = self.indexed_motive(&args[1], &[], &motive_family)? else {
            return Ok(None);
        };
        if self.value_type(&result_type)?.is_none() {
            return Ok(None);
        }
        // A literal lambda or an inert, already applied function prefix may be
        // copied into the two branches. A computation producing a callback is
        // never run, moved, duplicated, or discarded by this transformation.
        let marker = FVarId(named("_fln_runtime_unobserved_list_history"));
        let functional = self.list_history_reduce(&args[3], &marker)?;
        if !self.list_history_inert(&functional)? {
            return Ok(None);
        }
        let storage = Level::max(
            levels[1]
                .clone()
                .succ()
                .map_err(|_| unsupported("List history universe"))?,
            levels[0].clone(),
        )
        .map_err(|_| unsupported("List history universe"))?;
        let empty = Expr::app(
            constant("List.nil", vec![levels[1].clone()]),
            args[0].clone(),
        );
        let first = self.list_history_reduce(
            &application(
                functional.clone(),
                [empty, constant("PUnit.unit", vec![storage.clone()])],
            ),
            &marker,
        )?;
        let cons = application(
            constant("List.cons", vec![levels[1].clone()]),
            [args[0].clone(), variable(2)?, variable(1)?],
        );
        let previous_type = application(
            constant("List.below", levels.clone()),
            [args[0].clone(), args[1].clone(), variable(1)?],
        );
        let previous = application(
            constant("PProd.mk", vec![levels[0].clone(), storage]),
            [
                result_type.clone(),
                previous_type,
                variable(0)?,
                Expr::fvar(marker.clone()),
            ],
        );
        let lifted_functional = self.lift(&functional, 3)?;
        let step =
            self.list_history_reduce(&application(lifted_functional, [cons, previous]), &marker)?;
        if first.has_fvar() || step.has_fvar() {
            return Err(unsupported("List course-of-values history escapes"));
        }
        let step = Expr::lam(
            Name::anonymous(),
            args[0].clone(),
            Expr::lam(
                Name::anonymous(),
                family.clone(),
                Expr::lam(
                    Name::anonymous(),
                    result_type.clone(),
                    step,
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let motive = Expr::lam(Name::anonymous(), family, result_type, BinderInfo::Default);
        let fold = application(
            constant("List.rec", levels.clone()),
            [args[0].clone(), motive, first, step, args[2].clone()],
        );
        // History reduction can expose projections below fresh binders.
        // Select their ground layouts while the fold still contains that
        // telescope, before callable extraction removes its source context.
        let fold = self.lower_projections(&fold)?;
        Ok(Some(application(fold, args[4..].iter().cloned())))
    }

    /// Open variables denote values already bound by the caller. Constructor
    /// fields must all be inert; selecting a field cannot erase strict work in
    /// another field. Definitions are followed only to expose an inert value.
    fn list_history_inert(&mut self, source: &Expr) -> Result<bool, IngressError> {
        let mut work = vec![source.clone()];
        while let Some(expression) = work.pop() {
            self.tick()?;
            let (head, args) = self.spine(&expression)?;
            match head.node() {
                ExprNode::BVar { .. }
                | ExprNode::FVar { .. }
                | ExprNode::Lam { .. }
                | ExprNode::ForallE { .. }
                | ExprNode::Sort { .. }
                | ExprNode::Lit { .. }
                    if args.is_empty() => {}
                ExprNode::Const { name, levels } => match self.environment.find(name) {
                    Some(ConstantInfo::Induct(family))
                        if !family.is_unsafe && levels.len() == family.base.level_params.len() => {}
                    Some(ConstantInfo::Ctor(ctor))
                        if !ctor.is_unsafe
                            && levels.len() == ctor.base.level_params.len()
                            && args.len()
                                <= ctor.num_params as usize + ctor.num_fields as usize =>
                    {
                        let mut telescope = self.universe_instance(
                            &ctor.base.type_,
                            &ctor.base.level_params,
                            levels,
                        )?;
                        for argument in args {
                            let normal = self.type_head(&telescope)?;
                            let ExprNode::ForallE {
                                binder_type, body, ..
                            } = normal.node()
                            else {
                                return Ok(false);
                            };
                            // Types are inert metadata even when they mention
                            // the symbolic tail. Value parameters and every
                            // executable field still require an inert value.
                            if !self.type_parameter(binder_type)? {
                                reserve(&mut work, self.limits.max_nodes)?;
                                work.push(argument.clone());
                            }
                            telescope = self.substitution(body, &argument)?;
                        }
                    }
                    Some(ConstantInfo::Defn(definition))
                        if args.is_empty()
                            && definition.safety == DefinitionSafety::Safe
                            && levels.len() == definition.base.level_params.len() =>
                    {
                        let value = self.universe_instance(
                            &definition.value,
                            &definition.base.level_params,
                            levels,
                        )?;
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(value);
                    }
                    _ => return Ok(false),
                },
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn list_history_type(&mut self, source: &Expr) -> Result<bool, IngressError> {
        let mut work = vec![source.clone()];
        while let Some(expression) = work.pop() {
            self.tick()?;
            let mut push = |child: &Expr| -> Result<(), IngressError> {
                reserve(&mut work, self.limits.max_nodes)?;
                work.push(child.clone());
                Ok(())
            };
            match expression.node() {
                ExprNode::Const { name, .. } if name == &named("List.below") => return Ok(true),
                ExprNode::App { f, a } => {
                    push(f)?;
                    push(a)?;
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    push(binder_type)?;
                    push(body)?;
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    push(type_)?;
                    push(value)?;
                    push(body)?;
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => push(expr)?,
                _ => {}
            }
        }
        Ok(false)
    }

    /// One administrative reduction. Ordinary callback computations are left
    /// as code. Only safe wrappers whose telescope or arguments mention the
    /// checked history family are unfolded. Every beta/zeta operand is inert.
    fn list_history_step(
        &mut self,
        source: &Expr,
        marker: &FVarId,
    ) -> Result<Option<Expr>, IngressError> {
        match source.node() {
            ExprNode::MData { expr, .. } => return Ok(Some(expr.clone())),
            ExprNode::LetE { value, body, .. } if self.list_history_inert(value)? => {
                return self.substitution(body, value).map(Some);
            }
            ExprNode::Proj { expr, .. } if self.list_history_inert(expr)? => {
                let (head, mut args) = self.spine(expr)?;
                args.reverse();
                return Ok(self.projected_field(source, &head, &args));
            }
            _ => {}
        }
        let (head, args) = self.spine(source)?;
        if let ExprNode::Lam { body, .. } = head.node()
            && let Some(argument) = args.first()
            && self.list_history_inert(argument)?
        {
            let body = self.substitution(body, argument)?;
            return Ok(Some(application(body, args[1..].iter().cloned())));
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        if name == &named("List.rec") && levels.len() == 2 && args.len() >= 5 {
            let (constructor, fields) = self.spine(&args[4])?;
            if let ExprNode::Const {
                name: ctor,
                levels: ctor_levels,
            } = constructor.node()
                && ctor_levels.as_slice() == &levels[1..]
                && fields.first() == args.first()
                && self.list_history_inert(&args[4])?
            {
                let branch = if ctor == &named("List.nil") && fields.len() == 1 {
                    Some(args[2].clone())
                } else if ctor == &named("List.cons") && fields.len() == 3 {
                    // The canonical recursor's recursive result is unnecessary
                    // for a constructor case. Retain a refusal symbol if its
                    // minor observes that result instead of inventing a value.
                    Some(application(
                        args[3].clone(),
                        [
                            fields[1].clone(),
                            fields[2].clone(),
                            Expr::fvar(marker.clone()),
                        ],
                    ))
                } else {
                    None
                };
                if let Some(branch) = branch {
                    return Ok(Some(application(branch, args[5..].iter().cloned())));
                }
            }
            return Ok(None);
        }
        if ["List.below", "List.brecOn", "List.brecOn.go"]
            .iter()
            .any(|label| name == &named(label))
        {
            return Ok(None);
        }
        let Some(definition) = self.definition(name) else {
            return Ok(None);
        };
        if definition.safety != DefinitionSafety::Safe
            || definition.base.level_params.len() != levels.len()
        {
            return Ok(None);
        }
        let mut related = self.list_history_type(&definition.base.type_)?;
        for argument in &args {
            if related {
                break;
            }
            related = self.list_history_type(argument)?;
        }
        if !related {
            return Ok(None);
        }
        let body =
            self.universe_instance(&definition.value, &definition.base.level_params, levels)?;
        Ok(Some(application(body, args)))
    }

    /// An explicit worklist bounds both repeated reduction and reconstruction.
    /// Types are preserved as annotations; no dependent layout is manufactured.
    fn list_history_reduce(
        &mut self,
        source: &Expr,
        marker: &FVarId,
    ) -> Result<Expr, IngressError> {
        let mut work = vec![Work::Visit(source.clone())];
        let mut values = Vec::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            reserve(&mut values, self.limits.max_nodes)?;
            let rebuilt = match task {
                Work::Visit(expression) => {
                    if let Some(reduced) = self.list_history_step(&expression, marker)? {
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Visit(reduced));
                        continue;
                    }
                    let limit = self.limits.max_nodes;
                    let mut push = |task| -> Result<(), IngressError> {
                        reserve(&mut work, limit)?;
                        work.push(task);
                        Ok(())
                    };
                    match expression.node() {
                        ExprNode::App { .. } => {
                            let (head, args) = self.spine(&expression)?;
                            push(Work::Apply(args.len()))?;
                            for arg in args.into_iter().rev() {
                                push(Work::Visit(arg))?;
                            }
                            push(Work::Visit(head))?;
                        }
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => {
                            push(Work::Lambda(
                                binder_name.clone(),
                                binder_type.clone(),
                                *binder_info,
                            ))?;
                            push(Work::Visit(body.clone()))?;
                        }
                        ExprNode::LetE {
                            decl_name,
                            type_,
                            value,
                            body,
                            non_dep,
                        } => {
                            push(Work::Let(decl_name.clone(), type_.clone(), *non_dep))?;
                            push(Work::Visit(body.clone()))?;
                            push(Work::Visit(value.clone()))?;
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => {
                            push(Work::Projection(struct_name.clone(), *idx))?;
                            push(Work::Visit(expr.clone()))?;
                        }
                        _ => values.push(expression),
                    }
                    continue;
                }
                Work::Apply(count) => {
                    let start = values
                        .len()
                        .checked_sub(count.saturating_add(1))
                        .ok_or_else(|| unsupported("List history application stack"))?;
                    let mut arguments = values.drain(start..);
                    let head = arguments
                        .next()
                        .ok_or_else(|| unsupported("List history application head"))?;
                    application(head, arguments)
                }
                Work::Lambda(name, type_, info) => {
                    let body = values
                        .pop()
                        .ok_or_else(|| unsupported("List history lambda stack"))?;
                    Expr::lam(name, type_, body, info)
                }
                Work::Let(name, type_, nondep) => {
                    let body = values
                        .pop()
                        .ok_or_else(|| unsupported("List history let stack"))?;
                    let value = values
                        .pop()
                        .ok_or_else(|| unsupported("List history let value"))?;
                    Expr::let_e(name, type_, value, body, nondep)
                }
                Work::Projection(name, index) => {
                    let value = values
                        .pop()
                        .ok_or_else(|| unsupported("List history projection stack"))?;
                    Expr::proj(name, index, value)
                }
            };
            if let Some(reduced) = self.list_history_step(&rebuilt, marker)? {
                reserve(&mut work, self.limits.max_nodes)?;
                work.push(Work::Visit(reduced));
            } else {
                values.push(rebuilt);
            }
        }
        if values.len() != 1 {
            return Err(unsupported("List history reduction result"));
        }
        values
            .pop()
            .ok_or_else(|| unsupported("List history reduction result"))
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod catalog_tests;
