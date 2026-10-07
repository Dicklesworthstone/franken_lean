//! Lower the admitted Nat course-of-values scaffold to its observable fold.
//!
//! Both branches come from the actual checked functional. Only its immediate
//! predecessor result is represented; a fresh symbol tracks every deeper or
//! escaping history use and causes a typed refusal. The complete logical Nat,
//! PUnit, PProd and recursion declarations must match the pinned model first.
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
    Expr::bvar(index).map_err(|_| unsupported("Nat history binder scope"))
}

impl Preparation<'_> {
    pub(in crate::runtime) fn imported_nat_recursion(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        if name != &named("Nat.brecOn")
            || levels.len() != 1
            || levels
                .iter()
                .any(|level| level.has_param() || level.has_mvar())
            || args.len() < 3
            || !closed(&args[0])
            || args.iter().any(Expr::has_fvar)
        {
            return Ok(None);
        }
        if !self.specializations.nat_recursion_checked {
            if !crate::source_intrinsics::imported_nat_recursion_matches(
                self.environment,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            self.specializations.nat_recursion_checked = true;
        }
        let family = constant("Nat", vec![]);
        let Some(result_type) = self.indexed_motive(&args[0], &[], &family)? else {
            return Ok(None);
        };
        // Nat.rec itself checks the complete first-order result telescope,
        // including motives returning a function with erased proof domains.
        let marker = FVarId(named("_fln_runtime_unobserved_nat_history"));
        let functional = self.nat_history_reduce(&args[2], &marker)?;
        // Unfolding the actual history functional exposes fresh proof terms.
        // Erase them while its original dependent history/proof telescope is
        // available, before the recursive result acquires its erased ABI.
        let functional = self.erase_proofs(&functional, None)?;
        if !self.nat_history_inert(&functional)? {
            return Ok(None);
        }
        let storage = Level::max(Level::one(), levels[0].clone())
            .map_err(|_| unsupported("Nat history universe"))?;
        let first = self.nat_history_reduce(
            &application(
                functional.clone(),
                [
                    constant("Nat.zero", vec![]),
                    constant("PUnit.unit", vec![storage.clone()]),
                ],
            ),
            &marker,
        )?;
        let predecessor = variable(1)?;
        let successor = Expr::app(constant("Nat.succ", vec![]), predecessor.clone());
        let previous_type = application(
            constant("Nat.below", levels.clone()),
            [args[0].clone(), predecessor],
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
        let lifted_functional = self.lift(&functional, 2)?;
        let step = self.nat_history_reduce(
            &application(lifted_functional, [successor, previous]),
            &marker,
        )?;
        if first.has_fvar() || step.has_fvar() {
            return Err(unsupported("Nat course-of-values history escapes"));
        }
        let step = Expr::lam(
            Name::anonymous(),
            family.clone(),
            Expr::lam(
                Name::anonymous(),
                result_type.clone(),
                step,
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let motive = Expr::lam(Name::anonymous(), family, result_type, BinderInfo::Default);
        let fold = application(
            constant("Nat.rec", levels.clone()),
            [motive, first, step, args[1].clone()],
        );
        Ok(Some(application(fold, args[3..].iter().cloned())))
    }

    /// Open variables denote values already bound by the caller. Constructor
    /// fields must all be inert; selecting a field cannot erase strict work in
    /// another field. Definitions are followed only to expose an inert value.
    fn nat_history_inert(&mut self, source: &Expr) -> Result<bool, IngressError> {
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

    fn nat_history_type(&mut self, source: &Expr) -> Result<bool, IngressError> {
        let mut work = vec![source.clone()];
        while let Some(expression) = work.pop() {
            self.tick()?;
            let mut push = |child: &Expr| -> Result<(), IngressError> {
                reserve(&mut work, self.limits.max_nodes)?;
                work.push(child.clone());
                Ok(())
            };
            match expression.node() {
                ExprNode::Const { name, .. } if name == &named("Nat.below") => return Ok(true),
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
    fn nat_history_step(
        &mut self,
        source: &Expr,
        marker: &FVarId,
    ) -> Result<Option<Expr>, IngressError> {
        match source.node() {
            ExprNode::MData { expr, .. } => return Ok(Some(expr.clone())),
            ExprNode::LetE { value, body, .. } if self.nat_history_inert(value)? => {
                return self.substitution(body, value).map(Some);
            }
            ExprNode::Proj { expr, .. } if self.nat_history_inert(expr)? => {
                let (head, mut args) = self.spine(expr)?;
                args.reverse();
                return Ok(self.projected_field(source, &head, &args));
            }
            _ => {}
        }
        let (head, args) = self.spine(source)?;
        if let ExprNode::Lam { body, .. } = head.node()
            && let Some(argument) = args.first()
            && self.nat_history_inert(argument)?
        {
            let body = self.substitution(body, argument)?;
            return Ok(Some(application(body, args[1..].iter().cloned())));
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        if name == &named("Nat.rec") && levels.len() == 1 && args.len() >= 4 {
            // Static branch selection may discard the other minor. Both
            // operands must already be values; a strict producer of a minor
            // must still execute even when its branch is not selected.
            if !self.nat_history_inert(&args[1])? || !self.nat_history_inert(&args[2])? {
                return Ok(None);
            }
            let (constructor, fields) = self.spine(&args[3])?;
            if let ExprNode::Const {
                name: ctor,
                levels: ctor_levels,
            } = constructor.node()
                && ctor_levels.is_empty()
                && self.nat_history_inert(&args[3])?
            {
                let branch = if ctor == &named("Nat.zero") && fields.is_empty() {
                    Some(args[1].clone())
                } else if ctor == &named("Nat.succ") && fields.len() == 1 {
                    // Constructor matching does not inspect this recursive
                    // result. Refuse if the actual minor observes it.
                    Some(application(
                        args[2].clone(),
                        [fields[0].clone(), Expr::fvar(marker.clone())],
                    ))
                } else {
                    None
                };
                if let Some(branch) = branch {
                    return Ok(Some(application(branch, args[4..].iter().cloned())));
                }
            }
            return Ok(None);
        }
        if ["Nat.below", "Nat.brecOn", "Nat.brecOn.go"]
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
        let mut related = self.nat_history_type(&definition.base.type_)?;
        if !related {
            // A generic matcher exposes history through its static motive.
            // A runtime operand merely containing a history projection must
            // not cause ordinary arithmetic or user callbacks to unfold.
            let mut telescope = self.universe_instance(
                &definition.base.type_,
                &definition.base.level_params,
                levels,
            )?;
            for argument in &args {
                let normal = self.type_head(&telescope)?;
                let ExprNode::ForallE {
                    binder_type, body, ..
                } = normal.node()
                else {
                    break;
                };
                if self.type_parameter(binder_type)? && self.nat_history_type(argument)? {
                    related = true;
                    break;
                }
                telescope = self.substitution(body, argument)?;
            }
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
    fn nat_history_reduce(&mut self, source: &Expr, marker: &FVarId) -> Result<Expr, IngressError> {
        let mut work = vec![Work::Visit(source.clone())];
        let mut values = Vec::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            reserve(&mut values, self.limits.max_nodes)?;
            let rebuilt = match task {
                Work::Visit(expression) => {
                    if let Some(reduced) = self.nat_history_step(&expression, marker)? {
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
                        .ok_or_else(|| unsupported("Nat history application stack"))?;
                    let mut arguments = values.drain(start..);
                    let head = arguments
                        .next()
                        .ok_or_else(|| unsupported("Nat history application head"))?;
                    application(head, arguments)
                }
                Work::Lambda(name, type_, info) => {
                    let body = values
                        .pop()
                        .ok_or_else(|| unsupported("Nat history lambda stack"))?;
                    Expr::lam(name, type_, body, info)
                }
                Work::Let(name, type_, nondep) => {
                    let body = values
                        .pop()
                        .ok_or_else(|| unsupported("Nat history let stack"))?;
                    let value = values
                        .pop()
                        .ok_or_else(|| unsupported("Nat history let value"))?;
                    Expr::let_e(name, type_, value, body, nondep)
                }
                Work::Projection(name, index) => {
                    let value = values
                        .pop()
                        .ok_or_else(|| unsupported("Nat history projection stack"))?;
                    Expr::proj(name, index, value)
                }
            };
            if let Some(reduced) = self.nat_history_step(&rebuilt, marker)? {
                reserve(&mut work, self.limits.max_nodes)?;
                work.push(Work::Visit(reduced));
            } else {
                values.push(rebuilt);
            }
        }
        if values.len() != 1 {
            return Err(unsupported("Nat history reduction result"));
        }
        values
            .pop()
            .ok_or_else(|| unsupported("Nat history reduction result"))
    }
}

#[cfg(test)]
mod tests;
