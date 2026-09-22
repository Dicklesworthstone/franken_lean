//! Eliminate admitted self-recursive families through native closures.
//! Constructor branches are lazy; each used induction hypothesis is shared in
//! an ordinary let, while an unused hypothesis never traverses its subtree.
use super::*;
use fln_core::expr::FVarId;
use fln_core::level::Level;

pub(super) struct Recursion {
    pub name: Name,
    pub self_type: Expr,
    pub domains: Vec<Expr>,
    pub parameters: Vec<ValueType>,
    pub case: variants::Case,
    pub arguments: Vec<Expr>,
}

/// A positive recursive field may return a family after taking ordinary runtime
/// arguments. The field itself stays an owned closure; no child is selected or
/// evaluated while building its layout or induction-hypothesis closure.
pub(super) struct RecursiveField {
    pub target: usize,
    binders: Vec<(Name, Expr, BinderInfo)>,
}

fn variable(index: usize) -> Result<Expr, IngressError> {
    let index = u32::try_from(index).map_err(|_| unsupported("recursive data binder count"))?;
    Expr::bvar(index).map_err(|_| unsupported("recursive data binder scope"))
}

impl Preparation<'_> {
    pub(super) fn recursive_field(
        &mut self,
        type_: &Expr,
        families: &[Expr],
    ) -> Result<Option<RecursiveField>, IngressError> {
        let mut result = type_;
        let mut binders = Vec::new();
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = result.node()
        {
            self.tick()?;
            if body.has_loose_bvars() {
                return Ok(None);
            }
            reserve(&mut binders, self.limits.max_context_depth)?;
            binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
            result = body;
        }
        for (target, family) in families.iter().enumerate() {
            self.tick()?;
            if result == family {
                return Ok(Some(RecursiveField { target, binders }));
            }
        }
        Ok(None)
    }

    pub(super) fn recursive_hypothesis(
        &mut self,
        recursive: &RecursiveField,
        callee: Expr,
        field: Expr,
        result_type: &Expr,
    ) -> Result<(Expr, Expr), IngressError> {
        if recursive.binders.is_empty() {
            return Ok((Expr::app(callee, field), result_type.clone()));
        }
        let mut binders = recursive.binders.clone();
        let mut result = result_type;
        // The native callable interface is flat. Give this generated closure
        // real binders for every accumulator too, rather than registering a
        // longer signature against a shorter lambda spine. This does not eta
        // expand arbitrary user closures or evaluate the child early.
        while let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = result.node()
        {
            self.tick()?;
            if body.has_loose_bvars() {
                return Err(unsupported("dependent recursive child result"));
            }
            reserve(&mut binders, self.limits.max_context_depth)?;
            binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
            result = body;
        }
        let count = binders.len();
        let extra = count - recursive.binders.len();
        let depth = u32::try_from(count).map_err(|_| unsupported("recursive child arity"))?;
        let mut child = self.lift(&field, depth)?;
        for argument in (extra..count).rev() {
            self.tick()?;
            child = Expr::app(child, variable(argument)?);
        }
        let mut body = Expr::app(self.lift(&callee, depth)?, child);
        for argument in (0..extra).rev() {
            self.tick()?;
            body = Expr::app(body, variable(argument)?);
        }
        let mut type_ = self.lift(result, depth)?;
        for (name, domain, info) in binders.iter().rev() {
            self.tick()?;
            body = Expr::lam(name.clone(), domain.clone(), body, *info);
            type_ = Expr::forall_e(name.clone(), domain.clone(), type_, *info);
        }
        Ok((body, type_))
    }

    pub(super) fn data_recursion(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<Recursion>, IngressError> {
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(name) else {
            return Ok(None);
        };
        if rec.is_unsafe
            || rec.num_motives != 1
            || rec.num_minors == 0
            || rec.all.len() != 1
            || rec.rules.len() != rec.num_minors as usize
            || levels.len() != rec.base.level_params.len()
            || args.len()
                < rec
                    .rules
                    .len()
                    .saturating_add(rec.num_params as usize)
                    .saturating_add(rec.num_indices as usize)
                    .saturating_add(2)
        {
            return Ok(None);
        }
        let Some(shape) = self.recursor_shape(rec, levels, args)? else {
            return Ok(None);
        };
        if (!shape.recursive && rec.num_indices == 0) || shape.constructors.len() != rec.rules.len()
        {
            return Ok(None);
        }
        let family = shape.source.clone();
        let args = &args[rec.num_params as usize..];
        let (family_head, family_parameters) = self.spine(&family)?;
        let ExprNode::Const {
            name: family_name,
            levels: family_levels,
        } = family_head.node()
        else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(info)) = self.environment.find(family_name) else {
            return Ok(None);
        };
        let Some(mut domains) = self.index_domains(info, family_levels, &family_parameters)? else {
            return Ok(None);
        };
        let Some(motive) = self.indexed_motive(&args[0], &domains, &family)? else {
            return Ok(None);
        };
        let mut parameters = Vec::new();
        for domain in &domains {
            reserve(&mut parameters, self.limits.max_context_depth)?;
            parameters.push(
                self.value_type(domain)?
                    .ok_or_else(|| unsupported("index representation"))?,
            );
        }
        reserve(&mut domains, self.limits.max_context_depth)?;
        reserve(&mut parameters, self.limits.max_context_depth)?;
        domains.push(family.clone());
        parameters.push(ValueType::Constructor);
        let first_extra = domains.len();
        let mut result_type = &motive;
        loop {
            self.tick()?;
            match result_type.node() {
                ExprNode::MData { expr, .. } => result_type = expr,
                ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    let parameter = self
                        .value_type(binder_type)?
                        .ok_or_else(|| unsupported("dependent recursive data parameter"))?;
                    reserve(&mut domains, self.limits.max_context_depth)?;
                    reserve(&mut parameters, self.limits.max_context_depth)?;
                    domains.push(binder_type.clone());
                    parameters.push(parameter);
                    result_type = body;
                }
                _ => break,
            }
        }
        let result = self
            .value_type(result_type)?
            .ok_or_else(|| unsupported("dependent recursive data result"))?;
        let extra = parameters.len() - first_extra;
        let depth = parameters.len().saturating_add(2); // self, runtime arguments, branch major
        if depth > self.limits.max_context_depth {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: self.limits.max_context_depth,
                observed: depth,
            });
        }
        let lift = u32::try_from(depth).map_err(|_| unsupported("recursive data scope"))?;
        let id = self.next_variant;
        self.next_variant = id
            .checked_add(1)
            .ok_or_else(|| unsupported("recursive data identity"))?;
        let case_name = Name::num(super::name("_fln_runtime_variant_case"), id);
        if self.environment.contains(&case_name) {
            return Err(unsupported("runtime variant name collision"));
        }
        let mut hypothesis_type = result_type.clone();
        for domain in domains[first_extra..].iter().rev() {
            self.tick()?;
            hypothesis_type = Expr::forall_e(
                Name::anonymous(),
                domain.clone(),
                hypothesis_type,
                BinderInfo::Default,
            );
        }
        let mut self_type = hypothesis_type.clone();
        for domain in domains[..first_extra].iter().rev() {
            self.tick()?;
            self_type = Expr::forall_e(
                Name::anonymous(),
                domain.clone(),
                self_type,
                BinderInfo::Default,
            );
        }
        let major = variable(0)?;
        let mut branches = Vec::new();
        let mut constructors = Vec::new();
        for (index, (ctor, rule)) in shape.constructors.iter().zip(&rec.rules).enumerate() {
            self.tick()?;
            if rule.ctor != ctor.original || rule.nfields as usize != ctor.fields.len() {
                return Ok(None);
            }
            let mut body = args[index + 1]
                .lift_loose(0, lift)
                .map_err(|_| unsupported("recursive data minor scope"))?;
            let mut hypotheses = Vec::new();
            let mut logical_fields = self.indexed_constructor_telescope(&shape, ctor)?;
            for (field_index, field_type) in ctor.fields.iter().enumerate() {
                self.tick()?;
                let field = Expr::proj(shape.projection(ctor), field_index as u64, major.clone());
                body = self.minor_apply(body, field.clone())?;
                let logical = self.type_head(&logical_fields)?;
                let ExprNode::ForallE {
                    binder_type: logical_type,
                    body: next_field,
                    ..
                } = logical.node()
                else {
                    return Err(unsupported("indexed constructor field telescope"));
                };
                logical_fields = self.substitution(next_field, &field)?;
                if let Some(recursive) =
                    self.recursive_field(field_type, std::slice::from_ref(&family))?
                {
                    debug_assert_eq!(recursive.target, 0);
                    let marker = FVarId(Name::num(
                        Name::num(case_name.clone(), index as u64),
                        field_index as u64,
                    ));
                    reserve(&mut hypotheses, self.limits.max_context_depth)?;
                    let mut callee = variable(parameters.len() + 1)?;
                    if rec.num_indices != 0 {
                        let indices = self.indexed_field_arguments(
                            logical_type,
                            &family,
                            rec.num_indices as usize,
                        )?;
                        for index in indices {
                            self.tick()?;
                            callee = Expr::app(callee, index);
                        }
                    }
                    let (hypothesis, type_) =
                        self.recursive_hypothesis(&recursive, callee, field, &hypothesis_type)?;
                    hypotheses.push((marker, hypothesis, type_));
                }
            }
            // The admitted recursor puts IHs after all constructor fields.
            for (marker, _, _) in &hypotheses {
                self.tick()?;
                body = self.minor_apply(body, Expr::fvar(marker.clone()))?;
            }
            for argument in (0..extra).rev() {
                body = self.minor_apply(body, variable(argument + 1)?)?;
            }
            for (marker, hypothesis, type_) in hypotheses.into_iter().rev() {
                self.tick()?;
                let abstracted = body
                    .lift_loose(0, 1)
                    .and_then(|lifted| lifted.abstract_fvar(&marker, 0))
                    .map_err(|_| unsupported("recursive data hypothesis scope"))?;
                // Every preexisting loose index was lifted; a new loose #0
                // can only be this marker. Check individually so an ignored
                // child is not forced merely because another child is used.
                if abstracted.has_loose_bvar(0) {
                    body = Expr::let_e(marker.0, type_, hypothesis, abstracted, false);
                }
            }
            reserve(&mut branches, self.limits.max_lambda_bindings)?;
            branches.push(Expr::lam(
                Name::num(case_name.clone(), index as u64),
                family.clone(),
                body,
                BinderInfo::Default,
            ));
            reserve(&mut constructors, self.limits.fir.max_constructors)?;
            constructors.push(ctor.name.clone());
        }
        reserve(&mut self.variant_cases, self.limits.fir.max_functions)?;
        self.variant_cases.push(ConstructorCaseBinding {
            name: case_name.clone(),
            constructors,
            result,
        });
        let mut arguments = Vec::new();
        for arg in &args[rec.rules.len() + 1..] {
            reserve(&mut arguments, self.limits.max_application_args)?;
            arguments.push(arg.clone());
        }
        Ok(Some(Recursion {
            name: Name::num(super::name("_fln_runtime_data_rec"), id),
            self_type,
            domains,
            parameters,
            case: variants::Case {
                name: case_name,
                major: variable(extra)?,
                branches,
                result,
            },
            arguments,
        }))
    }
}
