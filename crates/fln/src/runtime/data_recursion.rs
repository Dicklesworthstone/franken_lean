//! Eliminate admitted direct-self recursive families through native closures.
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

fn variable(index: usize) -> Result<Expr, IngressError> {
    let index = u32::try_from(index).map_err(|_| unsupported("recursive data binder count"))?;
    Expr::bvar(index).map_err(|_| unsupported("recursive data binder scope"))
}

impl Preparation<'_> {
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
            || rec.num_params != 0
            || rec.num_indices != 0
            || rec.num_motives != 1
            || rec.num_minors == 0
            || rec.all.len() != 1
            || rec.rules.len() != rec.num_minors as usize
            || levels.len() != rec.base.level_params.len()
            || args.len() < rec.rules.len().saturating_add(2)
        {
            return Ok(None);
        }
        let Some(shape) = self.record_shape(&rec.all[0])? else {
            return Ok(None);
        };
        if !shape.recursive || shape.constructors.len() != rec.rules.len() {
            return Ok(None);
        }
        let family = Expr::const_(shape.name.clone(), vec![]);
        if self.value_type(&family)? != Some(ValueType::Constructor) {
            return Ok(None);
        }
        let ExprNode::Lam {
            binder_type,
            body: motive,
            ..
        } = args[0].node()
        else {
            return Ok(None);
        };
        if binder_type != &family {
            return Ok(None);
        }
        let mut domains = vec![family.clone()];
        let mut parameters = vec![ValueType::Constructor];
        let mut result_type = motive;
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
        let extra = parameters.len() - 1;
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
        for domain in domains[1..].iter().rev() {
            self.tick()?;
            hypothesis_type = Expr::forall_e(
                Name::anonymous(),
                domain.clone(),
                hypothesis_type,
                BinderInfo::Default,
            );
        }
        let self_type = Expr::forall_e(
            Name::anonymous(),
            family.clone(),
            hypothesis_type.clone(),
            BinderInfo::Default,
        );
        let major = variable(0)?;
        let mut branches = Vec::new();
        let mut constructors = Vec::new();
        for (index, (ctor, rule)) in shape.constructors.iter().zip(&rec.rules).enumerate() {
            self.tick()?;
            if rule.ctor != ctor.name || rule.nfields as usize != ctor.fields.len() {
                return Ok(None);
            }
            let mut body = args[index + 1]
                .lift_loose(0, lift)
                .map_err(|_| unsupported("recursive data minor scope"))?;
            let mut hypotheses = Vec::new();
            for (field_index, field_type) in ctor.fields.iter().enumerate() {
                self.tick()?;
                let field = Expr::proj(shape.projection(ctor), field_index as u64, major.clone());
                body = self.minor_apply(body, field.clone())?;
                if field_type == &family {
                    let marker = FVarId(Name::num(
                        Name::num(case_name.clone(), index as u64),
                        field_index as u64,
                    ));
                    reserve(&mut hypotheses, self.limits.max_context_depth)?;
                    hypotheses.push((marker, Expr::app(variable(extra + 2)?, field)));
                }
            }
            // The admitted recursor puts IHs after all constructor fields.
            for (marker, _) in &hypotheses {
                self.tick()?;
                body = self.minor_apply(body, Expr::fvar(marker.clone()))?;
            }
            for argument in (0..extra).rev() {
                body = self.minor_apply(body, variable(argument + 1)?)?;
            }
            for (marker, hypothesis) in hypotheses.into_iter().rev() {
                self.tick()?;
                let abstracted = body
                    .lift_loose(0, 1)
                    .and_then(|lifted| lifted.abstract_fvar(&marker, 0))
                    .map_err(|_| unsupported("recursive data hypothesis scope"))?;
                // Every preexisting loose index was lifted; a new loose #0
                // can only be this marker. Check individually so an ignored
                // child is not forced merely because another child is used.
                if abstracted.has_loose_bvar(0) {
                    body = Expr::let_e(
                        marker.0,
                        hypothesis_type.clone(),
                        hypothesis,
                        abstracted,
                        false,
                    );
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
