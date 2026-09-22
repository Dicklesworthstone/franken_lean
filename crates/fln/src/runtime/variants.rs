//! Native, lazy elimination of closed data variants. Layouts and eliminators
//! come from the admitted environment. Branch payloads are projected only after
//! the compiler's constructor tag/shape test selects that particular branch.
use super::*;
use fln_core::level::Level;

pub(super) struct Case {
    pub name: Name,
    pub major: Expr,
    pub branches: Vec<Expr>,
    pub result: ValueType,
}

impl Preparation<'_> {
    pub(super) fn variant_recursor(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<Case>, IngressError> {
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(name) else {
            return Ok(None);
        };
        if rec.is_unsafe
            || rec.num_indices != 0
            || rec.num_motives != 1
            || rec.num_minors < 2
            || rec.all.len() != 1
            || rec.rules.len() != rec.num_minors as usize
            || levels.len() != rec.base.level_params.len()
            || args.len()
                != rec
                    .rules
                    .len()
                    .saturating_add(rec.num_params as usize)
                    .saturating_add(2)
        {
            return Ok(None);
        }
        let Some(shape) = self.recursor_shape(rec, levels, args)? else {
            return Ok(None);
        };
        let family = shape.source.clone();
        let args = &args[rec.num_params as usize..];
        if shape.recursive || shape.constructors.len() != rec.rules.len() {
            return Ok(None);
        }
        let ExprNode::Lam { body: motive, .. } = args[0].node() else {
            return Ok(None);
        };
        let result = self
            .value_type(motive)?
            .ok_or_else(|| unsupported("dependent variant recursor result"))?;
        let id = self.next_variant;
        self.next_variant = id
            .checked_add(1)
            .ok_or_else(|| unsupported("variant identity"))?;
        let case_name = Name::num(super::name("_fln_runtime_variant_case"), id);
        if self.environment.contains(&case_name) {
            return Err(unsupported("runtime variant name collision"));
        }
        let major = Expr::bvar(0).map_err(|_| unsupported("variant major scope"))?;
        let mut branches = Vec::new();
        let mut constructors = Vec::new();
        for (index, (ctor, rule)) in shape.constructors.iter().zip(&rec.rules).enumerate() {
            self.tick()?;
            if rule.ctor != ctor.original || rule.nfields as usize != ctor.fields.len() {
                return Ok(None);
            }
            let mut body = args[index + 1]
                .lift_loose(0, 1)
                .map_err(|_| unsupported("variant minor scope"))?;
            for field in 0..ctor.fields.len() {
                self.tick()?;
                body = self.minor_apply(
                    body,
                    Expr::proj(shape.projection(ctor), field as u64, major.clone()),
                )?;
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
        Ok(Some(Case {
            name: case_name,
            major: args.last().expect("validated recursor arity").clone(),
            branches,
            result,
        }))
    }

    pub(super) fn register_constructor_branch(
        &mut self,
        lambda: &Expr,
        result: ValueType,
    ) -> Result<(), IngressError> {
        reserve(&mut self.lambdas, self.limits.max_lambda_bindings)?;
        self.lambdas.push(LambdaBinding {
            lambda: lambda.clone(),
            parameters: vec![ValueType::Constructor],
            parameter_ownership: borrowed_runtime_parameters(1)?,
            result,
            result_ownership: result_ownership(result),
            recursion: LambdaRecursion::NonRecursive,
        });
        Ok(())
    }
}
