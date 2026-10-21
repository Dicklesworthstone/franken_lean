//! Native, lazy elimination of closed data variants. Layouts and eliminators
//! come from the admitted environment. Branch payloads are projected only after
//! the compiler's constructor tag/shape test selects that particular branch.
use super::*;
use fln_core::level::Level;
mod nonrecursive;

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
                < rec
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
        if shape.constructors.len() != rec.rules.len() {
            return Ok(None);
        }
        let minors = if shape.recursive {
            let Some(minors) = self.case_only_minors(&shape, &args[1..rec.rules.len() + 1])? else {
                return Ok(None);
            };
            minors
        } else {
            args[1..rec.rules.len() + 1].to_vec()
        };
        // A branch can return a function whose later domains contain proofs
        // about the major or preceding fields. Keep every runtime argument,
        // erase only its checked proof representation, and remove the motive's
        // major binder only once its runtime type no longer refers to it.
        let motive = self
            .indexed_motive(&args[0], &[], &family)?
            .ok_or_else(|| unsupported("dependent variant recursor result"))?;
        let arity = rec.rules.len().saturating_add(2);
        let (args, applied) = args.split_at(arity);
        let (result_type, result) = if applied.is_empty() {
            let result = self
                .value_type(&motive)?
                .ok_or_else(|| unsupported("dependent variant recursor result"))?;
            (motive.clone(), result)
        } else {
            let Some(result) = self.variant_application_type(&motive, applied.len())? else {
                return Ok(None);
            };
            result
        };
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
            let mut body = minors[index]
                .lift_loose(0, 1)
                .map_err(|_| unsupported("variant minor scope"))?;
            for field in 0..ctor.fields.len() {
                self.tick()?;
                body = self.constructor_minor_apply(
                    body,
                    ctor,
                    field,
                    Expr::proj(shape.projection(ctor), field as u64, major.clone()),
                )?;
            }
            reserve(&mut branches, self.limits.max_lambda_bindings)?;
            let body = if applied.is_empty() {
                self.typed_callable_result(body, motive.clone(), result)?
            } else {
                // The major has already selected this minor. Apply its actual
                // operands one at a time, preserving every producer/argument
                // stage and evaluating each operand once. The extra depth is
                // this branch's major binder; operands still use caller scope.
                let body = self
                    .apply_producer(body, motive.clone(), applied, 1)?
                    .ok_or_else(|| unsupported("dependent variant recursor application"))?;
                self.typed_callable_result(body, result_type.clone(), result)?
            };
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

    /// Recover the exact residual interface after applying supplied operands.
    /// A residual callback remains a checked join: each prepared branch must
    /// produce this interface, never a cast between different return stages.
    pub(super) fn variant_application_type(
        &mut self,
        type_: &Expr,
        count: usize,
    ) -> Result<Option<(Expr, ValueType)>, IngressError> {
        let mut result = type_.clone();
        for _ in 0..count {
            self.tick()?;
            let normal = self.type_head(&result)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            if binder_type.has_loose_bvars()
                || body.has_loose_bvars()
                || self.value_type(binder_type)?.is_none()
            {
                return Ok(None);
            }
            result = body.clone();
        }
        Ok(self.value_type(&result)?.map(|layout| (result, layout)))
    }

    /// An applied identity ascription may expose a checked case when its
    /// residual interface is known. The selected branch retains that checked
    /// type even under partial application. Strict prefixes remain unevaluated.
    pub(super) fn applied_variant_ascription(
        &mut self,
        value: &Expr,
        type_: &Expr,
        arguments: usize,
    ) -> Result<bool, IngressError> {
        if arguments == 0 || self.variant_application_type(type_, arguments)?.is_none() {
            return Ok(false);
        }
        let mut value = value.clone();
        loop {
            self.tick()?;
            value = match value.node() {
                ExprNode::MData { expr, .. } => expr.clone(),
                ExprNode::LetE { value, body, .. }
                    if matches!(body.node(), ExprNode::BVar { idx: 0 }) =>
                {
                    value.clone()
                }
                ExprNode::LetE { body, .. } => body.clone(),
                _ => break,
            };
        }
        let (head, args) = self.spine(&value)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(false);
        };
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(name) else {
            return Ok(false);
        };
        if rec.is_unsafe
            || rec.num_indices != 0
            || rec.num_motives != 1
            || rec.num_minors < 2
            || rec.all.len() != 1
            || rec.rules.len() != rec.num_minors as usize
            || levels.len() != rec.base.level_params.len()
            || args.len()
                < rec
                    .rules
                    .len()
                    .saturating_add(rec.num_params as usize)
                    .saturating_add(2)
        {
            return Ok(false);
        }
        let Some(shape) = self.recursor_shape(rec, levels, &args)? else {
            return Ok(false);
        };
        if shape.constructors.len() != rec.rules.len() {
            return Ok(false);
        }
        if !shape.recursive {
            return Ok(true);
        }
        let offset = rec.num_params as usize + 1;
        Ok(self
            .case_only_minors(&shape, &args[offset..offset + rec.rules.len()])?
            .is_some())
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

#[cfg(test)]
mod application_tests {
    use super::*;

    fn engine() -> crate::Engine {
        crate::Engine::with_source_seed(crate::EngineAdmissionLimits::new(
            crate::Budget::for_stack_bytes(2 * 1024 * 1024),
        ))
        .unwrap()
        .into_complete()
        .unwrap()
    }
    fn constant(label: &str) -> Expr {
        Expr::const_(name(label), vec![])
    }
    fn arrow(domain: Expr, result: Expr) -> Expr {
        Expr::forall_e(Name::anonymous(), domain, result, BinderInfo::Default)
    }

    #[test]
    fn partial_variant_types_keep_the_exact_remaining_telescope() {
        let base = engine();
        let mut preparation = Preparation::new(base.environment(), IngressLimits::default());
        let suffix = arrow(constant("Bool"), constant("Nat"));
        let input = arrow(constant("Nat"), suffix.clone());
        let (type_, layout) = preparation
            .variant_application_type(&input, 1)
            .unwrap()
            .unwrap();
        assert_eq!(type_, suffix);
        let ValueType::Closure(id) = layout else {
            panic!("residual function interface");
        };
        let signature = &preparation.interfaces[id.get() as usize];
        assert_eq!(signature.parameters, vec![ValueType::Bool]);
        assert_eq!(signature.result, ValueType::Nat);
        assert_eq!(
            preparation.variant_application_type(&input, 2).unwrap(),
            Some((constant("Nat"), ValueType::Nat))
        );
        assert!(
            preparation
                .variant_application_type(&input, 3)
                .unwrap()
                .is_none()
        );
        let dependent = arrow(constant("Nat"), Expr::bvar(0).unwrap());
        assert!(
            preparation
                .variant_application_type(&dependent, 1)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn partial_variant_type_inspection_obeys_work_bounds_and_preserves_the_environment() {
        let base = engine();
        let root = base.logical_root(&KVMap::new());
        let input = arrow(constant("Nat"), arrow(constant("Bool"), constant("Nat")));
        let mut full = Preparation::new(base.environment(), IngressLimits::default());
        let result = full.variant_application_type(&input, 1).unwrap();
        let required = full.visited;
        for available in [0, required - 1] {
            let mut stopped = Preparation::new(
                base.environment(),
                IngressLimits {
                    max_nodes: available,
                    ..IngressLimits::default()
                },
            );
            assert!(matches!(
                stopped.variant_application_type(&input, 1),
                Err(IngressError::ResourceLimit { .. })
            ));
            assert_eq!(base.logical_root(&KVMap::new()), root);
        }
        let mut retry = Preparation::new(base.environment(), IngressLimits::default());
        assert_eq!(retry.variant_application_type(&input, 1).unwrap(), result);
        assert_eq!(retry.interfaces, full.interfaces);
        assert_eq!(retry.visited, required);
    }
}
