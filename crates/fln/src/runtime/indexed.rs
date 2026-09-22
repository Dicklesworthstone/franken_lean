//! Erase value indices from runtime *types*, never from executable arguments.
//! A supported family has one uniform layout at fixed type parameters. Both
//! checkers see the original indexed declaration and every original application.
use super::*;
use fln_core::level::Level;
use fln_env::constants::InductiveVal;
use std::collections::HashMap;

impl Preparation<'_> {
    /// The initial indexed profile has independent scalar index domains. Type
    /// indices and domains depending on earlier indices are not layout evidence.
    /// This is deliberately nonrecursive: discovering an index type must not
    /// recursively start discovery of the family whose layout is being built.
    pub(super) fn index_domains(
        &mut self,
        family: &InductiveVal,
        levels: &[Level],
        parameters: &[Expr],
    ) -> Result<Option<Vec<Expr>>, IngressError> {
        if family.is_unsafe
            || family.all.len() != 1
            || family.num_nested != 0
            || family.base.level_params.len() != levels.len()
            || family.num_params as usize != parameters.len()
        {
            return Ok(None);
        }
        let mut type_ =
            self.universe_instance(&family.base.type_, &family.base.level_params, levels)?;
        for parameter in parameters {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            if !self.type_parameter(binder_type)? {
                return Ok(None);
            }
            type_ = self.substitution(body, parameter)?;
        }
        let mut domains = Vec::new();
        for _ in 0..family.num_indices {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            let domain = self.normalize_type(binder_type)?;
            if domain.has_loose_bvars()
                || !matches!(
                    executable_value_type(&domain, &self.value_types),
                    Some((ValueType::Nat | ValueType::Bool | ValueType::String, _))
                )
            {
                return Ok(None);
            }
            reserve(&mut domains, self.limits.max_context_depth)?;
            domains.push(domain);
            // Do not substitute a fabricated value. Any dependence on a prior
            // index remains loose and is rejected by the next domain check.
            type_ = body.clone();
        }
        let sort = self.type_head(&type_)?;
        Ok(
            matches!(sort.node(), ExprNode::Sort { level } if level.is_never_zero())
                .then_some(domains),
        )
    }

    /// Separate from logical type normalization and proof classification. The
    /// postorder is heap-backed and memoized; erased indices are never traversed
    /// or normalized, so a large index expression cannot expand into a layout.
    pub(super) fn erase_data_indices(&mut self, input: &Expr) -> Result<Expr, IngressError> {
        enum Work {
            Enter(Expr),
            Finish(Expr, Expr),
        }
        let mut work = vec![Work::Enter(input.clone())];
        let mut done = HashMap::<Expr, Expr>::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Work::Enter(source) => {
                    if done.contains_key(&source) {
                        continue;
                    }
                    let mut normal = self.type_head(&source)?;
                    let (head, args) = self.spine(&normal)?;
                    if let ExprNode::Const { name, levels } = head.node()
                        && let Some(ConstantInfo::Induct(family)) = self.environment.find(name)
                        && family.num_indices != 0
                        && args.len()
                            == (family.num_params as usize)
                                .saturating_add(family.num_indices as usize)
                        && self
                            .index_domains(family, levels, &args[..family.num_params as usize])?
                            .is_some()
                    {
                        normal = args[..family.num_params as usize]
                            .iter()
                            .cloned()
                            .fold(head.clone(), Expr::app);
                    }
                    reserve(&mut work, self.limits.max_nodes)?;
                    work.push(Work::Finish(source, normal.clone()));
                    let mut push = |child: &Expr| -> Result<(), IngressError> {
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Enter(child.clone()));
                        Ok(())
                    };
                    match normal.node() {
                        ExprNode::App { f, a } => {
                            push(a)?;
                            push(f)?;
                        }
                        ExprNode::ForallE {
                            binder_type, body, ..
                        }
                        | ExprNode::Lam {
                            binder_type, body, ..
                        } => {
                            push(body)?;
                            push(binder_type)?;
                        }
                        _ => {}
                    }
                }
                Work::Finish(source, normal) => {
                    let child = |e: &Expr| {
                        done.get(e)
                            .cloned()
                            .ok_or_else(|| unsupported("indexed type postorder"))
                    };
                    let value = match normal.node() {
                        ExprNode::App { f, a } => Expr::app(child(f)?, child(a)?),
                        ExprNode::ForallE {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::forall_e(
                            binder_name.clone(),
                            child(binder_type)?,
                            child(body)?,
                            *binder_info,
                        ),
                        ExprNode::Lam {
                            binder_name,
                            binder_type,
                            body,
                            binder_info,
                        } => Expr::lam(
                            binder_name.clone(),
                            child(binder_type)?,
                            child(body)?,
                            *binder_info,
                        ),
                        _ => normal,
                    };
                    done.try_reserve(1)
                        .map_err(|_| IngressError::AllocationFailure {
                            resource: IngressResource::Nodes,
                            requested: done.len().saturating_add(1),
                        })?;
                    done.insert(source, value);
                }
            }
        }
        done.remove(input)
            .ok_or_else(|| unsupported("indexed type result"))
    }
}

impl Preparation<'_> {
    /// The logical motive may depend on erased value indices, but its runtime
    /// result may not. Remove only binders absent after representation erasure.
    pub(super) fn indexed_motive(
        &mut self,
        motive: &Expr,
        indices: &[Expr],
        family: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        let mut result = motive.clone();
        for domain in indices.iter().chain(std::iter::once(family)) {
            self.tick()?;
            let normal = self.type_head(&result)?;
            let ExprNode::Lam {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            if self.erase_runtime_type(binder_type)? != *domain {
                return Ok(None);
            }
            result = body.clone();
        }
        result = self.erase_runtime_type(&result)?;
        let count = indices.len().saturating_add(1);
        for index in 0..count {
            self.tick()?;
            let index = u32::try_from(index).map_err(|_| unsupported("indexed motive arity"))?;
            if result.has_loose_bvar(index) {
                return Ok(None);
            }
        }
        for _ in 0..count {
            // There is no occurrence to replace; substitution only lowers the
            // remaining outer context by one. No index value is fabricated.
            result = self.substitution(&result, &nat::literal(0))?;
        }
        Ok(Some(result))
    }

    pub(super) fn indexed_constructor_telescope(
        &mut self,
        shape: &records::Shape,
        ctor: &records::ShapeConstructor,
    ) -> Result<Expr, IngressError> {
        let (head, args) = self.spine(&shape.source)?;
        let ExprNode::Const { levels, .. } = head.node() else {
            return Err(unsupported("constructor family head"));
        };
        let Some(ConstantInfo::Ctor(original)) = self.environment.find(&ctor.original) else {
            return Err(unsupported("constructor telescope metadata"));
        };
        let mut type_ =
            self.universe_instance(&original.base.type_, &original.base.level_params, levels)?;
        for arg in args {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE { body, .. } = normal.node() else {
                return Err(unsupported("constructor parameter telescope"));
            };
            type_ = self.substitution(body, &arg)?;
        }
        Ok(type_)
    }

    /// Recursive calls retain the actual indices from the admitted field type.
    /// Preceding constructor fields have already been rebound to projections.
    pub(super) fn indexed_field_arguments(
        &mut self,
        type_: &Expr,
        family: &Expr,
        count: usize,
    ) -> Result<Vec<Expr>, IngressError> {
        let normal = self.type_head(type_)?;
        let (head, args) = self.spine(&normal)?;
        let (family_head, parameters) = self.spine(family)?;
        if head != family_head
            || args.len() != parameters.len().saturating_add(count)
            || self.erase_data_indices(&normal)? != *family
        {
            return Err(unsupported("dependent or function-valued indexed child"));
        }
        let mut indices = Vec::new();
        for index in &args[parameters.len()..] {
            self.tick()?;
            reserve(&mut indices, self.limits.max_application_args)?;
            indices.push(index.clone());
        }
        Ok(indices)
    }
}

#[cfg(test)]
mod tests;
