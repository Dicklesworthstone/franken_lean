//! Erase supported indices and value parameters from runtime *types*. A
//! supported family has one uniform layout at fixed type parameters: like the
//! pinned compiler, a constructor object stores only its fields. Value-index
//! arguments remain strict computations; Type-index arguments have inert slots
//! in generated folds. Both checkers see every original application.
use super::*;
use fln_core::expr::FVarId;
use fln_core::level::Level;
use fln_env::constants::InductiveVal;
use std::collections::HashMap;

pub(super) mod cache;

/// Stands for an unknown value parameter while a family or constructor
/// telescope is opened. A free variable selects no reduction, so a type still
/// mentioning it after runtime erasure depends on the parameter's actual value
/// and has no uniform representation. It never reaches executable code.
pub(super) fn pending_parameter() -> Expr {
    Expr::fvar(FVarId(name("_fln_runtime_value_parameter")))
}

/// The logical index telescope remains intact for motive checks. Only a
/// validated Type index has an inert native domain; scalar index domains and
/// arguments are unchanged. Keeping its slot preserves the checked index
/// order without making a type expression into an executable value.
pub(super) fn runtime_index_domain(domain: &Expr) -> Expr {
    if matches!(domain.node(), ExprNode::Sort { .. }) {
        proofs::erased_type()
    } else {
        domain.clone()
    }
}

pub(super) fn runtime_index_argument(domain: &Expr, argument: &Expr) -> Expr {
    if matches!(domain.node(), ExprNode::Sort { .. }) {
        proofs::erased_value()
    } else {
        argument.clone()
    }
}

impl Preparation<'_> {
    /// The canonical erased argument of a value parameter in a runtime type.
    /// It is not a term of the logical environment and is never evaluated; a
    /// layout keyed by it serves every value of that parameter.
    pub(super) fn erased_parameter(&self) -> Result<Expr, IngressError> {
        let erased = name("_fln_runtime_erased_parameter");
        if self.environment.contains(&erased) {
            return Err(unsupported("runtime erased parameter name collision"));
        }
        Ok(Expr::const_(erased, vec![]))
    }

    /// Open an admitted family's parameter telescope. A static type parameter
    /// is instantiated with its argument. Every other parameter is a value
    /// parameter; its argument is never inspected, normalized or evaluated
    /// here, and the pending marker stands for it. Returns the per-parameter
    /// value flags and the remaining index telescope.
    fn parameter_telescope(
        &mut self,
        family: &InductiveVal,
        levels: &[Level],
        parameters: &[Expr],
    ) -> Result<Option<(Vec<bool>, Expr)>, IngressError> {
        if family.is_unsafe
            || family.num_nested != 0
            || family.base.level_params.len() != levels.len()
            || family.num_params as usize != parameters.len()
        {
            return Ok(None);
        }
        let pending = pending_parameter();
        let mut type_ =
            self.universe_instance(&family.base.type_, &family.base.level_params, levels)?;
        let mut values = Vec::new();
        for parameter in parameters {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            let value = !self.type_parameter(binder_type)?;
            type_ = self.substitution(body, if value { &pending } else { parameter })?;
            reserve(&mut values, self.limits.max_context_depth)?;
            values.push(value);
        }
        Ok(Some((values, type_)))
    }

    /// Value-parameter flags of an admitted *data* family. A proposition keeps
    /// its original syntax: its inhabitants are erased proofs, never layouts.
    pub(super) fn value_parameters(
        &mut self,
        family: &InductiveVal,
        levels: &[Level],
        parameters: &[Expr],
    ) -> Result<Option<Vec<bool>>, IngressError> {
        let Some((values, mut type_)) = self.parameter_telescope(family, levels, parameters)?
        else {
            return Ok(None);
        };
        for _ in 0..family.num_indices {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE { body, .. } = normal.node() else {
                return Ok(None);
            };
            type_ = body.clone();
        }
        let sort = self.type_head(&type_)?;
        Ok(
            matches!(sort.node(), ExprNode::Sort { level } if level.is_never_zero())
                .then_some(values),
        )
    }

    /// Replace each value-parameter argument of a data family with the erased
    /// marker, without inspecting it. Static type arguments are unchanged.
    pub(super) fn runtime_parameters(
        &mut self,
        family: &InductiveVal,
        levels: &[Level],
        parameters: &[Expr],
    ) -> Result<Option<Vec<Expr>>, IngressError> {
        let Some(values) = self.value_parameters(family, levels, parameters)? else {
            return Ok(None);
        };
        let erased = self.erased_parameter()?;
        let mut result = Vec::new();
        for (parameter, value) in parameters.iter().zip(values) {
            self.tick()?;
            reserve(&mut result, self.limits.max_application_args)?;
            result.push(if value {
                erased.clone()
            } else {
                parameter.clone()
            });
        }
        Ok(Some(result))
    }

    /// The runtime type selecting a constructor's or recursor's layout. Value
    /// arguments are erased before any normalization, so a computed parameter
    /// is neither unfolded into a layout key nor evaluated. A family that is
    /// not supported data keeps its original application, and its refusal.
    pub(super) fn runtime_family(
        &mut self,
        family: &InductiveVal,
        levels: &[Level],
        parameters: &[Expr],
    ) -> Result<Expr, IngressError> {
        let parameters = match self.runtime_parameters(family, levels, parameters)? {
            Some(parameters) => parameters,
            None => parameters.to_vec(),
        };
        let mut source = Expr::const_(family.base.name.clone(), levels.to_vec());
        for parameter in parameters {
            self.tick()?;
            source = Expr::app(source, parameter);
        }
        Ok(source)
    }

    /// Index domains are independent scalars, or Type sorts for a single
    /// family. A domain depending on an earlier index or a value parameter is
    /// not layout evidence. This discovery is deliberately nonrecursive: it
    /// cannot start discovering the family whose layout is being built. The
    /// original domains are retained for checked motive comparisons.
    pub(super) fn index_domains(
        &mut self,
        family: &InductiveVal,
        levels: &[Level],
        parameters: &[Expr],
    ) -> Result<Option<Vec<Expr>>, IngressError> {
        let Some((_, mut type_)) = self.parameter_telescope(family, levels, parameters)? else {
            return Ok(None);
        };
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
            let type_index = family.all.len() == 1
                && matches!(domain.node(), ExprNode::Sort { level } if level.is_never_zero());
            if domain.has_loose_bvars()
                || domain.has_fvar()
                || (!type_index
                    && !matches!(
                        executable_value_type(&domain, &self.value_types),
                        Some((ValueType::Nat | ValueType::Bool | ValueType::String, _))
                    ))
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
        cache::erase_data_indices(self, input)
    }

    fn erase_data_indices_uncached(&mut self, input: &Expr) -> Result<Expr, IngressError> {
        enum Work {
            Enter(Expr),
            Finish(Expr, Expr),
            Alias(Expr, Expr),
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
                    if let Some(decision) = self.decision_representation(&head, &args)? {
                        normal = decision;
                    }
                    if let Some(carrier) = self.quotient_carrier(&head, &args)? {
                        // A quotient has its carrier's representation. Reenter
                        // the same worklist so nested quotients/data/functions
                        // do not create recursive host calls or visit relations.
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Alias(source, carrier.clone()));
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Enter(carrier));
                        continue;
                    }
                    if let ExprNode::Const { name, levels } = head.node()
                        && let Some(ConstantInfo::Induct(family)) = self.environment.find(name)
                        && args.len()
                            == (family.num_params as usize)
                                .saturating_add(family.num_indices as usize)
                        && let Some(parameters) = self.runtime_parameters(
                            family,
                            levels,
                            &args[..family.num_params as usize],
                        )?
                    {
                        // Value parameters and supported indices are erased before
                        // their children are visited: neither is traversed or
                        // normalized, so a computed argument never expands here.
                        let erase_indices = family.num_indices != 0
                            && self.index_domains(family, levels, &parameters)?.is_some();
                        if erase_indices
                            || parameters.as_slice() != &args[..family.num_params as usize]
                        {
                            let indices = if erase_indices {
                                &[][..]
                            } else {
                                &args[family.num_params as usize..]
                            };
                            normal = parameters
                                .into_iter()
                                .chain(indices.iter().cloned())
                                .fold(head.clone(), Expr::app);
                        }
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
                Work::Alias(source, carrier) => {
                    let value = done
                        .get(&carrier)
                        .cloned()
                        .ok_or_else(|| unsupported("quotient type postorder"))?;
                    done.try_reserve(1)
                        .map_err(|_| IngressError::AllocationFailure {
                            resource: IngressResource::Nodes,
                            requested: done.len().saturating_add(1),
                        })?;
                    done.insert(source, value);
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

    /// Open a constructor's parameter telescope at its layout's family. Static
    /// type arguments come from the layout key, which carries no value
    /// parameter: `values` supplies each value parameter in order (a runtime
    /// value the caller threads), and any one not supplied is the pending
    /// marker, so nothing computed from it can reach executable code.
    pub(super) fn indexed_constructor_telescope(
        &mut self,
        shape: &records::Shape,
        ctor: &records::ShapeConstructor,
        values: &[Expr],
    ) -> Result<Expr, IngressError> {
        let (head, args) = self.spine(&shape.source)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(unsupported("constructor family head"));
        };
        let Some(ConstantInfo::Induct(family)) = self.environment.find(name) else {
            return Err(unsupported("constructor family metadata"));
        };
        let flags = self
            .value_parameters(family, levels, &args)?
            .ok_or_else(|| unsupported("constructor parameter telescope"))?;
        let Some(ConstantInfo::Ctor(original)) = self.environment.find(&ctor.original) else {
            return Err(unsupported("constructor telescope metadata"));
        };
        let pending = pending_parameter();
        let mut supplied = values.iter();
        let mut type_ =
            self.universe_instance(&original.base.type_, &original.base.level_params, levels)?;
        for (arg, value) in args.iter().zip(flags) {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE { body, .. } = normal.node() else {
                return Err(unsupported("constructor parameter telescope"));
            };
            let replacement = if value {
                supplied.next().unwrap_or(&pending)
            } else {
                arg
            };
            type_ = self.substitution(body, replacement)?;
        }
        Ok(type_)
    }

    /// The runtime domains of a family's value parameters, by position. A
    /// child's index may be computed from one (a promoted index is), so a
    /// native recursion threads each as an unchanging runtime argument. A
    /// domain whose representation depends on an earlier value is refused.
    pub(super) fn value_parameter_domains(
        &mut self,
        family: &InductiveVal,
        levels: &[Level],
        parameters: &[Expr],
    ) -> Result<Option<Vec<(usize, Expr)>>, IngressError> {
        let Some(flags) = self.value_parameters(family, levels, parameters)? else {
            return Ok(None);
        };
        let pending = pending_parameter();
        let mut type_ =
            self.universe_instance(&family.base.type_, &family.base.level_params, levels)?;
        let mut domains = Vec::new();
        for (position, (parameter, value)) in parameters.iter().zip(flags).enumerate() {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = normal.node()
            else {
                return Ok(None);
            };
            if value {
                let domain = self.erase_runtime_type(binder_type)?;
                if domain.has_fvar() || domain.has_loose_bvars() {
                    return Err(unsupported("value parameter representation"));
                }
                reserve(&mut domains, self.limits.max_context_depth)?;
                domains.push((position, domain));
            }
            type_ = self.substitution(body, if value { &pending } else { parameter })?;
        }
        Ok(Some(domains))
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
            // The pending marker is the only free variable in an opened
            // constructor telescope. An index computed from a value parameter
            // the caller does not thread has no runtime value here.
            if index.has_fvar() {
                return Err(unsupported(
                    "index computed from an unthreaded value parameter",
                ));
            }
            reserve(&mut indices, self.limits.max_application_args)?;
            indices.push(index.clone());
        }
        Ok(indices)
    }
}

#[cfg(test)]
mod tests;
