//! Full mutual recursors become native, acyclic peer-closure groups. Each
//! motive supplies its own runtime interface, not the entry member's result.
use super::*;

struct Motive {
    domains: Vec<Expr>,
    parameters: Vec<ValueType>,
    result: ValueType,
    result_type: Expr,
    hypothesis_type: Expr,
    self_type: Expr,
}

fn variable(index: usize) -> Result<Expr, IngressError> {
    let index = u32::try_from(index).map_err(|_| unsupported("mutual binder count"))?;
    Expr::bvar(index).map_err(|_| unsupported("mutual binder scope"))
}

impl Preparation<'_> {
    fn mutual_motive(
        &mut self,
        syntax: &Expr,
        family: &Expr,
        indices: &[Expr],
    ) -> Result<Option<Motive>, IngressError> {
        let Some(body) = self.indexed_motive(syntax, indices, family)? else {
            return Ok(None);
        };
        let mut domains = Vec::new();
        let mut parameters = Vec::new();
        for domain in indices.iter().chain(std::iter::once(family)) {
            self.tick()?;
            let Some(parameter) = self.value_type(domain)? else {
                return Ok(None);
            };
            reserve(&mut domains, self.limits.max_context_depth)?;
            reserve(&mut parameters, self.limits.max_context_depth)?;
            domains.push(domain.clone());
            parameters.push(parameter);
        }
        let first_extra = domains.len();
        let mut result_type = &body;
        loop {
            self.tick()?;
            match result_type.node() {
                ExprNode::MData { expr, .. } => result_type = expr,
                ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    let Some(parameter) = self.value_type(binder_type)? else {
                        return Ok(None);
                    };
                    reserve(&mut domains, self.limits.max_context_depth)?;
                    reserve(&mut parameters, self.limits.max_context_depth)?;
                    domains.push(binder_type.clone());
                    parameters.push(parameter);
                    result_type = body;
                }
                _ => break,
            }
        }
        let Some(result) = self.value_type(result_type)? else {
            return Ok(None);
        };
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
        Ok(Some(Motive {
            domains,
            parameters,
            result,
            result_type: result_type.clone(),
            hypothesis_type,
            self_type,
        }))
    }

    pub(in crate::runtime) fn mutual_fold(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<Option<Fold>, IngressError> {
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(name) else {
            return Ok(None);
        };
        let Some(group) = self.mutual_group(rec, levels, args)? else {
            return Ok(None);
        };
        if args.len() < group.arity || group.shapes.len() > u16::MAX as usize {
            return Ok(None);
        }
        let mut motives = Vec::new();
        for (index, shape) in group.shapes.iter().enumerate() {
            self.tick()?;
            let Some(motive) = self.mutual_motive(
                &args[rec.num_params as usize + index],
                &shape.source,
                &group.indices[index],
            )?
            else {
                return Ok(None);
            };
            reserve(&mut motives, self.limits.max_lambda_bindings)?;
            motives.push(motive);
        }
        let id = self.next_mutual;
        self.next_mutual = id
            .checked_add(1)
            .ok_or_else(|| unsupported("mutual closure identity"))?;
        let group_name = Name::num(super::super::name("_fln_runtime_mutual_rec"), u64::from(id));
        let case_prefix = Name::num(
            super::super::name("_fln_runtime_mutual_fold_case"),
            u64::from(id),
        );
        let mut members = Vec::new();
        let mut minor_index = rec.num_params as usize + motives.len();
        for (index, (shape, motive)) in group.shapes.iter().zip(&motives).enumerate() {
            self.tick()?;
            let name = Name::num(group_name.clone(), index as u64);
            let case_name = Name::num(case_prefix.clone(), index as u64);
            if self.environment.contains(&name) || self.environment.contains(&case_name) {
                return Err(unsupported("runtime mutual fold name collision"));
            }
            // The branch is under all peer closures, this member's actual
            // runtime arguments, and one branch-local major premise.
            let depth = motives
                .len()
                .saturating_add(motive.parameters.len())
                .saturating_add(1);
            if depth > self.limits.max_context_depth {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::ContextDepth,
                    limit: self.limits.max_context_depth,
                    observed: depth,
                });
            }
            let lift = u32::try_from(depth).map_err(|_| unsupported("mutual minor scope"))?;
            let extra = motive.parameters.len() - 1 - group.indices[index].len();
            let mut branches = Vec::new();
            let mut constructors = Vec::new();
            for (constructor_index, ctor) in shape.constructors.iter().enumerate() {
                self.tick()?;
                let mut body = self.lift(&args[minor_index], lift)?;
                minor_index += 1;
                let mut hypotheses = Vec::new();
                let mut logical_fields = self.indexed_constructor_telescope(shape, ctor)?;
                for (field_index, field_type) in ctor.fields.iter().enumerate() {
                    self.tick()?;
                    let field =
                        Expr::proj(shape.projection(ctor), field_index as u64, variable(0)?);
                    body = self.minor_apply(body, field.clone())?;
                    let logical = self.type_head(&logical_fields)?;
                    let ExprNode::ForallE {
                        binder_type: logical_type,
                        body: next_field,
                        ..
                    } = logical.node()
                    else {
                        return Err(unsupported("mutual constructor field telescope"));
                    };
                    logical_fields = self.substitution(next_field, &field)?;
                    if let Some(target) = group
                        .shapes
                        .iter()
                        .position(|peer| &peer.source == field_type)
                    {
                        let marker = FVarId(Name::num(
                            Name::num(case_name.clone(), constructor_index as u64),
                            field_index as u64,
                        ));
                        let mut peer = variable(motives.len() + motive.parameters.len() - target)?;
                        // The child belongs to its own sibling's index space.
                        // Reconstruct its real indices from admitted field
                        // types with preceding fields rebound to projections.
                        for arg in self.indexed_field_arguments(
                            logical_type,
                            &group.shapes[target].source,
                            group.indices[target].len(),
                        )? {
                            self.tick()?;
                            peer = Expr::app(peer, arg);
                        }
                        reserve(&mut hypotheses, self.limits.max_context_depth)?;
                        hypotheses.push((marker, Expr::app(peer, field), target));
                    }
                }
                for (marker, _, _) in &hypotheses {
                    body = self.minor_apply(body, Expr::fvar(marker.clone()))?;
                }
                for argument in (0..extra).rev() {
                    body = self.minor_apply(body, variable(argument + 1)?)?;
                }
                // A sibling may have a different result or accumulator
                // telescope. Use its interface, and share only the IHs that
                // survive beta reduction of the checked minor premise.
                for (marker, hypothesis, target) in hypotheses.into_iter().rev() {
                    self.tick()?;
                    let abstracted = body
                        .lift_loose(0, 1)
                        .and_then(|lifted| lifted.abstract_fvar(&marker, 0))
                        .map_err(|_| unsupported("mutual hypothesis scope"))?;
                    if abstracted.has_loose_bvar(0) {
                        body = Expr::let_e(
                            marker.0,
                            motives[target].hypothesis_type.clone(),
                            hypothesis,
                            abstracted,
                            false,
                        );
                    }
                }
                let body =
                    self.typed_callable_result(body, motive.result_type.clone(), motive.result)?;
                reserve(&mut branches, self.limits.max_lambda_bindings)?;
                branches.push(Expr::lam(
                    Name::num(case_name.clone(), constructor_index as u64),
                    shape.source.clone(),
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
                result: motive.result,
            });
            reserve(&mut members, self.limits.max_lambda_bindings)?;
            members.push(Member {
                name,
                self_type: motive.self_type.clone(),
                domains: motive.domains.clone(),
                parameters: motive.parameters.clone(),
                case: variants::Case {
                    name: case_name,
                    major: variable(extra)?,
                    branches,
                    result: motive.result,
                },
            });
        }
        let mut arguments = Vec::new();
        for arg in &args[group.arity - 1 - group.indices[group.selected].len()..] {
            reserve(&mut arguments, self.limits.max_application_args)?;
            arguments.push(arg.clone());
        }
        Ok(Some(Fold {
            group: id,
            selected: group.selected,
            members,
            arguments,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_lexical_contexts_prepare_mutual_groups_on_a_small_host_stack() {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        let source = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../examples/native_mutual_folds.lean"
        ))
        .split("#eval")
        .next()
        .unwrap();
        let engine = Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(move || {
                let Some(ConstantInfo::Defn(definition)) = engine.environment.find(&name("total"))
                else {
                    panic!("checked definition")
                };
                let mut expression = definition.value.clone();
                for _ in 0..250 {
                    expression = Expr::let_e(
                        Name::anonymous(),
                        Expr::const_(name("Nat"), vec![]),
                        nat::literal(0),
                        expression,
                        false,
                    );
                }
                let mut preparation =
                    Preparation::new(&engine.environment, IngressLimits::default());
                let prepared = preparation.expression(&expression).unwrap();
                assert!(!prepared.has_fvar());
                assert_eq!(
                    preparation
                        .lambdas
                        .iter()
                        .filter(|binding| matches!(
                            binding.recursion,
                            LambdaRecursion::MutualMember { .. }
                        ))
                        .count(),
                    2
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
