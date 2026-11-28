//! Check the primitive used by generated overrides from its admitted body.
//! Proof helpers may differ between native source and imported declarations;
//! their values are erased. The computational path must still be precisely
//! balanced single-field lifts around canonical equality transport.
use super::*;
use fln_core::level::Level;

impl Preparation<'_> {
    fn computed_cast_dependency(&mut self, requested: &Name) -> Result<(), IngressError> {
        self.tick()?;
        if self.implementations()?.get(requested).is_some()
            || self.has_extern_attribute(requested)?
            || self
                .runtime_initializers
                .is_some_and(|names| names.contains(requested))
            || self
                .environment
                .contains(&Name::str(requested.clone(), "_unsafe_rec"))
        {
            return Err(unsupported(
                "computed-field cast dependency has conflicting execution metadata",
            ));
        }
        Ok(())
    }

    fn computed_cast_wrapper(&mut self, family_name: &Name) -> Result<Name, IngressError> {
        if family_name != &name("PLift") && family_name != &name("ULift") {
            return Err(unsupported(
                "computed-field cast uses an unsupported wrapper",
            ));
        }
        self.computed_cast_dependency(family_name)?;
        let Some(ConstantInfo::Induct(family)) = self.environment.find(family_name) else {
            return Err(unsupported("computed-field cast wrapper is absent"));
        };
        let [constructor] = family.ctors.as_slice() else {
            return Err(unsupported(
                "computed-field cast wrapper is not a single-field structure",
            ));
        };
        if family.is_unsafe
            || family.is_rec
            || family.num_params != 1
            || family.num_indices != 0
            || family.all.as_slice() != [family_name.clone()]
            || family.base.level_params.len() != if family_name == &name("PLift") { 1 } else { 2 }
        {
            return Err(unsupported(
                "computed-field cast wrapper differs from its representation",
            ));
        }
        self.computed_cast_dependency(constructor)?;
        let Some(ConstantInfo::Ctor(ctor)) = self.environment.find(constructor) else {
            return Err(unsupported(
                "computed-field cast wrapper constructor is absent",
            ));
        };
        let ExprNode::ForallE {
            binder_type: family_domain,
            body: family_sort,
            ..
        } = family.base.type_.node()
        else {
            return Err(unsupported("computed-field cast wrapper family telescope"));
        };
        if ctor.is_unsafe
            || ctor.num_params != 1
            || ctor.num_fields != 1
            || ctor.cidx != 0
            || ctor.induct != *family_name
            || ctor.base.level_params != family.base.level_params
        {
            return Err(unsupported(
                "computed-field cast wrapper constructor differs from its representation",
            ));
        }
        let ExprNode::ForallE {
            binder_type: carrier_sort,
            body: field,
            ..
        } = ctor.base.type_.node()
        else {
            return Err(unsupported("computed-field cast wrapper carrier telescope"));
        };
        let ExprNode::ForallE {
            binder_type: carrier,
            body: result,
            ..
        } = field.node()
        else {
            return Err(unsupported("computed-field cast wrapper field telescope"));
        };
        let (head, args) = self.spine(result)?;
        if !matches!(carrier_sort.node(), ExprNode::Sort { .. })
            || family_domain != carrier_sort
            || !matches!(family_sort.node(), ExprNode::Sort { level } if level.is_never_zero())
            || !matches!(carrier.node(), ExprNode::BVar { idx: 0 })
            || !matches!(head.node(), ExprNode::Const { name, levels }
                if name == family_name && levels == &family.base.level_params.iter().cloned().map(Level::param).collect::<Vec<_>>())
            || !matches!(args.as_slice(), [argument] if matches!(argument.node(), ExprNode::BVar { idx: 1 }))
        {
            return Err(unsupported(
                "computed-field cast wrapper does not retain its payload",
            ));
        }
        Ok(constructor.clone())
    }

    pub(super) fn check_computed_cast_primitive(&mut self) -> Result<(), IngressError> {
        if self.computed_fields.cast_checked {
            return Ok(());
        }
        let cast_name = name("unsafeCast");
        self.computed_cast_dependency(&cast_name)?;
        let Some(ConstantInfo::Defn(definition)) = self.environment.find(&cast_name) else {
            return Err(unsupported(
                "computed-field cast primitive is not an admitted definition",
            ));
        };
        if definition.safety != DefinitionSafety::Unsafe
            || definition.base.level_params.len() != 2
            || definition.all.as_slice() != [cast_name]
        {
            return Err(unsupported(
                "computed-field cast primitive has a different declaration shape",
            ));
        }
        let mut type_ = definition.base.type_.clone();
        let mut value = definition.value.clone();
        for (index, info) in [
            BinderInfo::Implicit,
            BinderInfo::Implicit,
            BinderInfo::Default,
        ]
        .into_iter()
        .enumerate()
        {
            self.tick()?;
            let ExprNode::ForallE {
                binder_type: domain,
                body: result,
                binder_info,
                ..
            } = type_.node()
            else {
                return Err(unsupported("computed-field cast primitive telescope"));
            };
            let ExprNode::Lam {
                binder_type: value_domain,
                body,
                binder_info: value_info,
                ..
            } = value.node()
            else {
                return Err(unsupported(
                    "computed-field cast primitive lambda telescope",
                ));
            };
            let expected = if index < 2 {
                Expr::sort(Level::param(definition.base.level_params[index].clone()))
            } else {
                Expr::bvar(1).map_err(|_| unsupported("computed-field cast primitive scope"))?
            };
            if *binder_info != info
                || *value_info != info
                || domain != &expected
                || value_domain != domain
            {
                return Err(unsupported(
                    "computed-field cast primitive has a different polymorphic signature",
                ));
            }
            type_ = result.clone();
            value = body.clone();
        }
        if !matches!(type_.node(), ExprNode::BVar { idx: 1 }) {
            return Err(unsupported("computed-field cast primitive result type"));
        }
        let mut wrappers = Vec::new();
        loop {
            self.tick()?;
            match value.node() {
                ExprNode::MData { expr, .. } => {
                    value = expr.clone();
                    continue;
                }
                ExprNode::BVar { idx: 0 } => break,
                ExprNode::Proj {
                    struct_name,
                    idx: 0,
                    expr,
                } => {
                    self.computed_cast_wrapper(struct_name)?;
                    reserve(&mut wrappers, self.limits.max_context_depth)?;
                    wrappers.push((false, struct_name.clone()));
                    value = expr.clone();
                    continue;
                }
                _ => {}
            }
            let (head, arguments) = self.spine(&value)?;
            let ExprNode::Const {
                name: callee,
                levels,
            } = head.node()
            else {
                return Err(unsupported(
                    "computed-field cast primitive has a different computational body",
                ));
            };
            if callee == &name("PLift.up") || callee == &name("ULift.up") {
                let family = callee.parent();
                let constructor = self.computed_cast_wrapper(&family)?;
                if *callee != constructor || arguments.len() != 2 {
                    return Err(unsupported("computed-field cast wrapper application"));
                }
                reserve(&mut wrappers, self.limits.max_context_depth)?;
                wrappers.push((true, family));
                value = arguments[1].clone();
            } else if callee == &name("Eq.rec") {
                if arguments.len() != 6
                    || levels.len() != 2
                    || !source_intrinsics::equality_family_matches(
                        self.environment,
                        &mut self.visited,
                        self.limits,
                    )?
                {
                    return Err(unsupported(
                        "computed-field cast requires canonical equality transport",
                    ));
                }
                for dependency in ["Eq", "Eq.refl", "Eq.rec"] {
                    self.computed_cast_dependency(&name(dependency))?;
                }
                value = arguments[3].clone();
            } else if ["cast", "PLift.down", "ULift.down"]
                .iter()
                .any(|candidate| callee == &name(candidate))
            {
                self.computed_cast_dependency(callee)?;
                let Some(ConstantInfo::Defn(helper)) = self.environment.find(callee) else {
                    return Err(unsupported(
                        "computed-field cast helper is not a definition",
                    ));
                };
                if helper.safety != DefinitionSafety::Safe
                    || helper.base.level_params.len() != levels.len()
                {
                    return Err(unsupported(
                        "computed-field cast helper is not a safe instantiated definition",
                    ));
                }
                let mut body =
                    self.universe_instance(&helper.value, &helper.base.level_params, levels)?;
                for argument in arguments {
                    self.tick()?;
                    let ExprNode::Lam { body: inner, .. } = body.node() else {
                        return Err(unsupported("computed-field cast helper application"));
                    };
                    body = self.substitution(inner, &argument)?;
                }
                value = body;
            } else {
                return Err(unsupported(
                    "computed-field cast primitive has an unsupported computational dependency",
                ));
            }
        }
        let mut payload = Vec::new();
        for (wrap, family) in wrappers.into_iter().rev() {
            self.tick()?;
            if wrap {
                reserve(&mut payload, self.limits.max_context_depth)?;
                payload.push(family);
            } else if payload.pop().as_ref() != Some(&family) {
                return Err(unsupported(
                    "computed-field cast primitive changes its payload representation",
                ));
            }
        }
        if !payload.is_empty() {
            return Err(unsupported(
                "computed-field cast primitive retains an unmatched wrapper",
            ));
        }
        self.computed_fields.cast_checked = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::array_iteration::{replace, with_fixture};

    #[test]
    fn actual_pinned_cast_has_the_required_payload_transport() {
        with_fixture(|environment| {
            let mut preparation = Preparation::new(environment, IngressLimits::default());
            preparation.check_computed_cast_primitive().unwrap();
            assert!(preparation.computed_fields.cast_checked);
            // Primitive recognition alone cannot erase an arbitrary call or
            // create a computed-family/override provenance entry.
            assert!(preparation.computed_fields.families.is_empty());
            assert!(preparation.computed_fields.overrides.is_empty());
            assert!(
                preparation
                    .computed_override_definition(&name("unsafeCast"))
                    .unwrap()
                    .is_none()
            );
        });
    }

    #[test]
    fn changed_cast_body_wrapper_and_execution_metadata_refuse() {
        with_fixture(|environment| {
            let Some(ConstantInfo::Defn(original)) = environment.find(&name("unsafeCast")) else {
                panic!("pinned cast definition");
            };
            let mut changed = original.clone();
            changed.value = Expr::const_(name("Nat.zero"), vec![]);
            let changed = replace(environment, ConstantInfo::Defn(changed));
            let mut preparation = Preparation::new(&changed, IngressLimits::default());
            assert!(preparation.check_computed_cast_primitive().is_err());
            assert!(!preparation.computed_fields.cast_checked);

            let Some(ConstantInfo::Ctor(original)) = environment.find(&name("PLift.up")) else {
                panic!("pinned lift constructor");
            };
            let mut changed = original.clone();
            changed.num_fields += 1;
            let changed = replace(environment, ConstantInfo::Ctor(changed));
            let mut preparation = Preparation::new(&changed, IngressLimits::default());
            assert!(preparation.check_computed_cast_primitive().is_err());
            assert!(!preparation.computed_fields.cast_checked);

            let changed = fln_elab::externs::register(
                environment,
                &name("cast"),
                vec![fln_elab::externs::ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "foreign_cast".to_owned(),
                }],
            )
            .unwrap();
            let mut preparation = Preparation::new(&changed, IngressLimits::default());
            assert!(preparation.check_computed_cast_primitive().is_err());
            assert!(!preparation.computed_fields.cast_checked);

            let mut preparation = Preparation::new(environment, IngressLimits::default());
            preparation.check_computed_cast_primitive().unwrap();
            let initializers = BTreeSet::from([name("unsafeCast")]);
            let mut preparation = preparation.with_runtime_initializers(&initializers);
            assert!(!preparation.computed_fields.cast_checked);
            assert!(preparation.check_computed_cast_primitive().is_err());
        });
    }

    #[test]
    fn incomplete_cast_validation_never_populates_the_positive_cache() {
        with_fixture(|environment| {
            let mut preparation = Preparation::new(
                environment,
                IngressLimits {
                    max_nodes: 1,
                    ..IngressLimits::default()
                },
            );
            assert!(matches!(
                preparation.check_computed_cast_primitive(),
                Err(IngressError::ResourceLimit { .. })
            ));
            assert!(!preparation.computed_fields.cast_checked);
            preparation.limits = IngressLimits::default();
            preparation.check_computed_cast_primitive().unwrap();
            assert!(preparation.computed_fields.cast_checked);
        });
    }
}
