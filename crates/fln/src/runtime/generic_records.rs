//! Records with generic methods require specialization at a known constructor.
//! This is type-only classification; it neither chooses a runtime layout nor
//! treats a failed compilation as permission to admit an executable command.
use super::*;

impl Preparation<'_> {
    pub(super) fn contains_generic_record(&mut self, input: &Expr) -> Result<bool, IngressError> {
        let mut work = vec![input.clone()];
        let mut seen = HashSet::new();
        while let Some(source) = work.pop() {
            self.tick()?;
            let source = self.type_head(&source)?;
            if seen.contains(&source) {
                continue;
            }
            let observed = seen.len().saturating_add(1);
            if observed > self.limits.max_nodes {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes,
                    limit: self.limits.max_nodes,
                    observed,
                });
            }
            seen.try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::Nodes,
                    requested: observed,
                })?;
            seen.insert(source.clone());
            if let ExprNode::ForallE {
                binder_type, body, ..
            } = source.node()
            {
                reserve(&mut work, self.limits.max_nodes)?;
                work.push(body.clone());
                reserve(&mut work, self.limits.max_nodes)?;
                work.push(binder_type.clone());
                continue;
            }
            let (head, parameters) = self.spine(&source)?;
            let ExprNode::Const { name, levels } = head.node() else {
                continue;
            };
            let Some(ConstantInfo::Induct(family)) = self.environment.find(name) else {
                continue;
            };
            if family.is_unsafe
                || family.is_rec
                || family.num_indices != 0
                || family.ctors.len() != 1
                || family.num_params as usize != parameters.len()
                || family.base.level_params.len() != levels.len()
            {
                continue;
            }
            let Some(ConstantInfo::Ctor(constructor)) =
                self.environment.find(&family.ctors[0]).cloned()
            else {
                continue;
            };
            if constructor.is_unsafe
                || constructor.induct != *name
                || constructor.num_params != family.num_params
                || constructor.base.level_params != family.base.level_params
                || self.st_ref_record_forbidden(name)?
                || self.array_record_forbidden(name)?
                || self.thunk_record_forbidden(name)?
                || self.task_record_forbidden(name)?
            {
                continue;
            }
            let mut type_ = self.universe_instance(
                &constructor.base.type_,
                &constructor.base.level_params,
                levels,
            )?;
            for parameter in parameters {
                self.tick()?;
                let normal = self.type_head(&type_)?;
                let ExprNode::ForallE { body, .. } = normal.node() else {
                    return Err(unsupported("generic record parameter telescope"));
                };
                type_ = self.substitution(body, &parameter)?;
            }
            // Keep earlier field binders in scope: classification reads their
            // types but never manufactures values for a dependent field.
            for _ in 0..constructor.num_fields {
                self.tick()?;
                let normal = self.type_head(&type_)?;
                let ExprNode::ForallE {
                    binder_type, body, ..
                } = normal.node()
                else {
                    return Err(unsupported("generic record field telescope"));
                };
                if self.polymorphic_callback_type(binder_type)? {
                    return Ok(true);
                }
                reserve(&mut work, self.limits.max_nodes)?;
                work.push(binder_type.clone());
                type_ = body.clone();
            }
        }
        Ok(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::OnceLock;

    fn c(label: &str) -> Expr {
        Expr::const_(name(label), Vec::new())
    }

    fn b(index: u32) -> Expr {
        Expr::bvar(index).unwrap()
    }

    fn engine() -> &'static Engine {
        static ENGINE: OnceLock<Engine> = OnceLock::new();
        ENGINE.get_or_init(|| {
            let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
            Engine::with_source_seed(limits)
                .unwrap()
                .into_complete()
                .unwrap()
                .check_source_files(
                    &[br#"
structure TemplateRecord where
  amount : (A : Type) -> A -> Nat
  unused : Nat
structure OrdinaryRecord where
  amount : Nat -> Nat
structure NestedTemplateRecord where
  inner : TemplateRecord
structure CarrierRecord where
  Carrier : Type
  value : Carrier
abbrev TemplateAlias := TemplateRecord
def templateWork (n : Nat) : Nat :=
  match n with | 0 => 0 | k + 1 => templateWork k + 1
def templateRecord (n : Nat) : TemplateRecord :=
  let paid := templateWork n
  { amount := fun A x => paid, unused := templateWork n }
"#],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                )
                .unwrap()
                .into_complete()
                .unwrap()
                .engine
        })
    }

    #[test]
    fn admitted_field_types_classify_record_parameters_results_aliases_and_nesting() {
        let environment = engine().environment();
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        for type_ in [
            c("TemplateRecord"),
            c("TemplateAlias"),
            c("NestedTemplateRecord"),
            Expr::forall_e(
                Name::anonymous(),
                c("TemplateRecord"),
                c("Nat"),
                BinderInfo::Default,
            ),
            Expr::forall_e(
                Name::anonymous(),
                c("Nat"),
                c("TemplateRecord"),
                BinderInfo::Default,
            ),
        ] {
            assert!(preparation.contains_generic_record(&type_).unwrap());
        }
        // Type-valued fields already have an independently checked boxed
        // representation; they are not generic method templates themselves.
        for type_ in [c("Nat"), c("OrdinaryRecord"), c("CarrierRecord")] {
            assert!(!preparation.contains_generic_record(&type_).unwrap());
        }
        let mut limited = Preparation::new(
            environment,
            IngressLimits {
                max_nodes: 1,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            limited.contains_generic_record(&c("NestedTemplateRecord")),
            Err(IngressError::ResourceLimit { .. })
        ));
    }

    #[test]
    fn a_local_record_prefix_preserves_inner_and_outer_slots_and_has_no_cache_escape() {
        let environment = engine().environment();
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        let value = Expr::app(c("templateRecord"), b(0));
        // Before the let, #0 is the outer cost. Inside the added lambda,
        // #0 is its argument and #1 is the record's original placeholder.
        let consumer_body = Expr::lam(
            name("argument"),
            c("Nat"),
            Expr::app(
                Expr::app(Expr::proj(name("TemplateRecord"), 0, b(1)), c("Nat")),
                b(0),
            ),
            BinderInfo::Default,
        );
        let exposed = preparation
            .local_record_template(
                &name("record"),
                &c("TemplateRecord"),
                &value,
                &consumer_body,
            )
            .unwrap()
            .unwrap();
        let needed = preparation.visited;
        let ExprNode::LetE {
            value: first,
            body: after_first,
            ..
        } = exposed.node()
        else {
            panic!("the live capture needs a runtime binding");
        };
        assert_eq!(*first, Expr::app(c("templateWork"), b(0)));
        let ExprNode::LetE {
            value: second,
            body: after_second,
            ..
        } = after_first.node()
        else {
            panic!("the separate constructor operand needs its own binding");
        };
        assert_eq!(*second, Expr::app(c("templateWork"), b(1)));
        let ExprNode::Lam { body, .. } = after_second.node() else {
            panic!("the consumer lambda was lost");
        };
        let (head, arguments) = preparation.spine(body).unwrap();
        let ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } = head.node()
        else {
            panic!("the record placeholder was not substituted");
        };
        assert_eq!(arguments, [c("Nat"), b(0)]);
        let method = preparation
            .instance_factory_field(struct_name, *idx, expr)
            .unwrap()
            .unwrap();
        assert_eq!(
            preparation.static_apply(&method, &arguments).unwrap(),
            Some(b(2)),
            "the selected method must read paid, beyond the lambda and sibling slots"
        );
        assert!(preparation.specializations.factory_values_is_empty());
        let mut limited = Preparation::new(
            environment,
            IngressLimits {
                max_nodes: needed - 1,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            limited.local_record_template(
                &name("record"),
                &c("TemplateRecord"),
                &value,
                &consumer_body,
            ),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                ..
            })
        ));
        assert!(limited.specializations.factory_values_is_empty());
        limited.limits.max_nodes = needed * 3 + 32;
        assert_eq!(
            limited
                .local_record_template(
                    &name("record"),
                    &c("TemplateRecord"),
                    &value,
                    &consumer_body,
                )
                .unwrap(),
            Some(exposed)
        );
    }
}
