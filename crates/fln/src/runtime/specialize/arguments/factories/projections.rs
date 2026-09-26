//! Select a field only after the complete factory receiver proved inert.
use super::*;

impl Preparation<'_> {
    pub(super) fn instance_factory_field(
        &mut self,
        family: &Name,
        index: u64,
        value: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        self.tick()?;
        let (head, arguments) = self.spine(value)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(constructor)) = self.environment.find(name) else {
            return Ok(None);
        };
        let parameters = constructor.num_params as usize;
        let fields = constructor.num_fields as usize;
        let Some(arity) = parameters.checked_add(fields) else {
            return Err(unsupported("instance projection arity"));
        };
        let Ok(index) = usize::try_from(index) else {
            return Ok(None);
        };
        if constructor.is_unsafe
            || constructor.induct != *family
            || levels.len() != constructor.base.level_params.len()
            || arguments.len() != arity
            || index >= fields
        {
            return Ok(None);
        }
        // Constructor parameters precede fields. The caller's heap evaluator
        // has already checked ALL operands, including the unselected fields;
        // selecting one must not erase an arbitrary sibling initializer.
        Ok(Some(arguments[parameters + index].clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_env::constants::{AxiomVal, ConstantVal, ConstructorVal};

    fn c(label: &str) -> Expr {
        Expr::const_(name(label), vec![])
    }
    fn dictionary(first: Expr, second: Expr) -> Expr {
        application(c("Dictionary.mk"), [Expr::sort(Level::zero()), first, second])
    }
    fn project(index: u64, value: Expr) -> Expr {
        Expr::proj(name("Dictionary"), index, value)
    }
    fn environment() -> Environment {
        // Metadata producer fixture, not a kernel-admitted declaration.
        Environment::new()
            .add_decl(ConstantInfo::Ctor(ConstructorVal {
                base: ConstantVal {
                    name: name("Dictionary.mk"),
                    level_params: vec![],
                    type_: Expr::sort(Level::one()),
                },
                induct: name("Dictionary"),
                cidx: 0,
                num_params: 1,
                num_fields: 2,
                is_unsafe: false,
            }))
            .unwrap()
    }
    fn evaluate(input: &Expr) -> Option<Expr> {
        let environment = environment();
        Preparation::new(&environment, IngressLimits::default())
            .instance_factory_value(input)
            .unwrap()
    }

    #[test]
    fn nested_parent_dictionary_projections_skip_parameters_not_fields() {
        let inner = dictionary(nat::literal(41), nat::literal(42));
        let outer = dictionary(inner, nat::literal(0));
        assert_eq!(
            evaluate(&project(1, project(0, outer))),
            Some(nat::literal(42))
        );
    }

    #[test]
    fn projected_factory_callbacks_are_applied_through_the_same_task_machine() {
        let field = Expr::lam(
            Name::anonymous(),
            c("Nat"),
            dictionary(Expr::bvar(0).unwrap(), Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        let input = Expr::app(
            project(0, dictionary(field, nat::literal(0))),
            nat::literal(42),
        );
        assert_eq!(
            evaluate(&input),
            Some(dictionary(nat::literal(42), nat::literal(42)))
        );
    }

    #[test]
    fn unselected_computations_and_receiver_initializers_cannot_disappear() {
        let computed = Expr::app(c("runtimeComputation"), nat::literal(3));
        assert!(evaluate(&project(0, dictionary(nat::literal(42), computed.clone()))).is_none());
        let receiver = Expr::let_e(
            name("unused"),
            c("Nat"),
            computed,
            dictionary(nat::literal(42), nat::literal(0)),
            false,
        );
        assert!(evaluate(&project(0, receiver)).is_none());
    }

    #[test]
    fn wrong_family_bad_index_underapplication_and_universe_mismatch_are_refused() {
        let value = dictionary(nat::literal(41), nat::literal(42));
        for input in [
            Expr::proj(name("OtherDictionary"), 0, value.clone()),
            project(2, value.clone()),
            project(u64::MAX, value),
            project(0, Expr::app(c("Dictionary.mk"), Expr::sort(Level::zero()))),
            project(
                0,
                application(
                    Expr::const_(name("Dictionary.mk"), vec![Level::one()]),
                    [Expr::sort(Level::zero()), nat::literal(41), nat::literal(42)],
                ),
            ),
        ] {
            assert!(evaluate(&input).is_none());
        }
    }

    #[test]
    fn opaque_type_parameters_are_metadata_but_axiomatic_values_are_not_code() {
        let environment = environment()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: name("OpaqueType"),
                    level_params: vec![],
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }))
            .unwrap()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: name("runtimeAxiom"),
                    level_params: vec![],
                    type_: c("OpaqueType"),
                },
                is_unsafe: false,
            }))
            .unwrap();
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        let inert = application(
            c("Dictionary.mk"),
            [c("OpaqueType"), nat::literal(41), nat::literal(42)],
        );
        assert_eq!(
            preparation.instance_factory_value(&inert).unwrap(),
            Some(inert)
        );
        let invalid = application(
            c("Dictionary.mk"),
            [c("runtimeAxiom"), nat::literal(41), nat::literal(42)],
        );
        assert!(preparation.instance_factory_value(&invalid).unwrap().is_none());
        let bad_level = Expr::const_(name("OpaqueType"), vec![Level::one()]);
        assert!(preparation.instance_factory_value(&bad_level).unwrap().is_none());
    }

    #[test]
    fn deeply_nested_projection_factories_are_heap_backed_and_metered() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut input = nat::literal(42);
                for _ in 0..2000 {
                    input = project(0, dictionary(input, nat::literal(0)));
                }
                let environment = environment();
                let mut limited = Preparation::new(
                    &environment,
                    IngressLimits {
                        max_nodes: 64,
                        ..IngressLimits::default()
                    },
                );
                assert!(matches!(
                    limited.instance_factory_value(&input),
                    Err(IngressError::ResourceLimit { .. })
                ));
                assert!(limited.specializations.instances.is_empty());
                assert!(limited.specializations.definitions.is_empty());
                assert_eq!(evaluate(&input), Some(nat::literal(42)));
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
