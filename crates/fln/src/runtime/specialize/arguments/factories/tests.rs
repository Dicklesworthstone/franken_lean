//! Structural compiler tests, not a second declaration-admission path.
use super::*;
use fln_env::constants::{AxiomVal, ConstantVal, ConstructorVal, ReducibilityHints};

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}
fn pi(domain: Expr, body: Expr, info: BinderInfo) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, info)
}
fn call(label: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    application(c(label), arguments)
}
fn definition(environment: Environment, label: &str, type_: Expr, value: Expr) -> Environment {
    environment
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: name(label),
                level_params: vec![],
                type_,
            },
            value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![],
        }))
        .unwrap()
}
fn environment() -> Environment {
    let environment = Environment::new()
        .add_decl(ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: name("Dictionary.mk"),
                level_params: vec![],
                type_: pi(
                    c("Nat"),
                    pi(c("Nat"), c("Dictionary"), BinderInfo::Default),
                    BinderInfo::Default,
                ),
            },
            induct: name("Dictionary"),
            cidx: 0,
            num_params: 0,
            num_fields: 2,
            is_unsafe: false,
        }))
        .unwrap();
    definition(
        environment,
        "factory",
        pi(c("Nat"), c("Dictionary"), BinderInfo::Default),
        lam(c("Nat"), call("Dictionary.mk", [b(0), b(0)])),
    )
}
fn evaluate(environment: &Environment, expression: &Expr) -> Option<Expr> {
    Preparation::new(environment, IngressLimits::default())
        .instance_factory_value(expression)
        .unwrap()
}

#[test]
fn applied_factories_produce_inert_constructor_values_without_changing_inputs() {
    let environment = environment();
    let input = call("factory", [nat::literal(42)]);
    let original = input.clone();
    assert_eq!(
        evaluate(&environment, &input),
        Some(call("Dictionary.mk", [nat::literal(42), nat::literal(42)]))
    );
    assert_eq!(input, original);
    assert_eq!(evaluate(&environment, &input), evaluate(&environment, &input));
}

#[test]
fn inert_let_values_and_constructor_function_aliases_are_supported() {
    let environment = definition(
        environment(),
        "constructorAlias",
        pi(
            c("Nat"),
            pi(c("Nat"), c("Dictionary"), BinderInfo::Default),
            BinderInfo::Default,
        ),
        c("Dictionary.mk"),
    );
    let input = Expr::let_e(
        name("saved"),
        c("Nat"),
        Expr::app(lam(c("Nat"), b(0)), nat::literal(7)),
        call("constructorAlias", [b(0), b(0)]),
        false,
    );
    assert_eq!(
        evaluate(&environment, &input),
        Some(call("Dictionary.mk", [nat::literal(7), nat::literal(7)]))
    );
}

#[test]
fn function_fields_are_code_not_computations_to_execute_during_specialization() {
    let environment = environment();
    let field = lam(c("Nat"), call("notACompileTimePrimitive", [b(0)]));
    let dictionary = call("Dictionary.mk", [nat::literal(0), field]);
    assert_eq!(evaluate(&environment, &dictionary), Some(dictionary));
}

#[test]
fn beta_zeta_and_constructor_building_cannot_discard_unproved_inertness() {
    let environment = environment();
    let computed = call("runtimeComputation", [nat::literal(0)]);
    for input in [
        Expr::app(lam(c("Nat"), nat::literal(42)), computed.clone()),
        Expr::let_e(
            name("unused"),
            c("Nat"),
            computed.clone(),
            nat::literal(42),
            false,
        ),
        call("Dictionary.mk", [nat::literal(42), computed.clone()]),
        call("Dictionary.mk", [computed, nat::literal(42)]),
    ] {
        assert!(evaluate(&environment, &input).is_none());
    }
    let value_parameter = environment
        .add_decl(ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: name("Indexed.mk"),
                level_params: vec![],
                type_: c("Nat"),
            },
            induct: name("Indexed"),
            cidx: 0,
            num_params: 1,
            num_fields: 0,
            is_unsafe: false,
        }))
        .unwrap();
    assert!(
        evaluate(
            &value_parameter,
            &call("Indexed.mk", [call("runtimeComputation", [])])
        )
        .is_none()
    );
}

#[test]
fn unsafe_partial_axiomatic_open_and_malformed_values_are_not_factory_evidence() {
    let mut environment = environment();
    for (label, safety) in [
        ("unsafeFactory", DefinitionSafety::Unsafe),
        ("partialFactory", DefinitionSafety::Partial),
    ] {
        environment = environment
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: name(label),
                    level_params: vec![],
                    type_: c("Nat"),
                },
                value: nat::literal(42),
                hints: ReducibilityHints::Abbrev,
                safety,
                all: vec![],
            }))
            .unwrap();
        assert!(evaluate(&environment, &c(label)).is_none());
    }
    environment = environment
        .add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: name("axiomatic"),
                level_params: vec![],
                type_: c("Nat"),
            },
            is_unsafe: false,
        }))
        .unwrap();
    for expression in [
        c("axiomatic"),
        b(0),
        call(
            "Dictionary.mk",
            [nat::literal(0), nat::literal(1), nat::literal(2)],
        ),
        Expr::const_(name("Dictionary.mk"), vec![Level::one()]),
    ] {
        assert!(evaluate(&environment, &expression).is_none());
    }
}

#[test]
fn private_bodies_receive_normalized_dictionaries_but_keys_keep_original_arguments() {
    let environment = environment();
    let type_ = pi(
        c("Nat"),
        pi(c("Dictionary"), c("Dictionary"), BinderInfo::InstImplicit),
        BinderInfo::Default,
    );
    let value = lam(
        c("Nat"),
        Expr::lam(Name::anonymous(), c("Dictionary"), b(0), BinderInfo::InstImplicit),
    );
    let input = call("factory", [nat::literal(42)]);
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let result = preparation
        .specialize_arguments(type_, value, &[b(0), input.clone()])
        .unwrap();
    assert_eq!(result.static_arguments, vec![(1, input)]);
    assert_eq!(result.runtime_arguments, vec![b(0)]);
    assert_eq!(
        result.value,
        lam(c("Nat"), call("Dictionary.mk", [nat::literal(42), nat::literal(42)]))
    );
    assert!(!result.value.has_loose_bvars());
}

#[test]
fn universe_instantiation_uses_the_factorys_real_level_arguments() {
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: name("universeFactory"),
                level_params: vec![name("u")],
                type_: pi(
                    Expr::sort(Level::param(name("u"))),
                    Expr::sort(Level::param(name("u"))),
                    BinderInfo::Default,
                ),
            },
            value: lam(Expr::sort(Level::param(name("u"))), b(0)),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![],
        }))
        .unwrap();
    let value = Expr::sort(Level::zero());
    let input = Expr::app(
        Expr::const_(name("universeFactory"), vec![Level::one()]),
        value.clone(),
    );
    assert_eq!(evaluate(&environment, &input), Some(value));
    assert!(evaluate(&environment, &c("universeFactory")).is_none());
}

#[test]
fn administrative_depth_is_heap_backed_and_resource_stops_leave_no_publication() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let identity = lam(c("Nat"), b(0));
            let mut input = nat::literal(42);
            for _ in 0..3000 {
                input = Expr::app(identity.clone(), input);
            }
            let environment = Environment::new();
            let mut limited = Preparation::new(
                &environment,
                IngressLimits {
                    max_nodes: 32,
                    ..IngressLimits::default()
                },
            );
            assert!(matches!(
                limited.instance_factory_value(&input),
                Err(IngressError::ResourceLimit { .. })
            ));
            assert!(limited.specializations.instances.is_empty());
            assert!(limited.specializations.definitions.is_empty());
            assert_eq!(evaluate(&environment, &input), Some(nat::literal(42)));
        })
        .unwrap()
        .join()
        .unwrap();
}
