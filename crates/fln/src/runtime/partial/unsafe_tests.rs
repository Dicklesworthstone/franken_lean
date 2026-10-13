use super::*;

fn definition() -> DefinitionVal {
    let (_, mut executable) = tests::pair("unsafeBody");
    executable.base.name = name("unsafeBody");
    executable.all = vec![executable.base.name.clone()];
    executable.safety = DefinitionSafety::Unsafe;
    executable
}

#[test]
fn an_unsafe_body_is_executable_but_never_a_logical_reduction() {
    let definition = definition();
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(definition.clone()))
        .unwrap();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    assert_eq!(
        preparation
            .executable_definition(&definition.base.name)
            .unwrap(),
        Some(definition.clone())
    );
    let term = Expr::app(
        Expr::const_(definition.base.name.clone(), vec![]),
        nat::literal(7),
    );
    assert_eq!(preparation.type_head(&term).unwrap(), term);
    assert!(
        !preparation
            .has_recursive_companion(&definition.base.name)
            .unwrap()
    );
}

#[test]
fn unsafe_body_lookup_does_not_bypass_named_initializers() {
    let definition = definition();
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(definition.clone()))
        .unwrap();
    let initializers = BTreeSet::from([definition.base.name.clone()]);
    let mut preparation = Preparation::new(&environment, IngressLimits::default())
        .with_runtime_initializers(&initializers);
    assert!(
        preparation
            .executable_definition(&definition.base.name)
            .unwrap()
            .is_none()
    );
}

#[test]
fn an_unsafe_body_cannot_authorize_an_unlinked_partial_companion() {
    let definition = definition();
    let (_, executable) = tests::pair("unsafeBody");
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(definition.clone()))
        .unwrap()
        .add_decl(ConstantInfo::Defn(executable.clone()))
        .unwrap();
    for requested in [&definition.base.name, &executable.base.name] {
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .executable_definition(requested)
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn unsafe_lookup_remains_inside_the_existing_ingress_budget() {
    let definition = definition();
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(definition.clone()))
        .unwrap();
    let limits = IngressLimits {
        max_nodes: 0,
        ..IngressLimits::default()
    };
    assert!(matches!(
        Preparation::new(&environment, limits).executable_definition(&definition.base.name),
        Err(IngressError::ResourceLimit { .. })
    ));
}

#[test]
fn unsafe_opaque_execution_requires_explicit_value_authority() {
    let definition = definition();
    let opaque = OpaqueVal {
        base: definition.base.clone(),
        value: definition.value.clone(),
        all: definition.all.clone(),
        is_unsafe: true,
    };
    let environment = Environment::new()
        .add_decl(ConstantInfo::Opaque(opaque.clone()))
        .unwrap();
    let name = &opaque.base.name;
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .executable_definition(name)
            .unwrap()
            .is_none()
    );
    let allowed = BTreeSet::from([name.clone()]);
    let executable = Preparation::new(&environment, IngressLimits::default())
        .with_executable_opaques(&allowed)
        .executable_definition(name)
        .unwrap()
        .unwrap();
    assert_eq!(executable.safety, DefinitionSafety::Unsafe);
    assert_eq!(executable.base, opaque.base);
    assert_eq!(executable.value, opaque.value);
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .with_executable_opaques(&allowed)
            .with_runtime_initializers(&allowed)
            .executable_definition(name)
            .unwrap()
            .is_none()
    );
    let (_, companion) = tests::pair("unsafeBody");
    let malformed = environment.add_decl(ConstantInfo::Defn(companion)).unwrap();
    assert!(
        Preparation::new(&malformed, IngressLimits::default())
            .with_executable_opaques(&allowed)
            .executable_definition(name)
            .unwrap()
            .is_none()
    );
}
