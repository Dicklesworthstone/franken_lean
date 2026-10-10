use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn call(label: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    application(c(label), arguments)
}

fn engine() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[br#"
structure CacheDictionary where
  first : Nat
  second : Nat
def cacheFactory (n : Nat) : CacheDictionary := CacheDictionary.mk n n
def cacheRuntimeWork (n : Nat) : Nat := n + 1
"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn exact_closed_factory_reuse_is_metered_and_preserves_original_arguments() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let input = call("cacheFactory", [nat::literal(42)]);
    let original = input.clone();
    let expected = call("CacheDictionary.mk", [nat::literal(42), nat::literal(42)]);
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(
        preparation.instance_factory_value(&input).unwrap(),
        Some(expected.clone())
    );
    let work = preparation.visited;
    assert!(work > 1);
    assert_eq!(preparation.specializations.factory_values.len(), 1);
    preparation.limits.max_nodes = work + 1;
    // Independently rebuilt syntax has the same key; no pointer identity or
    // substitution of the caller's original specialization argument is used.
    assert_eq!(
        preparation
            .instance_factory_value(&call("cacheFactory", [nat::literal(42)]))
            .unwrap(),
        Some(expected)
    );
    assert_eq!(preparation.visited, work + 1);
    assert!(matches!(
        preparation.instance_factory_value(&input),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        }) if limit == work + 1 && observed == work + 2
    ));
    assert_eq!(input, original);
    assert!(preparation.specializations.instances.is_empty());
    assert!(preparation.specializations.definitions.is_empty());
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn cached_factories_cannot_hide_changed_discarded_operands_or_open_inputs() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let result = call("CacheDictionary.mk", [nat::literal(42), nat::literal(42)]);
    let ignoring = Expr::lam(
        name("ignored"),
        c("Nat"),
        result.clone(),
        BinderInfo::Default,
    );
    let inert = Expr::app(ignoring.clone(), nat::literal(0));
    assert_eq!(
        preparation.instance_factory_value(&inert).unwrap(),
        Some(result.clone())
    );
    let entries = preparation.specializations.factory_values.len();
    let computed = call("cacheRuntimeWork", [nat::literal(0)]);
    for input in [
        Expr::app(ignoring, computed.clone()),
        Expr::let_e(name("ignored"), c("Nat"), computed.clone(), result, false),
        call("CacheDictionary.mk", [nat::literal(42), computed]),
        call("cacheFactory", [Expr::bvar(0).unwrap()]),
        Expr::app(
            Expr::const_(name("cacheFactory"), vec![Level::one()]),
            nat::literal(42),
        ),
    ] {
        assert!(
            preparation
                .instance_factory_value(&input)
                .unwrap()
                .is_none()
        );
        assert!(
            !preparation
                .specializations
                .factory_values
                .contains_key(&input)
        );
    }
    assert_eq!(preparation.specializations.factory_values.len(), entries);
    let different = call("cacheFactory", [nat::literal(7)]);
    assert_eq!(
        preparation.instance_factory_value(&different).unwrap(),
        Some(call(
            "CacheDictionary.mk",
            [nat::literal(7), nat::literal(7)]
        ))
    );
    assert_eq!(
        preparation.specializations.factory_values.len(),
        entries + 1
    );
}

#[test]
fn unfinished_factory_evaluation_does_not_publish_and_can_retry() {
    let engine = engine();
    let input = call("cacheFactory", [nat::literal(42)]);
    let mut fresh = Preparation::new(&engine.environment, IngressLimits::default());
    let expected = fresh.instance_factory_value(&input).unwrap();
    let complete_work = fresh.visited;
    assert!(complete_work > 1);
    let mut limited = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: complete_work - 1,
            ..IngressLimits::default()
        },
    );
    // Stop at the completed-result insertion, after the evaluator has done its
    // administrative work. An exhausted publication must not create a hit.
    assert!(matches!(
        limited.instance_factory_value(&input),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        }) if limit == complete_work - 1 && observed == complete_work
    ));
    assert!(limited.specializations.factory_values.is_empty());
    limited.limits = IngressLimits::default();
    assert_eq!(limited.instance_factory_value(&input).unwrap(), expected);
    assert_eq!(limited.specializations.factory_values.len(), 1);
}
