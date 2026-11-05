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
inductive CacheTree where
  | leaf : Nat → CacheTree
  | pair : CacheTree → CacheTree → CacheTree
def cacheLeafFactory (n : Nat) : CacheTree := CacheTree.leaf n
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

#[test]
fn shared_factory_subterms_fit_the_bound_for_completed_administrative_work() {
    fn tree(mut leaf: Expr) -> Expr {
        for _ in 0..25 {
            leaf = call("CacheTree.pair", [leaf.clone(), leaf]);
        }
        leaf
    }
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let source = tree(call("cacheLeafFactory", [nat::literal(42)]));
    let separate = call(
        "CacheTree.pair",
        [
            tree(call("cacheLeafFactory", [nat::literal(42)])),
            tree(call("cacheLeafFactory", [nat::literal(42)])),
        ],
    );
    let shared = call("CacheTree.pair", [source.clone(), source]);
    let expected = tree(call("CacheTree.leaf", [nat::literal(42)]));
    let expected = call("CacheTree.pair", [expected.clone(), expected]);
    let limits = IngressLimits {
        max_nodes: 2048,
        ..IngressLimits::default()
    };
    let mut left = Preparation::new(&engine.environment, limits);
    let mut right = Preparation::new(&engine.environment, limits);
    assert_eq!(
        left.instance_factory_value(&shared).unwrap(),
        Some(expected.clone())
    );
    assert_eq!(
        right.instance_factory_value(&separate).unwrap(),
        Some(expected)
    );
    assert_eq!(left.visited, right.visited);
    assert_eq!(engine.logical_root(&KVMap::new()), root);

    let mut limited = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: 32,
            ..IngressLimits::default()
        },
    );
    assert!(matches!(
        limited.instance_factory_value(&separate),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 32,
            observed: 33
        })
    ));
    assert!(limited.specializations.factory_values.is_empty());
}

#[test]
fn local_factory_reuse_keeps_unselected_computations_and_callers_separate() {
    let engine = engine();
    let branch = call("cacheFactory", [Expr::bvar(0).unwrap()]);
    let input = call("CacheDictionary.mk", [branch.clone(), branch]);
    let expected_branch = call(
        "CacheDictionary.mk",
        [Expr::bvar(0).unwrap(), Expr::bvar(0).unwrap()],
    );
    let expected = call(
        "CacheDictionary.mk",
        [expected_branch.clone(), expected_branch],
    );
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(
        preparation.scoped_instance_factory_value(&input).unwrap(),
        Some(expected)
    );
    let complete = preparation.visited;
    assert!(preparation.specializations.factory_values.is_empty());
    assert!(preparation.instance_factory_value(&input).unwrap().is_none());
    let before = preparation.visited;
    assert!(
        preparation.scoped_instance_factory_value(&input).unwrap().is_some()
    );
    assert_eq!(preparation.visited - before, complete);
    let shared = call("cacheLeafFactory", [nat::literal(42)]);
    let computed = call("cacheLeafFactory", [call("cacheRuntimeWork", [nat::literal(0)])]);
    let input = call(
        "CacheTree.pair",
        [shared.clone(), call("CacheTree.pair", [shared, computed])],
    );
    assert!(preparation.instance_factory_value(&input).unwrap().is_none());
    assert!(!preparation.specializations.factory_values.contains_key(&input));
}
