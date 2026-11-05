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
structure CacheLayer (α : Type) where
  first : α
  second : α
def cacheLayer (α : Type) (x : α) : CacheLayer α := { first := x, second := x }
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

fn nested_factory(value: Expr, depth: usize) -> (Expr, Expr, Expr) {
    let mut type_ = c("Nat");
    let mut input = value.clone();
    let mut expected = value;
    for _ in 0..depth {
        input = call("cacheLayer", [type_.clone(), input]);
        expected = call("CacheLayer.mk", [type_.clone(), expected.clone(), expected]);
        type_ = call("CacheLayer", [type_]);
    }
    (input, expected, type_)
}

#[test]
fn nested_factories_reuse_completed_operands_with_bounded_work() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    // Each source-admitted factory duplicates an inert dictionary. Without
    // local reuse, beta reduction makes the evaluator validate the same tree
    // twice at every layer, even though every operand was already checked.
    for (leaf, scoped) in [
        (nat::literal(42), false),
        (nat::literal(42), true),
        (Expr::bvar(0).unwrap(), true),
        (Expr::bvar(3).unwrap(), true),
    ] {
        let (input, expected, _) = nested_factory(leaf, 16);
        let original = input.clone();
        let mut preparation = Preparation::new(
            &engine.environment,
            IngressLimits {
                max_nodes: 20_000,
                ..IngressLimits::default()
            },
        );
        let result = if scoped {
            preparation.scoped_instance_factory_value(&input)
        } else {
            preparation.instance_factory_value(&input)
        };
        assert_eq!(result.unwrap(), Some(expected));
        assert_eq!(input, original);
        if scoped {
            assert!(preparation.specializations.factory_values.is_empty());
        }
        assert!(preparation.specializations.instances.is_empty());
        assert!(preparation.specializations.definitions.is_empty());
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn scoped_factory_reuse_has_identical_fuel_for_shared_and_rebuilt_syntax() {
    let engine = engine();
    let (operand, result, type_) = nested_factory(Expr::bvar(2).unwrap(), 8);
    let shared = call("CacheLayer.mk", [type_.clone(), operand.clone(), operand]);
    let rebuilt = call(
        "CacheLayer.mk",
        [
            type_.clone(),
            nested_factory(Expr::bvar(2).unwrap(), 8).0,
            nested_factory(Expr::bvar(2).unwrap(), 8).0,
        ],
    );
    let expected = call("CacheLayer.mk", [type_, result.clone(), result]);
    for budget in [0, 64, 1_000, 20_000] {
        let limits = IngressLimits {
            max_nodes: budget,
            ..IngressLimits::default()
        };
        let mut left = Preparation::new(&engine.environment, limits);
        let mut right = Preparation::new(&engine.environment, limits);
        let left_result = left.scoped_instance_factory_value(&shared);
        let right_result = right.scoped_instance_factory_value(&rebuilt);
        assert_eq!(left_result, right_result);
        assert_eq!(left.visited, right.visited);
        if budget == 20_000 {
            assert_eq!(left_result.unwrap(), Some(expected.clone()));
        }
        assert!(left.specializations.factory_values.is_empty());
        assert!(right.specializations.factory_values.is_empty());
    }
}

#[test]
fn local_factory_reuse_keeps_different_captures_and_computed_siblings_distinct() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let (first, first_value, type_) = nested_factory(Expr::bvar(0).unwrap(), 8);
    let (second, second_value, _) = nested_factory(Expr::bvar(1).unwrap(), 8);
    let input = call("CacheLayer.mk", [type_.clone(), first.clone(), second]);
    assert_eq!(
        preparation.scoped_instance_factory_value(&input).unwrap(),
        Some(call(
            "CacheLayer.mk",
            [type_.clone(), first_value, second_value]
        ))
    );

    // The first field populates the invocation-local table. The second has
    // the same returned dictionary but a computed initializer; its complete
    // syntax differs, and reusing the first result must not erase that work.
    let computed = Expr::let_e(
        name("unused"),
        c("Nat"),
        call("cacheRuntimeWork", [nat::literal(0)]),
        first.clone(),
        false,
    );
    let input = call("CacheLayer.mk", [type_, first, computed]);
    assert!(
        preparation
            .scoped_instance_factory_value(&input)
            .unwrap()
            .is_none()
    );
    assert!(preparation.specializations.factory_values.is_empty());
    assert!(preparation.specializations.instances.is_empty());
    assert!(preparation.specializations.definitions.is_empty());
}

#[test]
fn interrupted_scoped_factory_evaluation_can_retry_without_publishing_partial_values() {
    let engine = engine();
    let (input, expected, _) = nested_factory(Expr::bvar(1).unwrap(), 8);
    let mut complete = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(
        complete.scoped_instance_factory_value(&input).unwrap(),
        Some(expected.clone())
    );
    let limit = complete.visited / 2;
    assert!(limit > 0);
    let mut limited = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: limit,
            ..IngressLimits::default()
        },
    );
    assert!(matches!(
        limited.scoped_instance_factory_value(&input),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: actual,
            observed,
        }) if actual == limit && observed == limit + 1
    ));
    assert!(limited.specializations.factory_values.is_empty());
    assert!(limited.specializations.instances.is_empty());
    assert!(limited.specializations.definitions.is_empty());

    limited.limits = IngressLimits::default();
    assert_eq!(
        limited.scoped_instance_factory_value(&input).unwrap(),
        Some(expected)
    );
    assert!(limited.specializations.factory_values.is_empty());
}
