use super::*;
use fln_env::constants::{ConstantVal, DefinitionSafety, OpaqueVal, ReducibilityHints};

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

fn vector(element: Expr, index: Expr) -> Expr {
    app(c("CacheVec"), [element, index])
}

fn engine() -> &'static Engine {
    static ENGINE: std::sync::OnceLock<Engine> = std::sync::OnceLock::new();
    ENGINE.get_or_init(|| {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        let mut engine = Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[br#"
inductive CacheVec (A : Type) : Nat -> Type where
  | nil : CacheVec A 0
  | cons (n : Nat) (head : A) (tail : CacheVec A n) : CacheVec A (Nat.succ n)
def cacheIndexAlias (A : Type) (n : Nat) : Type := CacheVec A n
structure CachePayload where
  flag : Bool
  value : if flag then Nat else String
inductive CacheBad where
  | mk (callback : Nat -> CacheBad) (payload : CachePayload)
"#],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;

        // Partial source authoring is a separate frontend boundary. Admit
        // both checked halves directly so the erased index still contains
        // a genuinely nonreturning native computation.
        let logical = name("cacheIndexLoop");
        let executable = Name::str(logical.clone(), "_unsafe_rec");
        let type_ = Expr::forall_e(name("n"), c("Nat"), c("Nat"), BinderInfo::Default);
        for declaration in [
            Declaration::Opaque(OpaqueVal {
                base: ConstantVal {
                    name: logical.clone(),
                    level_params: vec![],
                    type_: type_.clone(),
                },
                value: Expr::lam(name("n"), c("Nat"), nat::literal(0), BinderInfo::Default),
                is_unsafe: false,
                all: vec![logical],
            }),
            Declaration::Mutual(vec![DefinitionVal {
                base: ConstantVal {
                    name: executable.clone(),
                    level_params: vec![],
                    type_,
                },
                value: Expr::lam(
                    name("n"),
                    c("Nat"),
                    Expr::app(Expr::const_(executable.clone(), vec![]), b(0)),
                    BinderInfo::Default,
                ),
                hints: ReducibilityHints::Opaque,
                safety: DefinitionSafety::Partial,
                all: vec![executable],
            }]),
        ] {
            engine = engine
                .admit_declaration(declaration, &KVMap::new(), limits)
                .unwrap()
                .into_complete()
                .unwrap()
                .engine;
        }
        engine
    })
}

fn nodes_error<T>(result: Result<T, IngressError>, limit: usize) {
    assert_eq!(
        result.err(),
        Some(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed: limit + 1,
        })
    );
}

#[test]
fn universe_syntax_needs_one_visit_and_no_cache_row() {
    let environment = Environment::new();
    for level in [Level::zero(), Level::one()] {
        let source = Expr::sort(level);
        let mut preparation = Preparation::new(
            &environment,
            IngressLimits {
                max_nodes: 1,
                max_context_depth: 0,
                max_application_args: 0,
                ..IngressLimits::default()
            },
        );
        assert_eq!(preparation.erase_data_indices(&source).unwrap(), source);
        assert_eq!(preparation.visited, 1);
        assert!(preparation.specializations.index_types.entries.is_empty());
        nodes_error(preparation.erase_data_indices(&source), 1);
    }
}

#[test]
fn completed_exact_types_reuse_results_without_conflating_static_arguments_or_running_indices() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let nat_vector = Expr::app(c("CacheVec"), c("Nat"));
    let string_vector = Expr::app(c("CacheVec"), c("String"));
    let zero = vector(c("Nat"), nat::literal(0));
    let cases = [
        (zero.clone(), nat_vector.clone()),
        (vector(c("Nat"), nat::literal(42)), nat_vector.clone()),
        (vector(c("String"), nat::literal(0)), string_vector),
        (
            vector(c("Nat"), Expr::app(c("cacheIndexLoop"), nat::literal(0))),
            nat_vector.clone(),
        ),
        (Expr::mdata(KVMap::new(), zero), nat_vector.clone()),
        (
            Expr::forall_e(name("kept"), c("Nat"), nat_vector, BinderInfo::Implicit),
            Expr::forall_e(
                name("kept"),
                c("Nat"),
                Expr::app(c("CacheVec"), c("Nat")),
                BinderInfo::Implicit,
            ),
        ),
    ];
    for (source, expected) in &cases {
        let original = source.clone();
        assert_eq!(preparation.erase_data_indices(source).unwrap(), *expected);
        assert_eq!(*source, original);
        assert!(
            preparation
                .specializations
                .index_types
                .entries
                .contains_key(source)
        );
    }
    assert_eq!(
        preparation.specializations.index_types.entries.len(),
        cases.len()
    );
    for (source, expected) in &cases {
        let before = preparation.visited;
        assert_eq!(preparation.erase_data_indices(source).unwrap(), *expected);
        assert_eq!(preparation.visited, before + 1);
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn open_inputs_and_results_do_not_publish_closed_type_evidence() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let open_element = vector(b(0), nat::literal(7));
    let open_index = vector(c("Nat"), b(0));
    for (source, expected) in [
        (open_element, Expr::app(c("CacheVec"), b(0))),
        (open_index, Expr::app(c("CacheVec"), c("Nat"))),
    ] {
        assert!(!specialize::closed(&source));
        assert_eq!(preparation.erase_data_indices(&source).unwrap(), expected);
        assert!(
            !preparation
                .specializations
                .index_types
                .entries
                .contains_key(&source)
        );
    }
    assert!(preparation.specializations.index_types.entries.is_empty());
}

#[test]
fn canonical_definition_and_native_carrier_generations_invalidate_completed_results() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let future = Expr::const_(Name::num(name("_fln_runtime_specialization"), 0), vec![]);
    let source = Expr::app(future.clone(), nat::literal(7));
    assert_eq!(preparation.erase_data_indices(&source).unwrap(), source);
    assert_eq!(
        preparation.specializations.index_types.entries[&source]
            .generation
            .definitions,
        0
    );
    assert_eq!(
        preparation
            .specialize_call(&c("cacheIndexAlias"), &[c("Nat")])
            .unwrap()
            .unwrap(),
        future
    );
    let expected = Expr::app(c("CacheVec"), c("Nat"));
    assert_eq!(preparation.erase_data_indices(&source).unwrap(), expected);
    assert_eq!(
        preparation.specializations.index_types.entries[&source]
            .generation
            .definitions,
        1
    );

    // Native contract owners can register scalar carrier descriptions later
    // in preparation. This private metadata fixture checks invalidation, not
    // source or native-operation authorization.
    preparation.value_types.native.insert(
        c("_fln_test_index_scalar"),
        (ValueType::Bool, CallableResultOwnership::Scalar),
    );
    let before = preparation.visited;
    assert_eq!(preparation.erase_data_indices(&source).unwrap(), expected);
    assert!(preparation.visited > before + 1);
    assert_eq!(
        preparation.specializations.index_types.entries[&source]
            .generation
            .native,
        1
    );
    let before = preparation.visited;
    assert_eq!(preparation.erase_data_indices(&source).unwrap(), expected);
    assert_eq!(preparation.visited, before + 1);
}

#[test]
fn cached_erasure_preserves_tighter_application_and_telescope_limits() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let source = vector(c("Nat"), nat::literal(99));
    let expected = preparation.erase_data_indices(&source).unwrap();
    preparation.limits.max_application_args = 1;
    assert_eq!(
        preparation.erase_data_indices(&source),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ApplicationArguments,
            limit: 1,
            observed: 2,
        })
    );
    preparation.limits.max_application_args = IngressLimits::default().max_application_args;
    preparation.limits.max_context_depth = 0;
    assert_eq!(
        preparation.erase_data_indices(&source),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: 0,
            observed: 1,
        })
    );
    preparation.limits.max_context_depth = IngressLimits::default().max_context_depth;
    assert_eq!(preparation.erase_data_indices(&source).unwrap(), expected);
}

#[test]
fn failed_computations_and_bounded_insertions_remain_retryable() {
    let engine = engine();
    let source = vector(c("Nat"), nat::literal(42));
    let mut baseline = Preparation::new(&engine.environment, IngressLimits::default());
    let expected = baseline.erase_data_indices(&source).unwrap();
    let needed = baseline.visited;
    let mut preparation = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: needed - 1,
            ..IngressLimits::default()
        },
    );
    nodes_error(preparation.erase_data_indices(&source), needed - 1);
    assert!(preparation.specializations.index_types.entries.is_empty());
    preparation.limits.max_nodes = IngressLimits::default().max_nodes;
    assert_eq!(preparation.erase_data_indices(&source).unwrap(), expected);
    let before = preparation.visited;
    preparation.limits.max_nodes = before + 1;
    assert_eq!(preparation.erase_data_indices(&source).unwrap(), expected);
    assert_eq!(preparation.visited, before + 1);
    nodes_error(preparation.erase_data_indices(&source), before + 1);

    let entry = |definitions| Entry {
        generation: Generation {
            definitions,
            native: 0,
        },
        limits: Limits::from(IngressLimits::default()),
        result: expected.clone(),
    };
    let mut store = Store::default();
    store.remember(source.clone(), entry(0), 1).unwrap();
    nodes_error(store.remember(c("anotherKey"), entry(0), 1), 1);
    assert_eq!(store.entries.len(), 1);
    store.remember(source.clone(), entry(1), 1).unwrap();
    assert_eq!(store.entries.len(), 1);
    assert_eq!(store.entries[&source].generation.definitions, 1);
}

#[test]
fn completed_type_syntax_survives_unrelated_layout_rollback() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let source = vector(c("Nat"), nat::literal(42));
    let expected = preparation.erase_data_indices(&source).unwrap();
    let interfaces = preparation.interfaces.len();
    let constructors = preparation.constructors.len();
    assert_eq!(preparation.value_type(&c("CacheBad")).unwrap(), None);
    assert_eq!(preparation.interfaces.len(), interfaces);
    assert_eq!(preparation.constructors.len(), constructors);
    assert!(!preparation.value_types.records.contains(&c("CacheBad")));
    assert!(
        preparation.value_types.closures.values().all(
            |value| matches!(value, ValueType::Closure(id) if (id.get() as usize) < interfaces)
        )
    );
    let before = preparation.visited;
    assert_eq!(preparation.erase_data_indices(&source).unwrap(), expected);
    assert_eq!(preparation.visited, before + 1);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
