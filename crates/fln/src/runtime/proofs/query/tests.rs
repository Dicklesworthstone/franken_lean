use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn metadata(value: Expr) -> Expr {
    Expr::mdata(KVMap::new(), value)
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn equality(value: Expr) -> Expr {
    app(
        Expr::const_(name("Eq"), vec![Level::one()]),
        [c("Nat"), value.clone(), value],
    )
}

fn engine() -> &'static Engine {
    static ENGINE: std::sync::OnceLock<Engine> = std::sync::OnceLock::new();
    ENGINE.get_or_init(|| {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[br#"
def queryMonomorphicType : Type := Nat
def queryMonomorphicProposition : Prop := True
def querySort (_ : Nat) : Type := Prop
def queryPredicate : querySort 0 := True
def queryFamily (A : Type) (_ : Nat) : Prop := True
structure QueryHolder (A : Type) where
  predicate : A -> Prop
structure QueryPayload where
  flag : Bool
  value : if flag then Nat else String
inductive QueryBad where
  | mk (callback : Nat -> QueryBad) (payload : QueryPayload)
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
fn completed_closed_sort_answers_reuse_exact_syntax_without_copying_contexts() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let context = vec![c("Nat"); 256];
    let cases = [
        (metadata(c("Nat")), false),
        (metadata(metadata(c("True"))), true),
        (equality(nat::literal(42)), true),
        (equality(nat::literal(7)), true),
        (pi(c("Nat"), equality(b(0))), true),
        (pi(c("Nat"), c("Nat")), false),
        (Expr::mdata(KVMap::new(), c("True")), true),
    ];
    for (source, expected) in &cases {
        assert!(specialize::closed(source));
        assert_eq!(
            preparation.proposition_type(source, &context).unwrap(),
            *expected
        );
        let entry = &preparation.proposition_queries.entries[&(source.clone(), context.len())];
        assert_eq!(entry.proposition, *expected);
    }
    assert_eq!(preparation.proposition_queries.entries.len(), cases.len());
    for (source, expected) in &cases {
        let start = preparation.visited;
        assert_eq!(
            preparation.proposition_type(source, &context).unwrap(),
            *expected
        );
        assert_eq!(preparation.visited, start + 1);
    }
    // A closed query uses only the size of the surrounding telescope. Its
    // unrelated slot types may change without changing that completed answer.
    let other_context = vec![c("String"); context.len()];
    let start = preparation.visited;
    assert!(
        preparation
            .proposition_type(&equality(nat::literal(42)), &other_context)
            .unwrap()
    );
    assert_eq!(preparation.visited, start + 1);
    let rows = preparation.proposition_queries.entries.len();
    for level in [Level::zero(), Level::one()] {
        let start = preparation.visited;
        assert!(
            !preparation
                .proposition_type(&Expr::sort(level), &context)
                .unwrap()
        );
        assert_eq!(preparation.visited, start + 1);
    }
    assert_eq!(preparation.proposition_queries.entries.len(), rows);
    assert_eq!(context, vec![c("Nat"); 256]);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn open_and_unknown_queries_never_borrow_another_scope_or_publish_a_false_answer() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let source = pi(b(0), b(1));
    assert!(!specialize::closed(&source));
    for (sort, expected) in [(Level::zero(), true), (Level::one(), false)] {
        assert_eq!(
            preparation
                .proposition_type(&source, &[Expr::sort(sort)])
                .unwrap(),
            expected
        );
    }
    assert!(!preparation.proposition_type(&b(0), &[]).unwrap());
    assert!(preparation.proposition_queries.entries.is_empty());

    // This exact future head has no type yet. No negative cache row may hide
    // its subsequently checked canonical specialization.
    let future = Expr::const_(
        Name::num(name("_fln_runtime_specialization"), 0),
        Vec::new(),
    );
    let applied = Expr::app(future.clone(), nat::literal(3));
    assert!(!preparation.proposition_type(&applied, &[]).unwrap());
    assert!(preparation.proposition_queries.entries.is_empty());
    let specialized = preparation
        .specialize_call(&c("queryFamily"), &[c("Nat")])
        .unwrap()
        .unwrap();
    assert_eq!(specialized, future);
    assert!(preparation.proposition_type(&applied, &[]).unwrap());
    assert!(
        preparation
            .proposition_queries
            .entries
            .contains_key(&(applied, 0))
    );
}

#[test]
fn completed_queries_recheck_after_canonical_declarations_and_private_shapes_grow() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let source = metadata(c("True"));
    assert!(preparation.proposition_type(&source, &[]).unwrap());
    assert_eq!(
        preparation.proposition_queries.entries[&(source.clone(), 0)]
            .generation
            .definitions,
        0
    );
    preparation
        .specialize_call(&c("queryFamily"), &[c("Nat")])
        .unwrap()
        .unwrap();
    let start = preparation.visited;
    assert!(preparation.proposition_type(&source, &[]).unwrap());
    assert!(preparation.visited > start + 1);
    assert_eq!(
        preparation.proposition_queries.entries[&(source.clone(), 0)]
            .generation
            .definitions,
        1
    );

    let holder = Expr::app(c("QueryHolder"), c("Nat"));
    let constructor = app(
        c("QueryHolder.mk"),
        [
            c("Nat"),
            Expr::lam(
                Name::anonymous(),
                c("Nat"),
                equality(b(0)),
                BinderInfo::Default,
            ),
        ],
    );
    let private = Name::num(
        name("_fln_runtime_data"),
        u64::try_from(preparation.data_shapes.len()).unwrap(),
    );
    let projection = Expr::app(
        Expr::proj(private.clone(), 0, constructor),
        nat::literal(42),
    );
    let rows = preparation.proposition_queries.entries.len();
    assert_eq!(
        preparation.proposition_type(&projection, &[]),
        Err(unsupported("projection receiver family mismatch"))
    );
    assert_eq!(preparation.proposition_queries.entries.len(), rows);
    let shape = preparation.record_shape(&holder).unwrap().unwrap();
    assert_eq!(shape.name, private);
    assert!(preparation.proposition_type(&projection, &[]).unwrap());
    let start = preparation.visited;
    assert!(preparation.proposition_type(&source, &[]).unwrap());
    assert!(preparation.visited > start + 1);
    let entry = &preparation.proposition_queries.entries[&(source, 0)];
    assert_eq!(entry.generation.shapes, preparation.data_shapes.len());
}

#[test]
fn cached_answers_keep_total_depth_and_tighter_reduction_limits() {
    let engine = engine();
    let mut preparation = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_context_depth: 3,
            ..IngressLimits::default()
        },
    );
    let source = pi(c("Nat"), c("True"));
    assert!(preparation.proposition_type(&source, &[c("Nat")]).unwrap());
    assert!(
        preparation
            .proposition_type(&source, &[c("Nat"), c("String")])
            .unwrap()
    );
    assert_eq!(preparation.proposition_queries.entries.len(), 2);
    assert_eq!(
        preparation.proposition_type(&source, &vec![c("Nat"); 3]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 3,
            observed: 4,
        })
    );
    preparation.limits.max_context_depth = 1;
    assert_eq!(
        preparation.proposition_type(&source, &[c("Nat")]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 1,
            observed: 2,
        })
    );
    preparation.limits.max_context_depth = 3;
    assert!(preparation.proposition_type(&source, &[c("Nat")]).unwrap());

    let predicate = c("queryPredicate");
    assert!(preparation.proposition_type(&predicate, &[]).unwrap());
    preparation.limits.max_application_args = 0;
    assert_eq!(
        preparation.proposition_type(&predicate, &[]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ApplicationArguments,
            limit: 0,
            observed: 1,
        })
    );
    preparation.limits.max_application_args = IngressLimits::default().max_application_args;
    assert!(preparation.proposition_type(&predicate, &[]).unwrap());
}

#[test]
fn exhausted_queries_never_publish_and_completed_hits_still_spend_work() {
    let engine = engine();
    let source = equality(nat::literal(42));
    let mut baseline = Preparation::new(&engine.environment, IngressLimits::default());
    assert!(baseline.proposition_type(&source, &[]).unwrap());
    let needed = baseline.visited;

    let mut preparation = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: needed - 1,
            ..IngressLimits::default()
        },
    );
    nodes_error(preparation.proposition_type(&source, &[]), needed - 1);
    assert!(preparation.proposition_queries.entries.is_empty());
    preparation.limits.max_nodes = IngressLimits::default().max_nodes;
    assert!(preparation.proposition_type(&source, &[]).unwrap());
    let start = preparation.visited;
    preparation.limits.max_nodes = start + 1;
    assert!(preparation.proposition_type(&source, &[]).unwrap());
    assert_eq!(preparation.visited, start + 1);
    nodes_error(preparation.proposition_type(&source, &[]), start + 1);
    assert!(preparation.proposition_queries.entries[&(source, 0)].proposition);

    let mut empty = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        },
    );
    nodes_error(empty.proposition_type(&c("True"), &[]), 0);
    assert!(empty.proposition_queries.entries.is_empty());
}

#[test]
fn descriptive_classification_survives_real_closure_layout_rollback() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let source = pi(c("Nat"), equality(b(0)));
    assert!(preparation.proposition_type(&source, &[]).unwrap());
    let interfaces = preparation.interfaces.len();
    let constructors = preparation.constructors.len();
    assert_eq!(preparation.value_type(&c("QueryBad")).unwrap(), None);
    assert_eq!(preparation.interfaces.len(), interfaces);
    assert_eq!(preparation.constructors.len(), constructors);
    assert!(!preparation.value_types.records.contains(&c("QueryBad")));
    assert!(
        preparation.value_types.closures.values().all(
            |value| matches!(value, ValueType::Closure(id) if (id.get() as usize) < interfaces)
        )
    );
    assert!(preparation.proposition_type(&source, &[]).unwrap());
    let start = preparation.visited;
    assert!(preparation.proposition_type(&source, &[]).unwrap());
    assert_eq!(preparation.visited, start + 1);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn admitted_monomorphic_sorts_need_one_visit_and_no_context_copy_or_cache_row() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let context = vec![c("Nat"); 256];
    let other_context = vec![c("String"); context.len()];
    let limits = IngressLimits {
        max_nodes: 1,
        max_application_args: 0,
        max_context_depth: context.len(),
        ..IngressLimits::default()
    };
    for (source, expected) in [
        (c("Nat"), false),
        (c("Bool"), false),
        (c("String"), false),
        (c("True"), true),
        (c("False"), true),
        (c("queryMonomorphicType"), false),
        (c("queryMonomorphicProposition"), true),
    ] {
        let mut preparation = Preparation::new(&engine.environment, limits);
        assert_eq!(
            preparation.proposition_type(&source, &context).unwrap(),
            expected
        );
        assert_eq!(preparation.visited, 1);
        assert!(preparation.proposition_queries.entries.is_empty());
        // There is no completed row whose presence could bypass the next
        // charged visit; the same immutable declaration remains retryable.
        nodes_error(preparation.proposition_type(&source, &context), 1);
        assert!(preparation.proposition_queries.entries.is_empty());
        preparation.visited = 0;
        assert_eq!(
            preparation
                .proposition_type(&source, &other_context)
                .unwrap(),
            expected
        );
        assert_eq!(preparation.visited, 1);
        preparation.visited = 0;
        preparation.limits.max_nodes = 0;
        nodes_error(preparation.proposition_type(&source, &context), 0);
        assert!(preparation.proposition_queries.entries.is_empty());

        preparation.visited = 0;
        preparation.limits = limits;
        preparation.limits.max_context_depth = context.len() - 1;
        assert_eq!(
            preparation.proposition_type(&source, &context),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: context.len() - 1,
                observed: context.len(),
            })
        );
        assert_eq!(preparation.visited, 0);
        assert!(preparation.proposition_queries.entries.is_empty());
    }
    assert_eq!(context, vec![c("Nat"); 256]);
    assert_eq!(other_context, vec![c("String"); 256]);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn admitted_sort_shortcut_does_not_reinterpret_values_unknown_names_or_universe_arities() {
    let engine = engine();
    for source in [
        c("Nat.zero"),
        c("Bool.true"),
        c("True.intro"),
        c("Nat.add"),
        c("queryFamily"),
        c("unknownQueryType"),
        c("PUnit"),
        Expr::const_(name("True"), vec![Level::zero()]),
        Expr::const_(name("PUnit"), vec![Level::zero(), Level::one()]),
    ] {
        let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
        assert!(!preparation.proposition_type(&source, &[]).unwrap());
        assert!(preparation.visited > 1, "{source:?}");
        assert!(preparation.proposition_queries.entries.is_empty());
    }

    // The very same polymorphic family inhabits Prop or Type after its
    // actual universe substitution. Its raw Sort parameter is not a verdict.
    let family = engine
        .environment
        .find(&name("PUnit"))
        .unwrap()
        .constant_val();
    assert_eq!(family.level_params.len(), 1);
    assert!(matches!(family.type_.node(), ExprNode::Sort { .. }));
    for (level, expected) in [(Level::zero(), true), (Level::one(), false)] {
        let source = Expr::const_(name("PUnit"), vec![level]);
        let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
        assert_eq!(
            preparation.proposition_type(&source, &[]).unwrap(),
            expected
        );
        assert!(preparation.visited > 1);
        assert_eq!(
            preparation.proposition_queries.entries[&(source, 0)].proposition,
            expected
        );
    }

    // Metadata and a nonliteral declared type keep the ordinary inference
    // path, including their completed memo rows and reduction refusals.
    for source in [metadata(c("True")), c("queryPredicate")] {
        let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
        assert!(preparation.proposition_type(&source, &[]).unwrap());
        assert!(preparation.visited > 1);
        assert!(preparation.proposition_queries.entries[&(source, 0)].proposition);
    }
}

#[test]
fn admitted_sort_statements_remain_independent_of_private_registry_growth_and_rollback() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let initial = Generation::current(&preparation);
    preparation
        .specialize_call(&c("queryFamily"), &[c("Nat")])
        .unwrap()
        .unwrap();
    assert!(Generation::current(&preparation).definitions > initial.definitions);
    let holder = Expr::app(c("QueryHolder"), c("Nat"));
    assert!(preparation.record_shape(&holder).unwrap().is_some());
    assert!(Generation::current(&preparation).shapes > initial.shapes);
    assert_eq!(preparation.value_type(&c("QueryBad")).unwrap(), None);
    let rows = preparation.proposition_queries.entries.len();
    for (source, expected) in [(c("Nat"), false), (c("True"), true)] {
        let start = preparation.visited;
        assert_eq!(
            preparation.proposition_type(&source, &[]).unwrap(),
            expected
        );
        assert_eq!(preparation.visited, start + 1);
        assert_eq!(preparation.proposition_queries.entries.len(), rows);
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
