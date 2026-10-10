use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn app(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn pi(label: &str, domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(name(label), domain, body, BinderInfo::Default)
}

fn lam(label: &str, domain: Expr, body: Expr) -> Expr {
    Expr::lam(name(label), domain, body, BinderInfo::Default)
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
def receiverIdentity (A : Type) (x : A) : A := x
def receiverFunctionType (_ : Nat) : Type := Nat -> Nat
def receiverAliasedFunction : receiverFunctionType 0 := fun n => n
structure ReceiverBox (A : Type) where
  value : A
structure ReceiverPayload where
  flag : Bool
  value : if flag then Nat else String
inductive ReceiverBad where
  | mk (callback : Nat -> ReceiverBad) (payload : ReceiverPayload)
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
fn completed_inference_reuses_exact_syntax_without_copying_unread_contexts() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let context = vec![c("Nat"); 256];
    let limits = IngressLimits {
        max_nodes: 128,
        max_context_depth: 512,
        ..IngressLimits::default()
    };
    let make_source = || Expr::app(c("Nat.succ"), nat::literal(42));
    let source = make_source();
    let original = source.clone();
    let mut preparation = Preparation::new(&engine.environment, limits);
    assert_eq!(
        preparation
            .projection_receiver_type(&source, &context)
            .unwrap(),
        Some(c("Nat"))
    );
    let cold = preparation.visited;
    assert!(cold > 1 && cold < context.len());
    assert!(
        preparation.specializations.receiver_queries.entries[&(source.clone(), context.len())]
            .dependency
            .is_none()
    );

    // Independently allocated equal syntax receives the identical completed
    // answer even when every unrelated caller domain has changed.
    let other_context = vec![c("String"); context.len()];
    for repeated in [source.clone(), make_source()] {
        let start = preparation.visited;
        assert_eq!(
            preparation
                .projection_receiver_type(&repeated, &other_context)
                .unwrap(),
            Some(c("Nat"))
        );
        assert_eq!(preparation.visited, start + 1);
    }
    assert_eq!(source, original);
    assert_eq!(context, vec![c("Nat"); 256]);
    assert!(preparation.lambdas.is_empty());
    assert!(preparation.constructors.is_empty());
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn open_inference_rechecks_only_the_actual_external_domain() {
    let engine = engine();
    let source = Expr::app(b(0), nat::literal(42));
    let nat_function = pi("n", c("Nat"), c("Nat"));
    let string_function = pi("n", c("Nat"), c("String"));
    let mut context = vec![c("Nat"); 255];
    context.push(nat_function.clone());
    let original = context.clone();
    let mut preparation = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: 128,
            max_context_depth: 512,
            ..IngressLimits::default()
        },
    );
    assert_eq!(
        preparation
            .projection_receiver_type(&source, &context)
            .unwrap(),
        Some(c("Nat"))
    );
    let entry =
        &preparation.specializations.receiver_queries.entries[&(source.clone(), context.len())];
    let dependency = entry.dependency.as_ref().unwrap();
    assert_eq!(dependency.index, 0);
    assert_eq!(dependency.domain, nat_function);
    assert!(preparation.visited < context.len());

    let mut other = vec![c("String"); 255];
    other.push(nat_function);
    let start = preparation.visited;
    assert_eq!(
        preparation
            .projection_receiver_type(&source, &other)
            .unwrap(),
        Some(c("Nat"))
    );
    assert_eq!(preparation.visited, start + 2);
    *other.last_mut().unwrap() = string_function.clone();
    let start = preparation.visited;
    assert_eq!(
        preparation
            .projection_receiver_type(&source, &other)
            .unwrap(),
        Some(c("String"))
    );
    assert!(preparation.visited > start + 2);
    assert_eq!(
        preparation.specializations.receiver_queries.entries[&(source.clone(), context.len())]
            .dependency
            .as_ref()
            .unwrap()
            .domain,
        string_function
    );
    assert_eq!(context, original);
    assert_eq!(
        preparation
            .projection_receiver_type(&source, &context)
            .unwrap(),
        Some(c("Nat"))
    );
}

#[test]
fn nested_binders_and_split_prefixes_preserve_exact_dependent_indices() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    // A : Type, f : Nat -> A. The function domain is relative to the
    // telescope before f, so A is #1 underneath its own Nat Pi binder.
    let prefix = [Expr::sort(Level::one())];
    let suffix = [pi("n", c("Nat"), b(1))];
    let source = lam("n", c("Nat"), Expr::app(b(1), b(0)));
    let expected = pi("n", c("Nat"), b(2));
    assert_eq!(
        preparation
            .projection_receiver_type_in(&source, &prefix, &suffix, 0)
            .unwrap(),
        Some(expected.clone())
    );
    let dependency = preparation.specializations.receiver_queries.entries[&(source.clone(), 2)]
        .dependency
        .as_ref()
        .unwrap();
    assert_eq!(dependency.index, 0);
    assert_eq!(dependency.domain, suffix[0]);
    let joined = [prefix[0].clone(), suffix[0].clone()];
    let start = preparation.visited;
    assert_eq!(
        preparation
            .projection_receiver_type(&source, &joined)
            .unwrap(),
        Some(expected)
    );
    assert_eq!(preparation.visited, start + 2);

    let through_let = Expr::let_e(
        name("n"),
        c("Nat"),
        nat::literal(42),
        Expr::app(b(1), b(0)),
        false,
    );
    for result in [c("Nat"), c("String"), c("Nat")] {
        let context = [pi("n", c("Nat"), result.clone())];
        assert_eq!(
            preparation
                .projection_receiver_type(&through_let, &context)
                .unwrap(),
            Some(result)
        );
    }

    // An internal type-valued let shadows the outer context. Its result
    // substitution must still expose Nat in both domains of the identity.
    let local = Expr::let_e(
        name("A"),
        Expr::sort(Level::one()),
        c("Nat"),
        lam("x", b(0), b(0)),
        false,
    );
    let result = pi("x", c("Nat"), c("Nat"));
    assert_eq!(
        preparation
            .projection_receiver_type(&local, &joined)
            .unwrap(),
        Some(result.clone())
    );
    assert!(
        preparation.specializations.receiver_queries.entries[&(local.clone(), 2)]
            .dependency
            .is_none()
    );
    let start = preparation.visited;
    assert_eq!(
        preparation
            .projection_receiver_type_in(&local, &[], &[], 2)
            .unwrap(),
        Some(result)
    );
    assert_eq!(preparation.visited, start + 1);
}

#[test]
fn equal_total_depth_does_not_authorize_a_missing_or_changed_borrowed_slot() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let source = Expr::app(b(1), nat::literal(42));
    let function = pi("n", c("Nat"), c("Nat"));
    let prefix = [function.clone()];
    let suffix = [c("String")];
    assert_eq!(
        preparation
            .projection_receiver_type_in(&source, &prefix, &suffix, 0)
            .unwrap(),
        Some(c("Nat"))
    );
    assert_eq!(
        preparation.specializations.receiver_queries.entries[&(source.clone(), 2)]
            .dependency
            .as_ref()
            .unwrap()
            .index,
        1
    );
    // Both calls have lexical depth two. The first now omits the actual
    // queried outer slot; the second has a live slot with a different type.
    assert_eq!(
        preparation
            .projection_receiver_type_in(&source, &[], &suffix, 1)
            .unwrap(),
        None
    );
    assert_eq!(
        preparation
            .projection_receiver_type_in(&source, &suffix, &[function], 0)
            .unwrap(),
        None
    );
    assert_eq!(
        preparation
            .projection_receiver_type_in(&source, &prefix, &suffix, 0)
            .unwrap(),
        Some(c("Nat"))
    );
}

#[test]
fn unknowns_and_private_projection_failures_never_publish_authority() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let future = Expr::const_(Name::num(name("_fln_runtime_specialization"), 0), vec![]);
    let applied = Expr::app(future.clone(), nat::literal(7));
    assert_eq!(
        preparation.projection_receiver_type(&applied, &[]).unwrap(),
        None
    );
    assert!(
        preparation
            .specializations
            .receiver_queries
            .entries
            .is_empty()
    );
    assert_eq!(
        preparation
            .specialize_call(&c("receiverIdentity"), &[c("Nat")])
            .unwrap()
            .unwrap(),
        future
    );
    assert_eq!(
        preparation.projection_receiver_type(&applied, &[]).unwrap(),
        Some(c("Nat"))
    );

    let holder = Expr::app(c("ReceiverBox"), c("Nat"));
    let value = app(c("ReceiverBox.mk"), [c("Nat"), nat::literal(42)]);
    let private = Name::num(
        name("_fln_runtime_data"),
        u64::try_from(preparation.data_shapes.len()).unwrap(),
    );
    let projection = Expr::proj(private.clone(), 0, value);
    let rows = preparation.specializations.receiver_queries.entries.len();
    assert_eq!(
        preparation.projection_receiver_type(&projection, &[]),
        Err(unsupported("projection receiver family mismatch"))
    );
    assert_eq!(
        preparation.specializations.receiver_queries.entries.len(),
        rows
    );
    assert_eq!(
        preparation.record_shape(&holder).unwrap().unwrap().name,
        private
    );
    assert_eq!(
        preparation
            .projection_receiver_type(&projection, &[])
            .unwrap(),
        Some(c("Nat"))
    );
    let start = preparation.visited;
    assert_eq!(
        preparation
            .projection_receiver_type(&projection, &[])
            .unwrap(),
        Some(c("Nat"))
    );
    assert_eq!(preparation.visited, start + 1);
}

#[test]
fn completed_queries_recheck_generations_and_survive_description_only_rollback() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let source = Expr::app(c("Nat.succ"), nat::literal(42));
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(
        preparation.projection_receiver_type(&source, &[]).unwrap(),
        Some(c("Nat"))
    );
    let initial = Generation::current(&preparation);
    preparation
        .specialize_call(&c("receiverIdentity"), &[c("Nat")])
        .unwrap()
        .unwrap();
    assert!(Generation::current(&preparation).definitions > initial.definitions);
    let start = preparation.visited;
    assert_eq!(
        preparation.projection_receiver_type(&source, &[]).unwrap(),
        Some(c("Nat"))
    );
    assert!(preparation.visited > start + 1);

    let initial = Generation::current(&preparation);
    preparation
        .record_shape(&Expr::app(c("ReceiverBox"), c("Nat")))
        .unwrap()
        .unwrap();
    assert!(Generation::current(&preparation).shapes > initial.shapes);
    let start = preparation.visited;
    assert_eq!(
        preparation.projection_receiver_type(&source, &[]).unwrap(),
        Some(c("Nat"))
    );
    assert!(preparation.visited > start + 1);

    let initial = Generation::current(&preparation);
    preparation.value_types.native.insert(
        c("_receiver_cache_native_generation"),
        (
            ValueType::Nat,
            fln_comp::flbc::CallableResultOwnership::Scalar,
        ),
    );
    assert!(Generation::current(&preparation).native > initial.native);
    let start = preparation.visited;
    assert_eq!(
        preparation.projection_receiver_type(&source, &[]).unwrap(),
        Some(c("Nat"))
    );
    assert!(preparation.visited > start + 1);

    let interfaces = preparation.interfaces.len();
    let constructors = preparation.constructors.len();
    assert_eq!(preparation.value_type(&c("ReceiverBad")).unwrap(), None);
    assert_eq!(preparation.interfaces.len(), interfaces);
    assert_eq!(preparation.constructors.len(), constructors);
    assert!(!preparation.value_types.records.contains(&c("ReceiverBad")));
    assert_eq!(
        preparation.projection_receiver_type(&source, &[]).unwrap(),
        Some(c("Nat"))
    );
    let start = preparation.visited;
    assert_eq!(
        preparation.projection_receiver_type(&source, &[]).unwrap(),
        Some(c("Nat"))
    );
    assert_eq!(preparation.visited, start + 1);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn cached_queries_keep_incoming_and_nested_depth_and_argument_limits() {
    let engine = engine();
    let mut preparation = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_context_depth: 3,
            ..IngressLimits::default()
        },
    );
    let source = lam("n", c("Nat"), b(0));
    assert_eq!(
        preparation
            .projection_receiver_type(&source, &[c("String")])
            .unwrap(),
        Some(pi("n", c("Nat"), c("Nat")))
    );
    preparation.limits.max_context_depth = 1;
    assert_eq!(
        preparation.projection_receiver_type(&source, &[c("String")]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 1,
            observed: 2
        })
    );
    let before = preparation.visited;
    assert_eq!(
        preparation.projection_receiver_type(&source, &[c("String"), c("Nat")]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 1,
            observed: 2
        })
    );
    assert_eq!(preparation.visited, before);
    preparation.limits.max_context_depth = 3;
    assert_eq!(
        preparation.projection_receiver_type_in(&source, &[], &[], 3),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 3,
            observed: 4
        })
    );

    let aliased = Expr::app(c("receiverAliasedFunction"), nat::literal(42));
    assert_eq!(
        preparation.projection_receiver_type(&aliased, &[]).unwrap(),
        Some(c("Nat"))
    );
    preparation.limits.max_application_args = 0;
    assert_eq!(
        preparation.projection_receiver_type(&aliased, &[]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ApplicationArguments,
            limit: 0,
            observed: 1
        })
    );
    preparation.limits.max_application_args = IngressLimits::default().max_application_args;
    assert_eq!(
        preparation.projection_receiver_type(&aliased, &[]).unwrap(),
        Some(c("Nat"))
    );
}

#[test]
fn cache_insertion_hits_and_capacity_remain_bounded_and_retryable() {
    let engine = engine();
    let source = Expr::app(c("Nat.succ"), nat::literal(42));
    let mut baseline = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(
        baseline.projection_receiver_type(&source, &[]).unwrap(),
        Some(c("Nat"))
    );
    let needed = baseline.visited;
    let mut preparation = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: needed - 1,
            ..IngressLimits::default()
        },
    );
    nodes_error(
        preparation.projection_receiver_type(&source, &[]),
        needed - 1,
    );
    assert!(
        preparation
            .specializations
            .receiver_queries
            .entries
            .is_empty()
    );
    preparation.limits.max_nodes = IngressLimits::default().max_nodes;
    assert_eq!(
        preparation.projection_receiver_type(&source, &[]).unwrap(),
        Some(c("Nat"))
    );
    let start = preparation.visited;
    preparation.limits.max_nodes = start + 1;
    assert_eq!(
        preparation.projection_receiver_type(&source, &[]).unwrap(),
        Some(c("Nat"))
    );
    assert_eq!(preparation.visited, start + 1);
    nodes_error(
        preparation.projection_receiver_type(&source, &[]),
        start + 1,
    );

    let generation = Generation::current(&baseline);
    let limits = Limits::from(IngressLimits::default());
    let mut store = Store::default();
    for value in [0, 1] {
        let result = store.remember(
            (Expr::app(c("Nat.succ"), nat::literal(value)), 0),
            Entry {
                generation,
                limits,
                dependency: None,
                type_: c("Nat"),
            },
            1,
        );
        if value == 0 {
            result.unwrap();
        } else {
            assert_eq!(
                result,
                Err(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes,
                    limit: 1,
                    observed: 2
                })
            );
        }
    }
    assert_eq!(store.entries.len(), 1);

    let mut empty = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        },
    );
    nodes_error(empty.projection_receiver_type(&source, &[]), 0);
    assert!(empty.specializations.receiver_queries.entries.is_empty());
}

#[test]
fn terminal_types_and_universe_mismatches_keep_the_original_inference_path() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    for source in [
        c("Nat"),
        c("Nat.zero"),
        c("Nat.succ"),
        b(0),
        nat::literal(42),
    ] {
        assert!(
            preparation
                .projection_receiver_type(&source, &[c("Nat")])
                .unwrap()
                .is_some()
        );
    }
    assert!(
        preparation
            .specializations
            .receiver_queries
            .entries
            .is_empty()
    );
    for source in [
        Expr::const_(name("Nat.succ"), vec![Level::zero()]),
        c("PUnit"),
        Expr::const_(name("PUnit"), vec![Level::zero(), Level::one()]),
        c("unknownReceiverConstant"),
    ] {
        let wrapped = Expr::mdata(KVMap::new(), source);
        assert_eq!(
            preparation.projection_receiver_type(&wrapped, &[]).unwrap(),
            None
        );
    }
    assert!(
        preparation
            .specializations
            .receiver_queries
            .entries
            .is_empty()
    );
    for level in [Level::zero(), Level::one()] {
        let source = Expr::mdata(
            KVMap::new(),
            Expr::const_(name("PUnit"), vec![level.clone()]),
        );
        assert_eq!(
            preparation.projection_receiver_type(&source, &[]).unwrap(),
            Some(Expr::sort(level))
        );
    }
    assert_eq!(
        preparation.specializations.receiver_queries.entries.len(),
        2
    );
}
