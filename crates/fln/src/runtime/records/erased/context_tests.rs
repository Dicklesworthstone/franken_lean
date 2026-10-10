use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn pi(label: &str, domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(name(label), domain, body, BinderInfo::Default)
}

fn lam(label: &str, domain: Expr, body: Expr) -> Expr {
    Expr::lam(name(label), domain, body, BinderInfo::Default)
}

fn carrier(receiver: Expr) -> Expr {
    Expr::proj(name("BorrowedPackage"), 0, receiver)
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
structure BorrowedPackage (A : Type) where
  carrier : Type
  value : carrier
  marker : A
structure BorrowedOuter where
  package : BorrowedPackage Nat
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

fn table_error<T>(result: Result<T, IngressError>, limit: usize) {
    assert_eq!(
        result.err(),
        Some(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit,
            observed: limit + 1,
        })
    );
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
fn unrelated_caller_slots_need_no_copy_for_hidden_type_erasure() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let context = vec![c("Nat"); 256];
    let original = context.clone();
    let limits = IngressLimits {
        max_nodes: 96,
        max_context_depth: 512,
        ..IngressLimits::default()
    };
    for source in [
        c("Nat"),
        pi("n", c("Nat"), c("String")),
        lam("A", Expr::sort(Level::one()), pi("x", b(0), b(1))),
    ] {
        let mut empty = Preparation::new(&engine.environment, limits);
        let mut nested = Preparation::new(&engine.environment, limits);
        assert_eq!(empty.erase_hidden_types(&source, &[]).unwrap(), source);
        assert_eq!(
            nested.erase_hidden_types(&source, &context).unwrap(),
            source
        );
        assert_eq!(nested.visited, empty.visited);
    }
    assert_eq!(context, original);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn dependent_local_suffixes_and_nested_receivers_keep_the_original_caller_scope() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let package = Expr::app(c("BorrowedPackage"), c("Nat"));
    let context = [c("Bool"), package.clone(), c("Nat")];
    let original = context.clone();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());

    // A is local to the query, x depends on A, and the package remains in the
    // caller. Every introduced lambda/Pi shifts that same caller receiver.
    let source = pi(
        "A",
        Expr::sort(Level::one()),
        pi("x", b(0), lam("ignored", c("String"), carrier(b(4)))),
    );
    let expected = pi(
        "A",
        Expr::sort(Level::one()),
        pi("x", b(0), lam("ignored", c("String"), boxed_slot_type())),
    );
    assert_eq!(
        preparation.erase_hidden_types(&source, &context).unwrap(),
        expected
    );

    // Finishing the inner telescope must restore the outer caller indices.
    let source = pi(
        "callback",
        pi("p", package.clone(), carrier(b(0))),
        carrier(b(2)),
    );
    let expected = pi(
        "callback",
        pi("p", package.clone(), boxed_slot_type()),
        boxed_slot_type(),
    );
    assert_eq!(
        preparation.erase_hidden_types(&source, &context).unwrap(),
        expected
    );

    let source = pi(
        "n",
        c("Nat"),
        carrier(Expr::proj(name("BorrowedOuter"), 0, b(2))),
    );
    assert_eq!(
        preparation
            .erase_hidden_types(&source, &[c("BorrowedOuter"), c("Nat")])
            .unwrap(),
        pi("n", c("Nat"), boxed_slot_type())
    );

    // A private projection still needs the exact, previously discovered
    // source family. Borrowing changes neither this authority nor data fields.
    let shape = preparation.record_shape(&package).unwrap().unwrap();
    assert_ne!(shape.name, name("BorrowedPackage"));
    assert_eq!(
        preparation
            .erase_hidden_types(&Expr::proj(shape.name, 0, b(1)), &context)
            .unwrap(),
        boxed_slot_type()
    );
    let marker = Expr::proj(name("BorrowedPackage"), 2, b(1));
    assert_eq!(
        preparation.erase_hidden_types(&marker, &context).unwrap(),
        marker
    );

    // An unresolved generic carrier cannot acquire a concrete boxed layout
    // merely because the same syntax was seen in a different caller scope.
    let open = [
        Expr::sort(Level::one()),
        Expr::app(c("BorrowedPackage"), b(0)),
    ];
    for caller in [&open[..], &[][..]] {
        let source = carrier(b(0));
        assert_eq!(
            preparation.erase_hidden_types(&source, caller).unwrap(),
            source
        );
    }
    assert_eq!(context, original);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn borrowed_and_introduced_depths_keep_the_table_refusal_and_retry_boundary() {
    let engine = engine();
    let context = vec![c("Nat"); 4];
    let limits = IngressLimits {
        max_context_depth: 4,
        ..IngressLimits::default()
    };
    let mut preparation = Preparation::new(&engine.environment, limits);
    assert_eq!(
        preparation.erase_hidden_types(&c("Nat"), &context).unwrap(),
        c("Nat")
    );
    let too_many = vec![c("Nat"); 5];
    table_error(preparation.erase_hidden_types(&c("Nat"), &too_many), 4);
    let one = pi("n", c("Nat"), c("Nat"));
    table_error(preparation.erase_hidden_types(&one, &context), 4);
    let two = pi("n", c("Nat"), lam("A", Expr::sort(Level::one()), b(0)));
    table_error(preparation.erase_hidden_types(&two, &context[..3]), 4);

    let mut retry = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_context_depth: 6,
            ..limits
        },
    );
    assert_eq!(retry.erase_hidden_types(&two, &context).unwrap(), two);
    assert_eq!(context, vec![c("Nat"); 4]);
}

#[test]
fn borrowed_context_work_is_still_metered_and_failed_erasure_can_retry() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let context = vec![c("Nat"); 256];
    let source = pi("n", c("Nat"), c("String"));
    let limits = IngressLimits {
        max_context_depth: 512,
        ..IngressLimits::default()
    };
    let mut measured = Preparation::new(&engine.environment, limits);
    assert_eq!(
        measured.erase_hidden_types(&source, &context).unwrap(),
        source
    );
    let required = measured.visited;
    assert!(required > 1 && required < context.len());
    for max_nodes in [0, required - 1] {
        let mut stopped = Preparation::new(
            &engine.environment,
            IngressLimits {
                max_nodes,
                ..limits
            },
        );
        nodes_error(stopped.erase_hidden_types(&source, &context), max_nodes);
    }
    let mut retry = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: required,
            ..limits
        },
    );
    assert_eq!(retry.erase_hidden_types(&source, &context).unwrap(), source);
    assert_eq!(retry.visited, required);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
