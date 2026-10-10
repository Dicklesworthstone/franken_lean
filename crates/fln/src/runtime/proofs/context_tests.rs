use super::*;

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap()
}

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

fn equality(value: Expr) -> Expr {
    [c("Nat"), value.clone(), value]
        .into_iter()
        .fold(Expr::const_(name("Eq"), vec![Level::one()]), Expr::app)
}

fn depth_error<T>(result: Result<T, IngressError>, limit: usize, observed: usize) {
    assert_eq!(
        result.err(),
        Some(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit,
            observed,
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
fn closed_queries_fit_a_budget_that_excludes_copying_unused_outer_locals() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let context = vec![c("Nat"); 256];
    let limits = IngressLimits {
        max_nodes: 128,
        max_context_depth: 512,
        ..IngressLimits::default()
    };
    for source in [
        nat::literal(42),
        Expr::app(c("Nat.succ"), nat::literal(42)),
        Expr::let_e(name("n"), c("Nat"), nat::literal(42), b(0), false),
    ] {
        assert!(specialize::closed(&source));
        let mut empty = Preparation::new(&engine.environment, limits);
        let mut nested = Preparation::new(&engine.environment, limits);
        assert_eq!(
            empty.projection_receiver_type(&source, &[]).unwrap(),
            Some(c("Nat"))
        );
        assert_eq!(
            nested.projection_receiver_type(&source, &context).unwrap(),
            Some(c("Nat"))
        );
        assert_eq!(nested.visited, empty.visited);
    }
    for (source, expected) in [
        (c("Nat"), false),
        (Expr::sort(Level::zero()), false),
        (equality(nat::literal(42)), true),
        (pi("n", c("Nat"), equality(b(0))), true),
    ] {
        assert!(specialize::closed(&source));
        let mut empty = Preparation::new(&engine.environment, limits);
        let mut nested = Preparation::new(&engine.environment, limits);
        assert_eq!(empty.proposition_type(&source, &[]).unwrap(), expected);
        assert_eq!(
            nested.proposition_type(&source, &context).unwrap(),
            expected
        );
        assert_eq!(nested.visited, empty.visited);
    }
    // A free de Bruijn variable still reads the actual original telescope.
    // The read borrows its prefix, so even an open query needs no copy of
    // these 256 slots. Exhausted work remains a refusal in the controls below.
    let mut open = Preparation::new(&engine.environment, limits);
    assert_eq!(
        open.projection_receiver_type(&b(0), &context).unwrap(),
        Some(c("Nat"))
    );
    let mut open = Preparation::new(&engine.environment, limits);
    assert!(!open.proposition_type(&b(0), &context).unwrap());
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn omitted_outer_locals_preserve_internal_and_captured_dependent_telescope_types() {
    let engine = engine();
    let context = [c("String"), Expr::sort(Level::zero()), c("Nat")];
    let identity = lam("A", Expr::sort(Level::one()), lam("x", b(0), b(0)));
    let identity_type = pi("A", Expr::sort(Level::one()), pi("x", b(0), b(1)));
    let selected = Expr::let_e(
        name("A"),
        Expr::sort(Level::one()),
        c("Nat"),
        lam("x", b(0), b(0)),
        false,
    );
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(
        prep.projection_receiver_type(&identity, &context).unwrap(),
        Some(identity_type)
    );
    assert_eq!(
        prep.projection_receiver_type(&selected, &context).unwrap(),
        Some(pi("x", c("Nat"), c("Nat")))
    );

    for (sort, proof) in [(Level::zero(), true), (Level::one(), false)] {
        // Both binders are internal to this closed telescope.
        let closed = pi("A", Expr::sort(sort.clone()), pi("x", b(0), b(1)));
        assert!(specialize::closed(&closed));
        assert_eq!(prep.proposition_type(&closed, &context).unwrap(), proof);
        // Here A belongs to the caller. Identical relative syntax must use
        // its actual local sort, including after the preceding closed query.
        let captured = pi("x", b(0), b(1));
        assert!(!specialize::closed(&captured));
        assert_eq!(
            prep.proposition_type(&captured, &[Expr::sort(sort.clone())])
                .unwrap(),
            proof
        );
        let predicate_context = [pi("n", c("Nat"), Expr::sort(sort.clone())), c("Nat")];
        let applied = Expr::app(b(1), b(0));
        assert_eq!(
            prep.projection_receiver_type(&applied, &predicate_context)
                .unwrap(),
            Some(Expr::sort(sort))
        );
        assert_eq!(
            prep.proposition_type(&applied, &predicate_context).unwrap(),
            proof
        );
    }
    assert_eq!(prep.projection_receiver_type(&b(0), &[]).unwrap(), None);
    assert!(!prep.proposition_type(&b(0), &[]).unwrap());
}

#[test]
fn omitted_context_depth_still_bounds_incoming_and_introduced_binders() {
    let engine = engine();
    let context = vec![c("Nat"); 4];
    let limits = IngressLimits {
        max_context_depth: 4,
        ..IngressLimits::default()
    };
    let mut prep = Preparation::new(&engine.environment, limits);
    assert_eq!(
        prep.projection_receiver_type(&nat::literal(42), &context)
            .unwrap(),
        Some(c("Nat"))
    );
    assert!(!prep.proposition_type(&c("Nat"), &context).unwrap());
    for source in [
        lam("n", c("Nat"), b(0)),
        Expr::let_e(name("n"), c("Nat"), nat::literal(42), b(0), false),
    ] {
        depth_error(prep.projection_receiver_type(&source, &context), 4, 5);
    }
    depth_error(
        prep.proposition_type(&pi("P", Expr::sort(Level::zero()), b(0)), &context),
        4,
        5,
    );
    let too_many = vec![c("Nat"); 5];
    for source in [c("Nat"), b(0)] {
        depth_error(prep.proposition_type(&source, &too_many), 4, 5);
        depth_error(prep.projection_receiver_type(&source, &too_many), 4, 5);
    }

    // The classifier introduces n, then delegates the let to type recovery.
    // Even a now-closed suffix retains BOTH omitted context depths. Neither
    // a captured n nor a discarded n permits one extra binder past the bound.
    for value in [b(0), nat::literal(42)] {
        let source = pi(
            "n",
            c("Nat"),
            Expr::let_e(
                name("Q"),
                Expr::sort(Level::zero()),
                equality(value),
                b(0),
                false,
            ),
        );
        assert!(specialize::closed(&source));
        let mut stopped = Preparation::new(
            &engine.environment,
            IngressLimits {
                max_context_depth: 5,
                ..limits
            },
        );
        depth_error(stopped.proposition_type(&source, &context), 5, 6);
        let mut retry = Preparation::new(
            &engine.environment,
            IngressLimits {
                max_context_depth: 6,
                ..limits
            },
        );
        assert!(retry.proposition_type(&source, &context).unwrap());
    }
}

#[test]
fn closed_query_work_remains_metered_and_failed_queries_can_retry() {
    let engine = engine();
    let context = vec![c("Nat"); 256];
    let limits = IngressLimits {
        max_context_depth: 512,
        ..IngressLimits::default()
    };
    let proposition = pi("n", c("Nat"), equality(b(0)));
    let mut measured = Preparation::new(&engine.environment, limits);
    assert!(measured.proposition_type(&proposition, &context).unwrap());
    let required = measured.visited;
    assert!(required > 1);
    for max_nodes in [0, required - 1] {
        let mut stopped = Preparation::new(
            &engine.environment,
            IngressLimits {
                max_nodes,
                ..limits
            },
        );
        nodes_error(stopped.proposition_type(&proposition, &context), max_nodes);
    }
    let mut retry = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: required,
            ..limits
        },
    );
    assert!(retry.proposition_type(&proposition, &context).unwrap());
    assert_eq!(retry.visited, required);

    let identity = lam("n", c("Nat"), b(0));
    let expected = pi("n", c("Nat"), c("Nat"));
    let mut measured = Preparation::new(&engine.environment, limits);
    assert_eq!(
        measured
            .projection_receiver_type(&identity, &context)
            .unwrap(),
        Some(expected.clone())
    );
    let required = measured.visited;
    assert!(required > 1);
    for max_nodes in [0, required - 1] {
        let mut stopped = Preparation::new(
            &engine.environment,
            IngressLimits {
                max_nodes,
                ..limits
            },
        );
        nodes_error(
            stopped.projection_receiver_type(&identity, &context),
            max_nodes,
        );
    }
    let mut retry = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: required,
            ..limits
        },
    );
    assert_eq!(
        retry.projection_receiver_type(&identity, &context).unwrap(),
        Some(expected)
    );
    assert_eq!(retry.visited, required);
}

#[test]
fn open_dependent_queries_borrow_large_telescope_prefixes_within_the_work_bound() {
    let engine = engine();
    let limits = IngressLimits {
        max_nodes: 128,
        max_context_depth: 258,
        ..IngressLimits::default()
    };
    for (sort, proposition) in [(Level::zero(), true), (Level::one(), false)] {
        // A : Sort u, followed by 254 independent Nat values, then x : A.
        // The last domain still refers all the way through the borrowed
        // prefix. Copying that prefix alone exhausted this same node bound.
        let mut context = vec![Expr::sort(sort.clone())];
        context.extend((0..254).map(|_| c("Nat")));
        context.push(b(254));
        let original = context.clone();
        let mut prep = Preparation::new(&engine.environment, limits);
        assert_eq!(
            prep.projection_receiver_type(&b(0), &context).unwrap(),
            Some(b(255))
        );
        assert_eq!(
            prep.projection_receiver_type(&b(255), &context).unwrap(),
            Some(Expr::sort(sort))
        );
        assert_eq!(
            prep.proposition_type(&b(255), &context).unwrap(),
            proposition
        );
        let identity = lam("x", b(255), b(0));
        assert_eq!(
            prep.projection_receiver_type(&identity, &context).unwrap(),
            Some(pi("x", b(255), b(256)))
        );
        assert_eq!(context, original);
    }
}

#[test]
fn borrowed_prefix_and_local_suffix_keep_dependent_shadowed_binders_distinct() {
    let engine = engine();
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    // A : Type, x : A. Every selected runtime value has type A even when
    // lambda and let binders share the same spelling. The domain of A still
    // belongs to the borrowed caller, while y/z/w belong to this query.
    let context = [Expr::sort(Level::one()), b(0)];
    for selected in 0..4 {
        let source = lam(
            "shadow",
            b(1),
            Expr::let_e(
                name("shadow"),
                b(2),
                b(1),
                lam("shadow", b(3), b(selected)),
                false,
            ),
        );
        assert_eq!(
            prep.projection_receiver_type(&source, &context).unwrap(),
            Some(pi("shadow", b(1), pi("shadow", b(2), b(3))))
        );
    }

    // The proposition classifier borrows A/x and opens p : A -> Prop.
    // Type recovery then opens the inner let. Its BVar lookup selects p from
    // the middle slice, whose domain still refers to the borrowed outer A.
    let predicate = pi("value", b(1), Expr::sort(Level::zero()));
    let body = Expr::let_e(
        name("shadow"),
        c("Nat"),
        nat::literal(0),
        Expr::app(b(1), b(2)),
        false,
    );
    let source = pi("shadow", predicate.clone(), body.clone());
    assert!(prep.proposition_type(&source, &context).unwrap());
    assert!(
        prep.proposition_type(
            &pi("shadow", predicate, Expr::mdata(KVMap::new(), body)),
            &context,
        )
        .unwrap()
    );

    // Identical open syntax must consult the current caller's actual sort.
    // Both the Pi suffix and the nested let are newer than that caller.
    let source = pi(
        "shadow",
        b(0),
        Expr::let_e(
            name("shadow"),
            Expr::sort(Level::one()),
            c("Nat"),
            b(2),
            false,
        ),
    );
    for (sort, proposition) in [(Level::zero(), true), (Level::one(), false)] {
        assert_eq!(
            prep.proposition_type(&source, &[Expr::sort(sort)]).unwrap(),
            proposition
        );
    }
    assert_eq!(
        prep.projection_receiver_type(&b(2), &context).unwrap(),
        None
    );
}

#[test]
fn failed_borrowed_queries_preserve_caller_context_and_retry_with_exact_depth() {
    let engine = engine();
    // P : Prop, n : Nat |- forall h : P, let n : Nat := n; P.
    let context = [Expr::sort(Level::zero()), c("Nat")];
    let original = context.clone();
    let source = pi(
        "h",
        b(1),
        Expr::let_e(name("n"), c("Nat"), b(1), b(3), false),
    );
    let limits = IngressLimits {
        max_context_depth: 4,
        ..IngressLimits::default()
    };
    let mut measured = Preparation::new(&engine.environment, limits);
    assert!(measured.proposition_type(&source, &context).unwrap());
    let required = measured.visited;
    assert!(required > 1);
    for max_nodes in [0, required - 1] {
        let mut prep = Preparation::new(
            &engine.environment,
            IngressLimits {
                max_nodes,
                ..limits
            },
        );
        nodes_error(prep.proposition_type(&source, &context), max_nodes);
        assert_eq!(context, original);
        prep.limits.max_nodes = IngressLimits::default().max_nodes;
        assert!(prep.proposition_type(&source, &context).unwrap());
        assert!(
            !prep
                .proposition_type(&b(1), &[Expr::sort(Level::one()), c("Nat")])
                .unwrap()
        );
        assert_eq!(context, original);
    }
    let mut prep = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_context_depth: 3,
            ..limits
        },
    );
    depth_error(prep.proposition_type(&source, &context), 3, 4);
    assert_eq!(context, original);
    prep.limits.max_context_depth = 4;
    assert!(prep.proposition_type(&source, &context).unwrap());
    assert_eq!(context, original);
}
