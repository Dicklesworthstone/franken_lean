//! Projection layout selection must not expand unaffected shared expression DAGs.
use super::*;

fn environment() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[b"structure PruningBox where\n  value : Nat"],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}
fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}
fn plus(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(c("Nat.add"), a), b)
}
fn shared(mut leaf: Expr, depth: usize) -> Expr {
    for _ in 0..depth {
        leaf = plus(leaf.clone(), leaf);
    }
    leaf
}
#[test]
fn an_unaffected_shared_sibling_does_not_exhaust_projection_lowering() {
    let engine = environment();
    let root = engine.logical_root(&KVMap::new());
    let sibling = shared(nat::literal(1), 20);
    let receiver = Expr::app(c("PruningBox.mk"), nat::literal(42));
    let projected = Expr::proj(name("PruningBox"), 0, receiver);
    let input = plus(sibling.clone(), projected);
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let output = preparation.lower_projections(&input).unwrap();
    let ExprNode::App { f, .. } = output.node() else {
        panic!("outer application");
    };
    let ExprNode::App { a, .. } = f.node() else {
        panic!("first operand");
    };
    assert_eq!(a, &sibling);
    assert_eq!(a.allocation_identity(), sibling.allocation_identity());
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn open_unaffected_subtrees_keep_their_exact_scope_and_strict_bindings() {
    let engine = environment();
    let variable = Expr::bvar(0).unwrap();
    let retained = Expr::let_e(
        name("strict"),
        c("Nat"),
        Expr::app(c("workStillExecutes"), variable.clone()),
        variable,
        false,
    );
    let body = plus(
        retained.clone(),
        Expr::proj(
            name("PruningBox"),
            0,
            Expr::app(c("PruningBox.mk"), nat::literal(42)),
        ),
    );
    let input = Expr::lam(name("x"), c("Nat"), body, BinderInfo::Default);
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let output = preparation.lower_projections(&input).unwrap();
    let ExprNode::Lam { body, .. } = output.node() else {
        panic!("lambda");
    };
    let ExprNode::App { f, .. } = body.node() else {
        panic!("application");
    };
    let ExprNode::App { a, .. } = f.node() else {
        panic!("retained operand");
    };
    assert_eq!(a, &retained);
    assert_eq!(a.allocation_identity(), retained.allocation_identity());
    // The unknown executable initializer is deliberately not evaluated by a
    // representation-only pass. This test does not authorize its compilation.
}

#[test]
fn nested_projections_and_invalid_receivers_are_not_hidden_by_the_summary() {
    let engine = environment();
    let nested = Expr::proj(
        name("PruningBox"),
        0,
        Expr::app(c("PruningBox.mk"), nat::literal(7)),
    );
    let input = Expr::proj(name("PruningBox"), 0, Expr::app(c("PruningBox.mk"), nested));
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let output = preparation.lower_projections(&input).unwrap();
    let ExprNode::Proj {
        struct_name: outer,
        expr,
        ..
    } = output.node()
    else {
        panic!("outer field");
    };
    let ExprNode::App { a, .. } = expr.node() else {
        panic!("constructor");
    };
    let ExprNode::Proj {
        struct_name: inner, ..
    } = a.node()
    else {
        panic!("inner field");
    };
    assert_eq!(outer, inner);
    assert_eq!(outer, &name("PruningBox"));
    for (family, index) in [("Other", 0), ("PruningBox", 1)] {
        let invalid = plus(
            shared(nat::literal(1), 20),
            Expr::proj(
                name(family),
                index,
                Expr::app(c("PruningBox.mk"), nat::literal(42)),
            ),
        );
        assert!(
            Preparation::new(engine.environment(), IngressLimits::default())
                .lower_projections(&invalid)
                .is_err()
        );
    }
}

#[test]
fn summary_and_lowering_budget_stops_do_not_change_fresh_retries() {
    let engine = environment();
    let root = engine.logical_root(&KVMap::new());
    let input = plus(
        shared(nat::literal(1), 12),
        Expr::proj(
            name("PruningBox"),
            0,
            Expr::app(c("PruningBox.mk"), nat::literal(42)),
        ),
    );
    let mut full = Preparation::new(engine.environment(), IngressLimits::default());
    let expected = full.lower_projections(&input).unwrap();
    let required = full.visited;
    assert!(
        required > 1 && required < 10_000,
        "bounded DAG work: {required}"
    );
    for allowed in [0, required / 2, required - 1] {
        let mut limited = Preparation::new(
            engine.environment(),
            IngressLimits {
                max_nodes: allowed,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            limited.lower_projections(&input),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
    let mut retry = Preparation::new(engine.environment(), IngressLimits::default());
    assert_eq!(retry.lower_projections(&input).unwrap(), expected);
    assert_eq!(retry.visited, required);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn closed_projection_dags_share_analysis_without_erasing_any_occurrence() {
    let engine = environment();
    let receiver = Expr::app(c("PruningBox.mk"), nat::literal(42));
    let leaf = Expr::proj(name("PruningBox"), 0, receiver);
    let input = shared(leaf, 20);
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let output = preparation.lower_projections(&input).unwrap();
    let mut current = &output;
    for _ in 0..20 {
        let ExprNode::App { f, a: right } = current.node() else {
            panic!("right operand");
        };
        let ExprNode::App { a: left, .. } = f.node() else {
            panic!("left operand");
        };
        assert_eq!(left, right);
        assert_eq!(left.allocation_identity(), right.allocation_identity());
        current = left;
    }
    assert!(matches!(current.node(), ExprNode::Proj { .. }));
    assert!(
        preparation.visited < 10_000,
        "linear analysis work: {}",
        preparation.visited
    );
}

fn metadata_engine() -> &'static Engine {
    static ENGINE: std::sync::OnceLock<Engine> = std::sync::OnceLock::new();
    ENGINE.get_or_init(|| {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[br#"
structure PruningGenericBox (A : Type) where
  value : A
structure PruningMetadata where
  proposition : Prop
  predicate : Nat -> Prop
  value : Nat
structure PruningFunction where
  callback : Nat -> Nat
structure PruningCarrier where
  carrier : Type
structure PruningIndexed (n : Nat) where
  value : Nat
def pruningTick (n : Nat) : Nat := n + 1
def pruningMetadataValue (box : PruningGenericBox Nat) : Nat :=
  (PruningMetadata.mk (box.value = 0) (fun n => box.value = n) box.value).value
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

fn metadata_box() -> Expr {
    Expr::app(c("PruningGenericBox"), c("Nat"))
}

fn metadata_projection(index: u32) -> Expr {
    Expr::proj(name("PruningGenericBox"), 0, Expr::bvar(index).unwrap())
}

fn equality(left: Expr, right: Expr) -> Expr {
    [c("Nat"), left, right]
        .into_iter()
        .fold(Expr::const_(name("Eq"), vec![Level::one()]), Expr::app)
}

#[test]
fn admitted_predicate_operands_keep_logical_projections_out_of_runtime_lowering() {
    let engine = metadata_engine();
    let root = engine.logical_root(&KVMap::new());
    let projection = metadata_projection(0);
    // The same projection node occurs in static metadata and in the strict
    // value field. A syntax-only skip cache would incorrectly skip the latter.
    let proposition = equality(projection.clone(), nat::literal(0));
    let predicate = Expr::lam(
        name("n"),
        c("Nat"),
        equality(shared(metadata_projection(1), 14), Expr::bvar(0).unwrap()),
        BinderInfo::Default,
    );
    let body = [proposition.clone(), predicate.clone(), projection.clone()]
        .into_iter()
        .fold(c("PruningMetadata.mk"), Expr::app);
    let input = Expr::lam(name("box"), metadata_box(), body, BinderInfo::Default);
    let limits = IngressLimits {
        max_nodes: 8192,
        ..IngressLimits::default()
    };
    let mut preparation = Preparation::new(engine.environment(), limits);
    let output = preparation.lower_projections(&input).unwrap();
    let required = preparation.visited;
    let ExprNode::Lam { body, .. } = output.node() else {
        panic!("outer receiver lambda");
    };
    let (head, fields) = preparation.spine(body).unwrap();
    assert_eq!(head, c("PruningMetadata.mk"));
    assert_eq!(fields.len(), 3);
    for (retained, original) in fields[..2].iter().zip([&proposition, &predicate]) {
        assert_eq!(retained, original);
        assert_eq!(
            retained.allocation_identity(),
            original.allocation_identity()
        );
    }
    let ExprNode::Proj {
        struct_name,
        idx,
        expr,
    } = fields[2].node()
    else {
        panic!("strict data field keeps its projection");
    };
    assert_ne!(struct_name, &name("PruningGenericBox"));
    assert_eq!(*idx, 0);
    assert_eq!(expr, &Expr::bvar(0).unwrap());
    assert!(!preparation.constructors.is_empty());

    for max_nodes in [0, required - 1] {
        let mut stopped = Preparation::new(
            engine.environment(),
            IngressLimits {
                max_nodes,
                ..limits
            },
        );
        assert!(matches!(
            stopped.lower_projections(&input),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
    let mut retry = Preparation::new(
        engine.environment(),
        IngressLimits {
            max_nodes: required,
            ..limits
        },
    );
    assert_eq!(retry.lower_projections(&input).unwrap(), output);
    assert_eq!(retry.visited, required);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn computational_callbacks_and_type_valued_operands_still_lower_their_projections() {
    let engine = metadata_engine();
    let initializer = Expr::app(c("pruningTick"), nat::literal(1));
    let callback = Expr::let_e(
        name("strict"),
        c("Nat"),
        initializer.clone(),
        Expr::lam(
            name("n"),
            c("Nat"),
            metadata_projection(2),
            BinderInfo::Default,
        ),
        false,
    );
    let carrier = Expr::app(c("PruningIndexed"), metadata_projection(0));
    for (constructor, operand, index) in [
        ("PruningFunction.mk", callback, 2),
        ("PruningCarrier.mk", carrier, 0),
    ] {
        let input = Expr::lam(
            name("box"),
            metadata_box(),
            Expr::app(c(constructor), operand),
            BinderInfo::Default,
        );
        let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
        let output = preparation.lower_projections(&input).unwrap();
        let ExprNode::Lam { body, .. } = output.node() else {
            panic!("outer receiver lambda");
        };
        let ExprNode::App { a, .. } = body.node() else {
            panic!("record constructor application");
        };
        let selected = match a.node() {
            ExprNode::LetE { value, body, .. } => {
                assert_eq!(value, &initializer);
                assert_eq!(
                    value.allocation_identity(),
                    initializer.allocation_identity()
                );
                let ExprNode::Lam { body, .. } = body.node() else {
                    panic!("the callback remains after its strict initializer");
                };
                body
            }
            ExprNode::App { a, .. } => a,
            _ => panic!("callback or Type-valued operand"),
        };
        let ExprNode::Proj {
            struct_name,
            expr,
            idx,
        } = selected.node()
        else {
            panic!("this operand must still visit its projection");
        };
        assert_ne!(struct_name, &name("PruningGenericBox"));
        assert_eq!(*idx, 0);
        assert_eq!(expr, &Expr::bvar(index).unwrap());
    }
}

#[test]
fn unknown_callees_do_not_authorize_skipping_an_operand() {
    let engine = metadata_engine();
    let invalid = Expr::proj(name("WrongFamily"), 0, Expr::bvar(0).unwrap());
    let input = Expr::lam(
        name("box"),
        metadata_box(),
        Expr::app(c("unknownPredicateConsumer"), invalid),
        BinderInfo::Default,
    );
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    assert!(matches!(
        preparation.lower_projections(&input),
        Err(IngressError::UnsupportedNode {
            kind: "projection receiver family mismatch"
        })
    ));
}

#[test]
fn a_record_with_predicate_metadata_executes_and_replays_its_value_field() {
    let engine = metadata_engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let result = engine
        .execute_source_definitions(
            &[b"#eval pruningMetadataValue (PruningGenericBox.mk 42)"],
            &options,
            limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.executions.len(), 1);
    let execution = &result.executions[0];
    assert_eq!(
        closed_vm_value(&execution.exit).unwrap(),
        Some(ClosedVmValue::Scalar(42))
    );
    let replay = execute_flbc_artifact(
        &execution.flbc_artifact,
        &options,
        FlbcExecutionLimits::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_eq!(
        closed_vm_value(&replay).unwrap(),
        Some(ClosedVmValue::Scalar(42))
    );
    assert_eq!(engine.logical_root(&options), root);
}
