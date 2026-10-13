use super::*;
use fln_core::diag::ResourceReason;
use fln_core::outcome::InconclusiveCause;

const STACK: usize = 2 * 1024 * 1024;

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
        .unwrap()
        .into_complete()
        .unwrap()
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn app(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

#[test]
fn completed_native_bindings_preserve_full_contracts_and_both_work_counters() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let target = name("Nat.add");
    let expected = executable_intrinsic_binding_cached(
        engine.environment(),
        &target,
        &mut 0,
        IngressLimits::default(),
        &mut None,
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        preparation.native_intrinsic_binding(&target).unwrap(),
        Some(expected.clone())
    );
    let first = preparation.visited;
    assert!(first > 100, "the complete Nat model was checked");
    assert_eq!(
        preparation.native_intrinsic_binding(&target).unwrap(),
        Some(expected.clone())
    );
    assert_eq!(preparation.visited, first + 1);

    let mut catalog_work = 11;
    assert_eq!(
        preparation
            .catalog_native_intrinsic_binding(
                &target,
                &mut catalog_work,
                IngressLimits {
                    max_nodes: 12,
                    ..IngressLimits::default()
                },
            )
            .unwrap(),
        Some(expected)
    );
    assert_eq!(catalog_work, 12);
    assert_eq!(preparation.visited, first + 1);

    // A catalog miss can establish the same completed contract for a later
    // expression query, while charging only the original catalog meter.
    let target = name("String.append");
    let mut catalog_work = 0;
    let expected = preparation
        .catalog_native_intrinsic_binding(&target, &mut catalog_work, IngressLimits::default())
        .unwrap()
        .unwrap();
    assert!(catalog_work > 0);
    assert_eq!(expected.result, ValueType::String);
    assert_eq!(
        expected.result_ownership,
        fln_comp::flbc::ResultOwnership::Owned
    );
    assert_eq!(preparation.visited, first + 1);
    let mut returned = preparation
        .native_intrinsic_binding(&target)
        .unwrap()
        .unwrap();
    assert_eq!(returned, expected);
    assert_eq!(preparation.visited, first + 2);
    returned.row.clear();
    returned.arguments.clear();
    returned.argument_ownership.clear();
    assert_eq!(
        preparation.native_intrinsic_binding(&target).unwrap(),
        Some(expected),
        "a caller cannot mutate the completed contract through its result"
    );
    assert_eq!(preparation.native_intrinsics.entries.len(), 2);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn cache_hits_obey_the_callers_node_limit_without_borrowing_the_other_meter() {
    let engine = engine();
    let target = name("Nat.add");
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let expected = preparation.native_intrinsic_binding(&target).unwrap();
    let work = preparation.visited;
    preparation.limits.max_nodes = work;
    assert_eq!(
        preparation.native_intrinsic_binding(&target),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: work,
            observed: work + 1,
        })
    );
    let mut catalog_work = 0;
    assert_eq!(
        preparation.catalog_native_intrinsic_binding(
            &target,
            &mut catalog_work,
            IngressLimits {
                max_nodes: 0,
                ..IngressLimits::default()
            },
        ),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 0,
            observed: 1,
        })
    );
    assert_eq!(catalog_work, 0);
    assert_eq!(preparation.visited, work);
    assert_eq!(
        preparation
            .catalog_native_intrinsic_binding(
                &target,
                &mut catalog_work,
                IngressLimits {
                    max_nodes: 1,
                    ..IngressLimits::default()
                },
            )
            .unwrap(),
        expected
    );
    assert_eq!(catalog_work, 1);
    assert_eq!(preparation.visited, work);
    preparation.limits.max_nodes = work + 1;
    assert_eq!(
        preparation.native_intrinsic_binding(&target).unwrap(),
        expected
    );
    assert_eq!(preparation.visited, work + 1);
}

#[test]
fn missing_models_and_extern_refusals_never_publish_native_bindings() {
    let engine = engine();
    let target = name("Nat.add");
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    for _ in 0..2 {
        assert_eq!(
            preparation
                .native_intrinsic_binding(&name("notNative"))
                .unwrap(),
            None
        );
    }
    assert_eq!(
        preparation.visited, 0,
        "negative names retain their existing fast path"
    );
    assert!(preparation.native_intrinsics.entries.is_empty());

    let changed = fln_elab::externs::register(
        engine.environment(),
        &target,
        vec![fln_elab::externs::ExternEntry::Opaque],
    )
    .unwrap();
    let mut rejected = Preparation::new(&changed, IngressLimits::default());
    for _ in 0..2 {
        let before = rejected.visited;
        assert!(matches!(
            rejected.native_intrinsic_binding(&target),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(rejected.visited > before);
        assert!(rejected.native_intrinsics.entries.is_empty());
    }
    assert!(
        preparation
            .native_intrinsic_binding(&target)
            .unwrap()
            .is_some()
    );

    // A separate immutable world must prove its own full model. This scratch
    // counterfeit is only recognizer input, never an admitted Engine snapshot.
    let mut counterfeit = Environment::new();
    for (label, _) in engine.environment().constants() {
        if label != &target {
            counterfeit = counterfeit
                .with_entry(engine.environment().entry(label).unwrap())
                .unwrap();
        }
    }
    let ConstantInfo::Defn(mut changed) = engine.environment().find(&target).unwrap().clone()
    else {
        panic!("the checked Nat.add model is a definition");
    };
    changed.value = Expr::lam(
        Name::anonymous(),
        c("Nat"),
        Expr::lam(
            Name::anonymous(),
            c("Nat"),
            nat::literal(42),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    counterfeit = counterfeit.add_decl(ConstantInfo::Defn(changed)).unwrap();
    let mut rejected = Preparation::new(&counterfeit, IngressLimits::default());
    assert_eq!(rejected.native_intrinsic_binding(&target).unwrap(), None);
    assert!(rejected.native_intrinsics.entries.is_empty());
    assert!(
        preparation
            .native_intrinsic_binding(&target)
            .unwrap()
            .is_some()
    );
}

#[test]
fn a_failed_final_insertion_leaves_no_binding_and_a_clean_retry_succeeds() {
    let engine = engine();
    let target = name("Nat.add");
    let mut model_work = 0;
    let expected = executable_intrinsic_binding_cached(
        engine.environment(),
        &target,
        &mut model_work,
        IngressLimits::default(),
        &mut None,
    )
    .unwrap()
    .unwrap();
    let mut preparation = Preparation::new(
        engine.environment(),
        IngressLimits {
            max_nodes: model_work,
            ..IngressLimits::default()
        },
    );
    assert_eq!(
        preparation.native_intrinsic_binding(&target),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: model_work,
            observed: model_work + 1,
        })
    );
    assert_eq!(preparation.visited, model_work);
    assert!(preparation.native_intrinsics.entries.is_empty());
    preparation.visited = 0;
    preparation.limits = IngressLimits::default();
    assert_eq!(
        preparation.native_intrinsic_binding(&target).unwrap(),
        Some(expected.clone())
    );
    assert_eq!(preparation.native_intrinsics.entries.len(), 1);

    // The independent table bound applies before allocation/publication even
    // when its input is an already completed genuine contract.
    let mut store = Store::default();
    assert_eq!(
        store.remember(&target, &expected, 0),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 0,
            observed: 1,
        })
    );
    assert!(store.entries.is_empty());
    store.remember(&target, &expected, 1).unwrap();
    assert_eq!(store.entries.get(&target), Some(&expected));
}

#[test]
fn a_warmed_logical_model_cannot_override_explicit_implementation_routing() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
    let engine = engine()
        .check_source_files(
            &[b"def cachedImplementation (left right : Nat) : Nat := right"],
            &KVMap::new(),
            SourceCheckLimits::new(limits.admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let environment = fln_elab::implemented_by::register(
        engine.environment(),
        &name("Nat.add"),
        &name("cachedImplementation"),
    )
    .unwrap();
    let engine = Engine::from_environment(environment);
    let root = engine.logical_root(&KVMap::new());
    let original = engine.environment().find(&name("Nat.add")).unwrap().clone();
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    assert!(
        preparation
            .native_intrinsic_binding(&name("Nat.add"))
            .unwrap()
            .is_some()
    );
    let arguments = [nat::literal(20), nat::literal(22)];
    assert_eq!(
        preparation
            .implemented_by_call(&c("Nat.add"), &arguments)
            .unwrap(),
        Some(app(c("cachedImplementation"), arguments))
    );
    assert_eq!(
        preparation.implemented_by_call(&c("Nat.add"), &[]).unwrap(),
        Some(c("cachedImplementation"))
    );
    assert_eq!(engine.environment().find(&name("Nat.add")), Some(&original));
    let execution = engine
        .execute_source_definitions(&[b"#eval Nat.add 20 22"], &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(returned) = &execution.executions.last().unwrap().exit else {
        panic!("the selected checked implementation must execute");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
        Some("22")
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn repeated_native_operations_keep_runtime_work_owned_results_and_canonical_replay() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
    let options = KVMap::new();
    let engine = engine()
        .check_source_files(
            &[b"def nativeCacheSpend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (nativeCacheSpend k)"],
            &options,
            SourceCheckLimits::new(limits.admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = engine.logical_root(&options);
    let source = |cost| format!("#eval Nat.add (nativeCacheSpend {cost}) (Nat.add 20 22)");
    let execute = |cost, expected| {
        let source = source(cost);
        let completed = engine
            .execute_source_definitions(&[source.as_bytes()], &options, limits)
            .unwrap()
            .into_complete()
            .unwrap();
        let execution = completed.executions.last().unwrap();
        let VmExit::Returned(returned) = &execution.exit else {
            panic!("native arithmetic must execute every operand");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
            Some(expected)
        );
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        let VmExit::Returned(replay) = replay else {
            panic!("canonical native arithmetic must replay");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&replay.value).as_deref(),
            Some(expected)
        );
        assert_eq!(replay.usage, returned.usage);
        returned.usage.steps
    };
    let idle = execute(0, "42");
    let busy = execute(30, "72");
    assert!(busy > idle + 30);
    let mut bounded = limits;
    bounded.vm.max_steps = idle;
    let stopped = engine
        .execute_source_definitions(&[source(30).as_bytes()], &options, bounded)
        .unwrap();
    assert!(matches!(
        stopped,
        Outcome::Inconclusive(stop)
            if matches!(&stop.cause,
                InconclusiveCause::ResourceExhausted { usage }
                    if usage.reason == ResourceReason::ExecutionSteps
                        && usage.allowed == idle && usage.observed == idle + 1)
    ));
    assert_eq!(execute(0, "42"), idle);

    let source = r#"#eval String.append (String.append "λ" "😀") (String.append "\x00" "done")"#;
    let mut previous = None;
    for _ in 0..2 {
        let completed = engine
            .execute_source_definitions(&[source.as_bytes()], &options, limits)
            .unwrap()
            .into_complete()
            .unwrap();
        let execution = completed.executions.last().unwrap();
        let VmExit::Returned(returned) = &execution.exit else {
            panic!("owned native String operations must return");
        };
        assert_eq!(
            closed_vm_value(&execution.exit).unwrap(),
            Some(ClosedVmValue::String("λ😀\0done".to_owned()))
        );
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        let VmExit::Returned(replayed) = &replay else {
            panic!("owned native Strings must survive canonical decoding");
        };
        assert_eq!(
            closed_vm_value(&replay).unwrap(),
            Some(ClosedVmValue::String("λ😀\0done".to_owned()))
        );
        assert_eq!(replayed.usage, returned.usage);
        if let Some(previous) = &previous {
            assert_eq!(&execution.flbc_artifact, previous);
        }
        previous = Some(execution.flbc_artifact.clone());
    }
    assert_eq!(engine.logical_root(&options), root);
}
