//! Fully lambda-bound recursive consumers retain a callback's actual stages.
use super::*;

fn callback_type() -> Expr {
    arrow(arrow(nat_type()))
}

fn callback_parameter(body: Expr) -> Expr {
    Expr::lam(
        Name::anonymous(),
        callback_type(),
        body,
        BinderInfo::Default,
    )
}

fn consumer_type() -> Expr {
    arrow(Expr::forall_e(
        Name::anonymous(),
        callback_type(),
        arrow(nat_type()),
        BinderInfo::Default,
    ))
}

fn consumer() -> (DefinitionVal, DefinitionVal) {
    consumer_with_forwarding(false)
}

fn consumer_with_forwarding(changed: bool) -> (DefinitionVal, DefinitionVal) {
    // The callback is the middle parameter. Its prefix executes before
    // recursion, and its retained suffix consumes the original final state.
    let recursive = Expr::let_e(
        name("action"),
        arrow(nat_type()),
        Expr::app(b(1), b(2)),
        Expr::let_e(
            name("previous"),
            nat_type(),
            call(
                "fullStageConsume._unsafe_rec",
                [
                    call("Nat.pred", [b(3)]),
                    if changed {
                        lambda(lambda(Expr::app(Expr::app(b(4), b(1)), b(0))))
                    } else {
                        b(2)
                    },
                    call("Nat.add", [b(1), nat::literal(1)]),
                ],
            ),
            call("Nat.add", [Expr::app(b(1), b(2)), b(0)]),
            false,
        ),
        false,
    );
    pair(
        "fullStageConsume",
        consumer_type(),
        lambda(callback_parameter(lambda(nat::literal(0)))),
        lambda(callback_parameter(lambda(choose(
            nat_type(),
            call("Nat.beq", [b(2), nat::literal(0)]),
            Expr::app(Expr::app(b(1), b(2)), b(0)),
            recursive,
        )))),
    )
}

fn staged(offset: u64) -> Expr {
    lambda(Expr::let_e(
        name("captured"),
        nat_type(),
        call("Nat.add", [nat::literal(offset), b(0)]),
        lambda(call("Nat.add", [b(1), b(0)])),
        false,
    ))
}

fn computed_staged(offset: u64) -> Expr {
    Expr::let_e(
        name("prefix"),
        nat_type(),
        call("Nat.add", [nat::literal(offset), nat::literal(0)]),
        lambda(Expr::let_e(
            name("captured"),
            nat_type(),
            call("Nat.add", [b(1), b(0)]),
            lambda(call("Nat.add", [b(1), b(0)])),
            false,
        )),
        false,
    )
}

#[test]
fn fully_bound_recursive_consumers_keep_dynamic_middle_callbacks_and_replay() {
    let engine = admit(consumer());
    returned(
        &engine,
        b"#eval fullStageConsume 3 (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state) 2\n\
          #eval fullStageConsume 3 (fun n => let saved := Nat.add 100 n; fun state => Nat.add saved state) 2\n\
          #eval fullStageConsume 3 (fun n state => Nat.add n state) 2\n\
          #eval let action : Nat -> Nat := fullStageConsume 3 (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state); Nat.add (action 2) (action 3)",
        &["60", "420", "20", "124"],
    );
    engine.check_source_files(
        &[b"theorem logicalFullStage : fullStageConsume 3 (fun n state => Nat.add n state) 2 = 0 := by rfl"],
        &KVMap::new(),
        SourceCheckLimits::new(limits().admission()),
    ).unwrap().into_complete().unwrap();

    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let head = call("fullStageConsume._unsafe_rec", []);
    for offset in [10, 100, 10] {
        assert!(
            preparation
                .partial_stage_call(&head, &[nat::literal(3), staged(offset), nat::literal(2)])
                .unwrap()
                .is_some()
        );
        assert_eq!(preparation.partial_stages.entries.len(), 1);
        assert_eq!(preparation.partial_stages.callbacks.len(), 1);
        assert!(preparation.partial_stages.origins.is_empty());
    }
    assert!(
        preparation
            .partial_stage_call(
                &head,
                &[
                    nat::literal(3),
                    lambda(lambda(call("Nat.add", [b(1), b(0)]))),
                    nat::literal(2),
                ],
            )
            .unwrap()
            .is_none()
    );
    assert_eq!(preparation.partial_stages.entries.len(), 1);
}

#[test]
fn dead_callback_source_results_are_discarded_and_live_results_execute() {
    let engine = admit(pair(
        "fullStageSpin",
        arrow(nat_type()),
        lambda(nat::literal(0)),
        lambda(call("fullStageSpin._unsafe_rec", [b(0)])),
    ));
    let engine = extend(
        engine,
        pair(
            "fullStageIgnore",
            consumer_type(),
            lambda(callback_parameter(lambda(nat::literal(0)))),
            lambda(callback_parameter(lambda(Expr::let_e(
                name("ignored"),
                arrow(nat_type()),
                Expr::app(b(1), b(2)),
                choose(
                    nat_type(),
                    call("Nat.beq", [b(3), nat::literal(0)]),
                    nat::literal(42),
                    call(
                        "fullStageIgnore._unsafe_rec",
                        [call("Nat.pred", [b(3)]), b(2), b(1)],
                    ),
                ),
                false,
            )))),
        ),
    );
    let engine = extend(
        engine,
        pair(
            "fullStageUse",
            consumer_type(),
            lambda(callback_parameter(lambda(nat::literal(0)))),
            lambda(callback_parameter(lambda(Expr::let_e(
                name("action"),
                arrow(nat_type()),
                Expr::app(b(1), b(2)),
                choose(
                    nat_type(),
                    call("Nat.beq", [b(3), nat::literal(0)]),
                    Expr::app(b(0), b(1)),
                    call(
                        "Nat.add",
                        [
                            Expr::app(b(0), b(1)),
                            call(
                                "fullStageUse._unsafe_rec",
                                [call("Nat.pred", [b(3)]), b(2), b(1)],
                            ),
                        ],
                    ),
                ),
                false,
            )))),
        ),
    );
    let original = engine.logical_root(&KVMap::new());
    let mut bounded = limits();
    bounded.vm.max_steps = 500;
    let run_dead = |count, producer: &str| {
        let source = format!(
            "#eval fullStageIgnore {count} (fun n => let paid := {producer}; fun state => Nat.add paid state) 5"
        );
        let batch = engine
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), bounded)
            .unwrap()
            .into_complete()
            .unwrap_or_else(|stop| panic!("{source}: {stop:?}"));
        let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
            panic!("the discarded source callback must return 42");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42"),
            "{source}"
        );
        value.usage.steps
    };
    for count in [0, 3] {
        // The pin removes an unused pure source binding before discovering
        // callback stages. Its first-stage producer must remain unexecuted;
        // strict runtime operands have their separate regression below.
        assert_eq!(
            run_dead(count, "fullStageSpin n"),
            run_dead(count, "Nat.add n 1"),
            "an erased source callback result must not run its producer"
        );
        let source = format!(
            "#eval fullStageUse {count} (fun n => let paid := fullStageSpin n; fun state => Nat.add paid state) 5"
        );
        let outcome = engine
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), bounded)
            .unwrap();
        assert!(
            matches!(outcome, Outcome::Inconclusive(_)),
            "{source}: a live callback result must execute its diverging first stage"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), original);
    }
    returned(
        &engine,
        b"#eval fullStageIgnore 3 (fun n => let paid := Nat.add n 1; fun state => Nat.add paid state) 5\n\
          #eval fullStageUse 0 (fun n => let paid := Nat.add n 1; fun state => Nat.add paid state) 5",
        &["42", "6"],
    );
}

#[test]
fn computed_callbacks_keep_dynamic_captures_recursive_stages_and_replay() {
    let engine = admit(consumer())
        .check_source_files(
            &[br#"def computedRun (offset : Nat) : Nat :=
  fullStageConsume 3 (let paid := Nat.add offset 0; fun n => let saved := Nat.add paid n; fun state => Nat.add saved state) 2"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    returned(
        &engine,
        b"#eval computedRun 10\n\
          #eval computedRun 100\n\
          #eval let action : Nat -> Nat := fullStageConsume 3 (let paid := Nat.add 9 1; fun n => let saved := Nat.add paid n; fun state => Nat.add saved state); Nat.add (action 2) (action 3)",
        &["60", "420", "124"],
    );

    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let head = call("fullStageConsume._unsafe_rec", []);
    for offset in [10, 100, 10] {
        let callback = computed_staged(offset);
        assert!(preparation.inert_callable(&callback).unwrap().is_none());
        assert!(
            preparation
                .partial_stage_call(&head, &[nat::literal(3), callback, nat::literal(2)])
                .unwrap()
                .is_some()
        );
        assert_eq!(preparation.partial_stages.entries.len(), 1);
        assert_eq!(preparation.partial_stages.callbacks.len(), 1);
        assert!(preparation.partial_stages.origins.is_empty());
    }
}

#[test]
fn computed_callback_producers_run_once_and_before_an_unused_consumer() {
    let engine = extend(
        admit(consumer()),
        pair(
            "fullStageSpend",
            arrow(nat_type()),
            lambda(nat::literal(0)),
            lambda(choose(
                nat_type(),
                call("Nat.beq", [b(0), nat::literal(0)]),
                nat::literal(0),
                call(
                    "Nat.add",
                    [
                        call("fullStageSpend._unsafe_rec", [call("Nat.pred", [b(0)])]),
                        nat::literal(1),
                    ],
                ),
            )),
        ),
    );
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let steps = |source: &str, expected: &str| {
        let run = engine
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap();
        let VmExit::Returned(result) = &run.executions.last().unwrap().exit else {
            panic!("computed callback producer must return");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
            Some(expected)
        );
        result.usage.steps
    };
    let once = steps("#eval fullStageSpend 25", "25")
        .checked_sub(steps("#eval fullStageSpend 0", "0"))
        .unwrap();
    assert!(once > 25);
    let source = |cost| {
        format!(
            "#eval fullStageConsume 3 (let paid := fullStageSpend {cost}; fun n => let saved := Nat.add paid n; fun state => Nat.add saved state) 2"
        )
    };
    let idle = steps(&source(0), "20");
    let busy = steps(&source(25), "120");
    assert_eq!(
        busy.checked_sub(idle).unwrap(),
        once,
        "recursive callback uses must share their producer's strict prefix"
    );
    let mut bounded = limits();
    bounded.vm.max_steps = idle;
    assert!(matches!(
        engine
            .execute_source_definitions(&[source(25).as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(engine.logical_root(&options), root);
    assert_eq!(steps(&source(0), "20"), idle);

    let engine = extend(
        engine,
        pair(
            "fullStageSpin",
            arrow(nat_type()),
            lambda(nat::literal(0)),
            lambda(call("fullStageSpin._unsafe_rec", [b(0)])),
        ),
    );
    let engine = extend(
        engine,
        pair(
            "fullStageDiscard",
            consumer_type(),
            lambda(callback_parameter(lambda(nat::literal(42)))),
            lambda(callback_parameter(lambda(nat::literal(42)))),
        ),
    );
    let root = engine.logical_root(&options);
    bounded.vm.max_steps = 500;
    assert!(matches!(
        engine
            .execute_source_definitions(
                &[b"#eval fullStageDiscard 0 (let paid := fullStageSpin 1; fun n => let saved := Nat.add paid n; fun state => Nat.add saved state) 2"],
                &options,
                bounded,
            )
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(engine.logical_root(&options), root);
    returned(
        &engine,
        b"#eval fullStageDiscard 0 (let paid := Nat.add 9 1; fun n => let saved := Nat.add paid n; fun state => Nat.add saved state) 2",
        &["42"],
    );
}

#[test]
fn computed_callback_forwarding_mismatches_and_limits_publish_no_variant() {
    let engine = admit(consumer_with_forwarding(true));
    let head = call("fullStageConsume._unsafe_rec", []);
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    assert!(matches!(
        preparation.partial_stage_call(
            &head,
            &[nat::literal(3), computed_staged(10), nat::literal(2)],
        ),
        Err(IngressError::UnsupportedNode {
            kind: "partial callback recursive forwarding"
        })
    ));
    assert!(preparation.partial_stages.entries.is_empty());
    assert!(preparation.partial_stages.callbacks.is_empty());

    let engine = admit(consumer());
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    assert!(
        preparation
            .partial_stage_call(
                &head,
                &[
                    call("Nat.add", [nat::literal(2), nat::literal(1)]),
                    b(0),
                    nat::literal(2),
                ],
            )
            .unwrap()
            .is_none(),
        "a computed scalar argument cannot select an unknown callback interface"
    );
    assert!(preparation.partial_stages.entries.is_empty());
    assert!(preparation.partial_stages.callbacks.is_empty());
    for source in [
        b"#eval fullStageConsume 3 (let paid := Nat.add 9 1; fun (_ : Bool) => let saved := Nat.add paid 1; fun state => Nat.add saved state) 2".as_slice(),
        b"#eval fullStageConsume 3 (let paid := Nat.add 9 1; fun n => let saved := Nat.add paid n; fun (_ : Nat) => true) 2".as_slice(),
    ] {
        assert!(
            engine
                .check_source_files(&[source], &options, SourceCheckLimits::new(limits().admission()))
                .is_err(),
            "a computed callback must retain its checked domain and result"
        );
        assert_eq!(engine.logical_root(&options), root);
    }
    let mut bounded = IngressLimits::default();
    bounded.fir.max_functions = 0;
    let mut preparation = Preparation::new(engine.environment(), bounded);
    assert!(matches!(
        preparation.partial_stage_call(
            &head,
            &[nat::literal(3), computed_staged(10), nat::literal(2)],
        ),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: 0,
            observed: 1,
        })
    ));
    assert!(preparation.partial_stages.entries.is_empty());
    assert!(preparation.partial_stages.callbacks.is_empty());
    returned(
        &engine,
        b"#eval fullStageConsume 3 (let paid := Nat.add 9 1; fun n => let saved := Nat.add paid n; fun state => Nat.add saved state) 2",
        &["60"],
    );
}
