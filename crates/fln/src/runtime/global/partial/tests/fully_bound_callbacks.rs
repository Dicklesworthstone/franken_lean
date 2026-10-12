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
                    b(2),
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
fn ignored_callback_results_still_execute_their_prefix_in_fully_bound_consumers() {
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
    let original = engine.logical_root(&KVMap::new());
    let mut bounded = limits();
    bounded.vm.max_steps = 500;
    for source in [
        b"#eval fullStageIgnore 0 (fun n => let paid := fullStageSpin n; fun state => Nat.add paid state) 5".as_slice(),
        b"#eval fullStageIgnore 3 (fun n => let paid := fullStageSpin n; fun state => Nat.add paid state) 5".as_slice(),
    ] {
        assert!(matches!(
            engine.execute_source_definitions(&[source], &KVMap::new(), bounded).unwrap(),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(engine.logical_root(&KVMap::new()), original);
    }
    returned(
        &engine,
        b"#eval fullStageIgnore 3 (fun n => let paid := Nat.add n 1; fun state => Nat.add paid state) 5",
        &["42"],
    );
}
