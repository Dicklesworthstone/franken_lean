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
    Expr::forall_e(
        Name::anonymous(),
        callback_type(),
        arrow(arrow(nat_type())),
        BinderInfo::Default,
    )
}

fn consumer() -> (DefinitionVal, DefinitionVal) {
    // Applying f n executes its real prefix immediately. The produced action
    // is retained once, before recursion, and invoked with the later state.
    let next = Expr::app(b(1), b(0));
    let previous = call("stageConsume._unsafe_rec", [b(2), call("Nat.pred", [b(1)])]);
    let value = callback_parameter(lambda(choose(
        arrow(nat_type()),
        call("Nat.beq", [b(0), nat::literal(0)]),
        next.clone(),
        Expr::let_e(
            name("next"),
            arrow(nat_type()),
            next,
            Expr::let_e(
                name("previous"),
                arrow(nat_type()),
                previous,
                lambda(call(
                    "Nat.add",
                    [Expr::app(b(2), b(0)), Expr::app(b(1), b(0))],
                )),
                false,
            ),
            false,
        ),
    )));
    pair(
        "stageConsume",
        consumer_type(),
        callback_parameter(lambda(lambda(nat::literal(0)))),
        value,
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
fn checked_recursive_consumer_preserves_callback_stages_and_runtime_captures() {
    let engine = admit(consumer());
    returned(
        &engine,
        b"#eval stageConsume (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state) 3 2\n\
          #eval stageConsume (fun n => let saved := Nat.add 100 n; fun state => Nat.add saved state) 3 2\n\
          #eval stageConsume (fun n state => Nat.add n state) 3 2\n\
          #eval Nat.add (stageConsume (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state) 3 2) (stageConsume (fun n state => Nat.add n state) 3 2)\n\
          #eval let run : Nat -> Nat -> Nat := stageConsume (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state); run 3 2\n\
          #eval let action : Nat -> Nat := stageConsume (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state) 3; Nat.add (action 2) (action 3)",
        &["54", "414", "14", "68", "54", "112"],
    );
    // The safe logical half is unchanged by either private executable ABI.
    engine.check_source_files(
        &[b"theorem unchangedStageConsumer : stageConsume (fun n state => Nat.add n state) 3 2 = 0 := by rfl"],
        &KVMap::new(),
        SourceCheckLimits::new(limits().admission()),
    ).unwrap().into_complete().unwrap();
}

#[test]
fn a_callback_prefix_cannot_be_delayed_when_its_returned_action_is_ignored() {
    let engine = admit(pair(
        "stageSpin",
        arrow(nat_type()),
        lambda(nat::literal(0)),
        lambda(call("stageSpin._unsafe_rec", [b(0)])),
    ));
    let engine = extend(
        engine,
        pair(
            "stageIgnore",
            consumer_type(),
            callback_parameter(lambda(lambda(nat::literal(0)))),
            callback_parameter(lambda(Expr::let_e(
                name("action"),
                arrow(nat_type()),
                Expr::app(b(1), b(0)),
                lambda(nat::literal(42)),
                false,
            ))),
        ),
    );
    let root = engine.logical_root(&KVMap::new());
    let mut bounded = limits();
    bounded.vm.max_steps = 500;
    for source in [
        b"#eval let ignored : Nat -> Nat := stageIgnore (fun n => let paid := stageSpin n; fun state => Nat.add paid state) 3; 42".as_slice(),
        b"#eval stageIgnore (fun n => let paid := stageSpin n; fun state => Nat.add paid state) 3 5".as_slice(),
    ] {
        assert!(matches!(
            engine.execute_source_definitions(&[source], &KVMap::new(), bounded).unwrap(),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    returned(
        &engine,
        b"#eval stageIgnore (fun n => let paid := Nat.add n 1; fun state => Nat.add paid state) 3 5",
        &["42"],
    );
}

#[test]
fn callback_stage_cache_keeps_values_dynamic_and_flat_calls_separate() {
    let engine = admit(consumer());
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let head = call("stageConsume._unsafe_rec", []);
    for offset in [10, 100, 10] {
        preparation
            .partial_stage_call(&head, &[staged(offset), nat::literal(3), nat::literal(2)])
            .unwrap()
            .unwrap();
        assert_eq!(preparation.partial_stages.entries.len(), 2);
        assert_eq!(preparation.partial_stages.callbacks.len(), 1);
        assert_eq!(preparation.partial_stages.origins.len(), 1);
    }
    let original = &preparation.partial_stages.entries[0];
    let specialized = &preparation.partial_stages.entries[1];
    assert_ne!(original.parameter_types[0], specialized.parameter_types[0]);
    assert_eq!(
        original.parameter_types[1..],
        specialized.parameter_types[1..]
    );
    assert_eq!(original.suffix, specialized.suffix);
    assert_eq!(original.type_, specialized.type_);
    preparation
        .partial_stage_call(
            &head,
            &[
                lambda(lambda(call("Nat.add", [b(1), b(0)]))),
                nat::literal(3),
                nat::literal(2),
            ],
        )
        .unwrap()
        .unwrap();
    assert_eq!(preparation.partial_stages.entries.len(), 2);
    assert_eq!(preparation.partial_stages.callbacks.len(), 1);
}

#[test]
fn changed_or_missing_recursive_callback_forwarding_refuses_without_a_variant() {
    let changed = callback_parameter(lambda(choose(
        arrow(nat_type()),
        call("Nat.beq", [b(0), nat::literal(0)]),
        Expr::app(b(1), b(0)),
        call(
            "changedStage._unsafe_rec",
            [
                lambda(lambda(Expr::app(Expr::app(b(3), b(1)), b(0)))),
                call("Nat.pred", [b(0)]),
            ],
        ),
    )));
    let bare = callback_parameter(lambda(Expr::let_e(
        name("saved"),
        consumer_type(),
        call("bareStage._unsafe_rec", []),
        lambda(nat::literal(0)),
        false,
    )));
    for (label, value) in [("changedStage", changed), ("bareStage", bare)] {
        let engine = admit(pair(
            label,
            consumer_type(),
            callback_parameter(lambda(lambda(nat::literal(0)))),
            value,
        ));
        let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
        let head = Expr::const_(Name::str(name(label), "_unsafe_rec"), Vec::new());
        assert!(matches!(
            preparation.partial_stage_call(&head, &[staged(10), nat::literal(3)]),
            Err(IngressError::UnsupportedNode {
                kind: "partial callback recursive forwarding"
            })
        ));
        assert_eq!(preparation.partial_stages.entries.len(), 1);
        assert!(preparation.partial_stages.callbacks.is_empty());
        returned(&engine, b"#eval 42", &["42"]);
    }
}

#[test]
fn callback_variant_limits_and_reserved_names_fail_before_publication() {
    let engine = admit(consumer());
    let head = call("stageConsume._unsafe_rec", []);
    let arguments = [staged(10), nat::literal(3)];
    let mut bounded = IngressLimits::default();
    bounded.fir.max_functions = 1;
    let mut preparation = Preparation::new(engine.environment(), bounded);
    assert!(matches!(
        preparation.partial_stage_call(&head, &arguments),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: 1,
            observed: 2,
        })
    ));
    assert_eq!(preparation.partial_stages.entries.len(), 1);
    assert!(preparation.partial_stages.callbacks.is_empty());

    let engine = engine
        .admit_declaration(
            Declaration::Axiom(fln_env::constants::AxiomVal {
                base: ConstantVal {
                    name: Name::num(name_of_stages(), 1),
                    level_params: Vec::new(),
                    type_: nat_type(),
                },
                is_unsafe: false,
            }),
            &KVMap::new(),
            limits().admission(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    assert!(matches!(
        preparation.partial_stage_call(&head, &arguments),
        Err(IngressError::UnsupportedNode {
            kind: "partial stage name collision"
        })
    ));
    assert_eq!(preparation.partial_stages.entries.len(), 1);
    assert!(preparation.partial_stages.callbacks.is_empty());
}
