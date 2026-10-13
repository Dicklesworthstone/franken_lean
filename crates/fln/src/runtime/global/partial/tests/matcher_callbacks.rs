//! Checked matcher minors may rebind an unchanged recursive callback.
use super::*;

fn callback_type() -> Expr {
    arrow(arrow(nat_type()))
}

fn callback_parameter(body: Expr) -> Expr {
    lam(callback_type(), body)
}

fn consumer_type() -> Expr {
    forall(callback_type(), arrow(arrow(nat_type())))
}

fn forall(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn matcher() -> DefinitionVal {
    let boolean = call("Bool", []);
    let minor = consumer_type();
    // Rebind the same callback and argument in each minor, like the admitted
    // List.foldlM.match_1. The third, computed operand is intentionally unused.
    let value = callback_parameter(lambda(lambda(lam(
        boolean.clone(),
        lam(
            minor.clone(),
            lam(
                minor.clone(),
                choose(
                    arrow(nat_type()),
                    b(2),
                    Expr::app(Expr::app(b(0), b(5)), b(4)),
                    Expr::app(Expr::app(b(1), b(5)), b(4)),
                ),
            ),
        ),
    ))));
    DefinitionVal {
        base: ConstantVal {
            name: name("callbackStageMatcher"),
            level_params: Vec::new(),
            type_: forall(
                callback_type(),
                arrow(arrow(forall(
                    boolean,
                    forall(minor.clone(), forall(minor, arrow(nat_type()))),
                ))),
            ),
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("callbackStageMatcher")],
    }
}

fn consumer(changed: bool, diverging: bool) -> (DefinitionVal, DefinitionVal) {
    let forwarded = if changed {
        // Extensionally equal is insufficient: recursive stage selection must
        // preserve the exact runtime callback value, including its captures.
        lambda(lambda(Expr::app(Expr::app(b(4), b(1)), b(0))))
    } else {
        b(2)
    };
    let recursive = Expr::let_e(
        name("next"),
        arrow(nat_type()),
        Expr::app(b(1), b(0)),
        Expr::let_e(
            name("previous"),
            arrow(nat_type()),
            call(
                "matchedStage._unsafe_rec",
                [forwarded, call("Nat.pred", [b(1)])],
            ),
            lambda(call(
                "Nat.add",
                [Expr::app(b(2), b(0)), Expr::app(b(1), b(0))],
            )),
            false,
        ),
        false,
    );
    let paid = if diverging {
        call("matcherStageSpin", [b(0)])
    } else {
        call("Nat.add", [b(0), nat::literal(0)])
    };
    pair(
        "matchedStage",
        consumer_type(),
        callback_parameter(lambda(lambda(nat::literal(0)))),
        callback_parameter(lambda(call(
            "callbackStageMatcher",
            [
                b(1),
                b(0),
                paid,
                call("Nat.beq", [b(0), nat::literal(0)]),
                callback_parameter(lambda(recursive)),
                callback_parameter(lambda(Expr::app(b(1), b(0)))),
            ],
        ))),
    )
}

fn engine(changed: bool, diverging: bool) -> Engine {
    let engine = admit(pair(
        "matcherStageSpin",
        arrow(nat_type()),
        lambda(nat::literal(0)),
        lambda(call("matcherStageSpin._unsafe_rec", [b(0)])),
    ));
    let engine = engine
        .admit_declaration(
            Declaration::Defn(matcher()),
            &KVMap::new(),
            limits().admission(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    extend(engine, consumer(changed, diverging))
}

fn staged(offset: u64) -> Expr {
    lambda(Expr::let_e(
        name("saved"),
        nat_type(),
        call("Nat.add", [nat::literal(offset), b(0)]),
        lambda(call("Nat.add", [b(1), b(0)])),
        false,
    ))
}

#[test]
fn checked_matcher_rebinding_preserves_recursive_callback_stages_and_captures() {
    let engine = engine(false, false);
    returned(
        &engine,
        b"#eval matchedStage (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state) 3 2\n\
          #eval matchedStage (fun n => let saved := Nat.add 100 n; fun state => Nat.add saved state) 3 2\n\
          #eval matchedStage (fun n state => Nat.add n state) 3 2\n\
          #eval Nat.add (matchedStage (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state) 3 2) (matchedStage (fun n => let saved := Nat.add 100 n; fun state => Nat.add saved state) 3 2)\n\
          #eval let action : Nat -> Nat := matchedStage (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state) 3; Nat.add (action 2) (action 3)",
        &["54", "414", "14", "468", "112"],
    );
    engine
        .check_source_files(
            &[b"theorem logicalMatchedStage : matchedStage (fun n state => Nat.add n state) 3 2 = 0 := by rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap();

    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let head = call("matchedStage._unsafe_rec", []);
    for offset in [10, 100, 10] {
        assert!(
            preparation
                .partial_stage_call(&head, &[staged(offset), nat::literal(3)])
                .unwrap()
                .is_some()
        );
        assert_eq!(preparation.partial_stages.entries.len(), 2);
        assert_eq!(preparation.partial_stages.callbacks.len(), 1);
    }
}

#[test]
fn changed_callback_in_a_checked_matcher_minor_refuses_without_a_variant() {
    let engine = engine(true, false);
    let original = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    assert!(matches!(
        preparation.partial_stage_call(
            &call("matchedStage._unsafe_rec", []),
            &[staged(10), nat::literal(3)],
        ),
        Err(IngressError::UnsupportedNode {
            kind: "partial callback recursive forwarding",
        })
    ));
    assert_eq!(preparation.partial_stages.entries.len(), 1);
    assert!(preparation.partial_stages.callbacks.is_empty());
    assert_eq!(engine.logical_root(&KVMap::new()), original);
    returned(&engine, b"#eval 42", &["42"]);
}

#[test]
fn checked_matcher_exposure_keeps_unused_computed_arguments_strict() {
    let engine = engine(false, true);
    let original = engine.logical_root(&KVMap::new());
    let mut bounded = limits();
    bounded.vm.max_steps = 500;
    for source in [
        b"#eval let ignored : Nat -> Nat := matchedStage (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state) 0; 42".as_slice(),
        b"#eval matchedStage (fun n => let saved := Nat.add 10 n; fun state => Nat.add saved state) 0 5".as_slice(),
    ] {
        assert!(matches!(
            engine.execute_source_definitions(&[source], &KVMap::new(), bounded).unwrap(),
            Outcome::Inconclusive(stop)
                if matches!(
                    stop.cause,
                    fln_core::outcome::InconclusiveCause::ResourceExhausted { ref usage }
                        if usage.reason == fln_core::diag::ResourceReason::ExecutionSteps
                            && usage.allowed == 500
                            && usage.observed == 501
                )
        ));
        assert_eq!(engine.logical_root(&KVMap::new()), original);
    }
    returned(&engine, b"#eval 42", &["42"]);
}
