//! Structural producer controls; source tests separately exercise admission.
use super::*;
use fln_env::constants::{ConstantVal, ReducibilityHints};

fn nat() -> Expr {
    Expr::const_(name("Nat"), vec![])
}
fn b(index: usize) -> Expr {
    variable(index).unwrap()
}
fn pi(domain: Expr, result: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, result, BinderInfo::Default)
}
fn lam(label: &str, domain: Expr, body: Expr) -> Expr {
    Expr::lam(name(label), domain, body, BinderInfo::Default)
}
fn call(label: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter()
        .fold(Expr::const_(name(label), vec![]), Expr::app)
}
fn local(label: &str, value: Expr, body: Expr) -> Expr {
    Expr::let_e(name(label), nat(), value, body, false)
}
fn callback_type() -> Expr {
    pi(nat(), pi(nat(), nat()))
}
fn staged() -> Expr {
    lam(
        "x",
        nat(),
        local("paid", call("observe", [b(0)]), lam("y", nat(), b(1))),
    )
}
fn definition(safety: DefinitionSafety) -> DefinitionVal {
    DefinitionVal {
        base: ConstantVal {
            name: name("consume"),
            level_params: Vec::new(),
            type_: pi(nat(), pi(callback_type(), pi(nat(), nat()))),
        },
        value: lam(
            "first",
            nat(),
            lam(
                "callback",
                callback_type(),
                lam("last", nat(), Expr::app(Expr::app(b(1), b(2)), b(0))),
            ),
        ),
        hints: ReducibilityHints::Abbrev,
        safety,
        all: Vec::new(),
    }
}
fn environment(safety: DefinitionSafety) -> Environment {
    Environment::new()
        .add_decl(ConstantInfo::Defn(definition(safety)))
        .unwrap()
}
fn occurrences(input: &Expr, label: &str) -> usize {
    let mut work = vec![input.clone()];
    let mut found = 0;
    while let Some(expr) = work.pop() {
        match expr.node() {
            ExprNode::Const { name: n, .. } => found += usize::from(n == &name(label)),
            ExprNode::App { f, a } => {
                work.push(f.clone());
                work.push(a.clone());
            }
            ExprNode::Lam { body, .. } | ExprNode::MData { expr: body, .. } => {
                work.push(body.clone());
            }
            ExprNode::LetE { value, body, .. } => {
                work.push(value.clone());
                work.push(body.clone());
            }
            _ => {}
        }
    }
    found
}

#[test]
fn flat_literal_callbacks_keep_the_existing_catalog_path() {
    let environment = environment(DefinitionSafety::Safe);
    let flat = lam("x", nat(), lam("y", nat(), b(0)));
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .specialize_staged_callback(
                &call("consume", []),
                &[nat::literal(0), flat, nat::literal(1)]
            )
            .unwrap()
            .is_none()
    );
}

#[test]
fn specialization_keeps_ordered_runtime_arguments_and_the_literal_stage_boundary() {
    let environment = environment(DefinitionSafety::Safe);
    let callback = staged();
    let actual = Preparation::new(&environment, IngressLimits::default())
        .specialize_staged_callback(
            &call("consume", []),
            &[
                call("firstArgument", []),
                callback.clone(),
                call("lastArgument", []),
            ],
        )
        .unwrap()
        .unwrap();
    let expected = local(
        "first",
        call("firstArgument", []),
        local(
            "last",
            call("lastArgument", []),
            Expr::app(
                Expr::app(
                    Expr::let_e(Name::anonymous(), callback_type(), callback, b(0), false),
                    b(1),
                ),
                b(0),
            ),
        ),
    );
    assert_eq!(actual, expected);
    assert_eq!(occurrences(&actual, "observe"), 1);
    assert_eq!(occurrences(&actual, "consume"), 0);
}

#[test]
fn open_callback_captures_are_lifted_across_retained_arguments_without_capture() {
    let environment = environment(DefinitionSafety::Safe);
    let callback = lam("x", nat(), local("paid", b(1), lam("y", nat(), b(1))));
    let actual = Preparation::new(&environment, IngressLimits::default())
        .specialize_staged_callback(&call("consume", []), &[b(0), callback.clone(), b(1)])
        .unwrap()
        .unwrap();
    let expected = local(
        "first",
        b(0),
        local(
            "last",
            b(2),
            Expr::app(
                Expr::app(
                    Expr::let_e(
                        Name::anonymous(),
                        callback_type(),
                        callback.lift_loose(0, 2).unwrap(),
                        b(0),
                        false,
                    ),
                    b(1),
                ),
                b(0),
            ),
        ),
    );
    assert_eq!(actual, expected);
}

#[test]
fn partial_consumers_return_a_typed_real_lambda_not_a_flat_interface_cast() {
    let environment = environment(DefinitionSafety::Safe);
    let actual = Preparation::new(&environment, IngressLimits::default())
        .specialize_staged_callback(&call("consume", []), &[nat::literal(9), staged()])
        .unwrap()
        .unwrap();
    let ExprNode::LetE { value, body, .. } = actual.node() else {
        panic!("strict prefix");
    };
    assert_eq!(value, &nat::literal(9));
    let ExprNode::LetE {
        type_, value, body, ..
    } = body.node()
    else {
        panic!("callback annotation");
    };
    assert_eq!(type_, &pi(nat(), nat()));
    assert!(matches!(value.node(), ExprNode::Lam { .. }));
    assert_eq!(body, &b(0));
    assert!(!actual.has_loose_bvars());
}

#[test]
fn computed_callback_operands_are_never_treated_as_literal_values() {
    let environment = environment(DefinitionSafety::Safe);
    let operand = Expr::let_e(
        name("paid"),
        nat(),
        call("observableInitializer", []),
        staged(),
        false,
    );
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .specialize_staged_callback(
                &call("consume", []),
                &[nat::literal(0), operand, nat::literal(1)]
            )
            .unwrap()
            .is_none()
    );
}

#[test]
fn specialization_never_crosses_a_strict_callee_stage_to_find_a_callback() {
    let mut declaration = definition(DefinitionSafety::Safe);
    let ExprNode::Lam { body, .. } = declaration.value.node() else {
        panic!("first binder");
    };
    declaration.value = lam(
        "first",
        nat(),
        local(
            "required",
            call("observe", [b(0)]),
            body.lift_loose(0, 1).unwrap(),
        ),
    );
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(declaration))
        .unwrap();
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .specialize_staged_callback(
                &call("consume", []),
                &[nat::literal(0), staged(), nat::literal(1)]
            )
            .unwrap()
            .is_none()
    );
}

#[test]
fn unsafe_definitions_and_universe_arity_errors_cannot_supply_callback_code() {
    for safety in [DefinitionSafety::Unsafe, DefinitionSafety::Partial] {
        let environment = environment(safety);
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .specialize_staged_callback(&call("consume", []), &[nat::literal(0), staged()])
                .unwrap()
                .is_none()
        );
    }
    let environment = environment(DefinitionSafety::Safe);
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .specialize_staged_callback(
                &Expr::const_(name("consume"), vec![Level::one()]),
                &[nat::literal(0), staged()]
            )
            .unwrap()
            .is_none()
    );
    assert!(
        Preparation::new(&Environment::new(), IngressLimits::default())
            .specialize_staged_callback(&call("consume", []), &[staged()])
            .unwrap()
            .is_none()
    );
}

#[test]
fn specialization_obeys_work_argument_and_retained_context_limits() {
    let environment = environment(DefinitionSafety::Safe);
    for limits in [
        IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        },
        IngressLimits {
            max_application_args: 1,
            ..IngressLimits::default()
        },
        IngressLimits {
            max_context_depth: 1,
            ..IngressLimits::default()
        },
    ] {
        assert!(matches!(
            Preparation::new(&environment, limits).specialize_staged_callback(
                &call("consume", []),
                &[nat::literal(0), staged(), nat::literal(1)],
            ),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
}

fn annotated_alias(type_: Expr, value: Expr) -> Expr {
    Expr::let_e(
        Name::anonymous(),
        type_.clone(),
        value,
        Expr::let_e(Name::anonymous(), type_, b(0), b(0), false),
        false,
    )
}

#[test]
fn inert_aliases_preserve_checked_callback_stages_and_open_captures() {
    let environment = environment(DefinitionSafety::Safe);
    let callback = lam("x", nat(), local("paid", b(1), lam("y", nat(), b(1))));
    let annotated = annotated_alias(callback_type(), callback.clone());
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let expected = preparation
        .annotate_callable_tail(&callback, &callback_type())
        .unwrap();
    let recovered = preparation.inert_callable(&annotated).unwrap().unwrap();
    // Reapplying an annotation can retain another typed identity binding, but
    // the actual lambda and its strict first-stage initializer stay intact.
    let ExprNode::Lam { body, .. } = recovered.node() else {
        panic!("literal callback remains a lambda");
    };
    let ExprNode::LetE { value, .. } = body.node() else {
        panic!("strict first-stage initializer remains before the next lambda");
    };
    assert_eq!(value, &b(1));
    assert!(recovered.has_loose_bvars());
    assert!(
        preparation
            .staged_callback(&recovered, &callback_type())
            .unwrap()
    );
    assert!(
        preparation
            .staged_callback(&expected, &callback_type())
            .unwrap()
    );
}

#[test]
fn annotated_consumers_and_callbacks_expose_only_literal_code() {
    let environment = environment(DefinitionSafety::Safe);
    let declaration = definition(DefinitionSafety::Safe);
    let consumer = annotated_alias(declaration.base.type_, declaration.value.clone());
    let callback = annotated_alias(callback_type(), staged());
    let arguments = [
        call("firstArgument", []),
        callback,
        call("lastArgument", []),
    ];
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let exposed = preparation
        .static_apply(&consumer, &arguments)
        .unwrap()
        .unwrap();
    let (head, args) = preparation.spine(&exposed).unwrap();
    assert_eq!(head, declaration.value);
    assert_eq!(args, arguments);

    let specialized = preparation
        .specialize_staged_callback(&call("consume", []), &arguments)
        .unwrap()
        .unwrap();
    assert_eq!(occurrences(&specialized, "observe"), 1);
    assert_eq!(occurrences(&specialized, "firstArgument"), 1);
    assert_eq!(occurrences(&specialized, "lastArgument"), 1);
    let ExprNode::LetE { value, body, .. } = specialized.node() else {
        panic!("first strict operand");
    };
    assert_eq!(value, &call("firstArgument", []));
    let ExprNode::LetE { value, .. } = body.node() else {
        panic!("second strict operand");
    };
    assert_eq!(value, &call("lastArgument", []));
}

#[test]
fn inert_exposure_does_not_cross_computed_initializers_or_result_work() {
    let environment = environment(DefinitionSafety::Safe);
    for computed in [
        local("paid", call("observe", [nat::literal(0)]), staged()),
        Expr::let_e(
            Name::anonymous(),
            callback_type(),
            staged(),
            Expr::app(call("computeResult", []), b(0)),
            false,
        ),
        annotated_alias(callback_type(), call("computeCallback", [])),
        Expr::let_e(
            Name::anonymous(),
            callback_type(),
            staged(),
            local("paid", call("observe", [nat::literal(0)]), staged()),
            false,
        ),
    ] {
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        assert!(preparation.inert_callable(&computed).unwrap().is_none());
        let applied = preparation
            .static_apply(&computed, &[nat::literal(4)])
            .unwrap()
            .unwrap();
        let ExprNode::LetE { value: actual, .. } = applied.node() else {
            panic!("the strict callee binding must remain");
        };
        let ExprNode::LetE {
            value: original, ..
        } = computed.node()
        else {
            unreachable!();
        };
        assert_eq!(actual, original);
    }
}

#[test]
fn inert_exposure_obeys_work_and_context_limits() {
    let environment = environment(DefinitionSafety::Safe);
    let nested = annotated_alias(callback_type(), annotated_alias(callback_type(), staged()));
    for limits in [
        IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        },
        IngressLimits {
            max_context_depth: 1,
            ..IngressLimits::default()
        },
    ] {
        assert!(matches!(
            Preparation::new(&environment, limits).inert_callable(&nested),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
}

#[test]
fn known_consumer_binding_retains_two_strict_prefixes_and_outer_capture_scope() {
    let environment = environment(DefinitionSafety::Safe);
    let type_ = pi(callback_type(), nat());
    let literal = lam(
        "callback",
        callback_type(),
        Expr::app(Expr::app(b(0), b(2)), b(3)),
    );
    let initializer = local(
        "first",
        call("firstInitializer", [b(0)]),
        local("second", call("secondInitializer", [b(0)]), literal.clone()),
    );
    let body = Expr::app(b(0), b(1));
    let actual = Preparation::new(&environment, IngressLimits::default())
        .expose_callable_binding(&type_, &initializer, &body)
        .unwrap()
        .unwrap();
    let expected = local(
        "first",
        call("firstInitializer", [b(0)]),
        local(
            "second",
            call("secondInitializer", [b(0)]),
            Expr::app(literal, b(2)),
        ),
    );
    assert_eq!(actual, expected);
    assert_eq!(occurrences(&actual, "firstInitializer"), 1);
    assert_eq!(occurrences(&actual, "secondInitializer"), 1);
}

#[test]
fn applied_literal_prefix_is_bound_before_exposing_the_remaining_consumer() {
    let environment = environment(DefinitionSafety::Safe);
    let declaration = definition(DefinitionSafety::Safe);
    let initializer = Expr::app(declaration.value, call("firstInitializer", [b(0)]));
    let type_ = pi(callback_type(), pi(nat(), nat()));
    let actual = Preparation::new(&environment, IngressLimits::default())
        .expose_callable_binding(&type_, &initializer, &Expr::app(b(0), b(1)))
        .unwrap()
        .unwrap();
    let ExprNode::LetE { value, body, .. } = actual.node() else {
        panic!("supplied prefix remains strict");
    };
    assert_eq!(value, &call("firstInitializer", [b(0)]));
    assert_eq!(occurrences(&actual, "firstInitializer"), 1);
    let (head, arguments) = Preparation::new(&environment, IngressLimits::default())
        .spine(body)
        .unwrap();
    assert!(matches!(head.node(), ExprNode::Lam { .. }));
    assert_eq!(arguments, vec![b(1)]);
}

#[test]
fn consumer_values_and_mixed_uses_keep_their_outer_type_annotation() {
    let environment = environment(DefinitionSafety::Safe);
    let type_ = pi(pi(nat(), nat()), nat());
    let initializer = lam(
        "callback",
        pi(nat(), nat()),
        Expr::app(b(0), nat::literal(42)),
    );
    let direct = Expr::app(b(0), lam("value", nat(), b(0)));
    for body in [
        call("use", [b(0)]),
        Expr::app(b(1), b(0)),
        local("first", direct.clone(), Expr::app(b(2), b(1))),
    ] {
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .expose_callable_binding(&type_, &initializer, &body)
                .unwrap()
                .is_none()
        );
    }
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .expose_callable_binding(&type_, &initializer, &direct)
            .unwrap()
            .is_some()
    );
}

#[test]
fn callee_use_analysis_tracks_binders_and_retains_resource_limits() {
    let environment = environment(DefinitionSafety::Safe);
    let nested = lam(
        "argument",
        nat(),
        local("saved", b(0), Expr::app(b(2), b(0))),
    );
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .only_callee_uses(&nested)
            .unwrap()
    );
    assert!(
        !Preparation::new(&environment, IngressLimits::default())
            .only_callee_uses(&lam("unrelated", nat(), Expr::app(b(0), nat::literal(1))))
            .unwrap()
    );
    for limits in [
        IngressLimits {
            max_nodes: 0,
            ..IngressLimits::default()
        },
        IngressLimits {
            max_context_depth: 1,
            ..IngressLimits::default()
        },
    ] {
        assert!(matches!(
            Preparation::new(&environment, limits).only_callee_uses(&nested),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
}

#[test]
fn substituted_staged_values_keep_an_outer_signature_for_local_consumers() {
    let environment = environment(DefinitionSafety::Safe);
    let type_ = callback_type();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let exposed = preparation
        .expose_callable_binding(&type_, &staged(), &Expr::app(b(1), b(0)))
        .unwrap()
        .unwrap();
    let applied = preparation
        .static_apply(
            &lam("callback", type_.clone(), Expr::app(b(1), b(0))),
            &[staged()],
        )
        .unwrap()
        .unwrap();
    for expression in [exposed, applied] {
        let ExprNode::App { f, a } = expression.node() else {
            panic!("the dynamic consumer remains an application");
        };
        assert_eq!(f, &b(0));
        let ExprNode::LetE {
            type_, value, body, ..
        } = a.node()
        else {
            panic!("the staged value retains its outer checked type");
        };
        assert_eq!(type_, &callback_type());
        assert!(matches!(value.node(), ExprNode::Lam { .. }));
        assert_eq!(body, &b(0));
        assert!(preparation.inert_callable(a).unwrap().is_some());
        assert_eq!(occurrences(&expression, "observe"), 1);
    }
}

#[test]
fn known_consumer_sources_are_exposed_inside_typed_aliases_before_registration() {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[br#"
structure Consumer where
  run : (Nat -> Nat -> Nat) -> Nat
def consumer : Consumer := { run := fun callback => callback 20 21 }
def genericConsumer {A : Type} (callback : Nat -> Nat -> Nat) : Nat := callback 20 21
"#],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let type_ = pi(callback_type(), nat());
    for projection in [
        Expr::proj(name("Consumer"), 0, call("consumer", [])),
        call("Consumer.run", [call("consumer", [])]),
        call("genericConsumer", [nat()]),
    ] {
        let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
        let initializer = annotated_alias(type_.clone(), projection);
        let exposed = preparation
            .expose_callable_binding(&type_, &initializer, &Expr::app(b(0), staged()))
            .unwrap()
            .unwrap();
        let (head, arguments) = preparation.spine(&exposed).unwrap();
        assert!(matches!(head.node(), ExprNode::Lam { .. }));
        assert_eq!(arguments, vec![staged()]);
        assert!(
            preparation.lambdas.is_empty(),
            "projection exposure precedes registration"
        );
    }
}

#[test]
fn first_order_functions_result_anchors_and_unknown_producers_keep_their_bindings() {
    let environment = environment(DefinitionSafety::Safe);
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    assert!(
        preparation
            .expose_callable_binding(
                &pi(nat(), nat()),
                &lam("value", nat(), b(0)),
                &call("use", [b(0)])
            )
            .unwrap()
            .is_none()
    );
    assert!(
        preparation
            .expose_callable_binding(&callback_type(), &staged(), &b(0))
            .unwrap()
            .is_none()
    );
    assert!(
        preparation
            .expose_callable_binding(
                &pi(callback_type(), nat()),
                &call("unknownProducer", [b(0)]),
                &call("use", [b(0)])
            )
            .unwrap()
            .is_none()
    );
}
