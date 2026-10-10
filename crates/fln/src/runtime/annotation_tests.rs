//! Checked callable domains distinguish static motives from runtime callbacks.
//! The open catalog fixture reproduces the annotation/type-let rewrite cycle;
//! source execution separately verifies that real callbacks remain strict.

use super::*;

const STACK: usize = 2 * 1024 * 1024;

fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn pi(domain: Expr, result: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, result, BinderInfo::Default)
}

fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn app(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn engine() -> Engine {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK));
    Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[br#"
universe u
def annotationMotive (x : Nat) (motive : (fuel : Nat) -> x = fuel -> Sort u)
    (fuel : Nat) (h : x = fuel) (handler : (fuel : Nat) -> x = fuel -> Nat) : Nat :=
  handler fuel h
def annotationDependent (D : Sort u) (value : D) : Nat := 42
def annotationRuntimeDomain (choose : Bool)
    (motive : (if choose then Nat else String) -> Sort u) (value : Nat) : Nat := value
def annotationConsumer (first : Nat) (callback : Nat -> Nat) (last : Nat) : Nat :=
  callback (first + last)
"#],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn motive_type() -> Expr {
    pi(c("Nat"), pi(c("Bool"), Expr::sort(Level::one())))
}

fn motive() -> Expr {
    lam(c("Nat"), lam(c("Bool"), c("Nat")))
}

fn canonical_motive(preparation: &mut Preparation<'_>) -> Expr {
    // Universe-only specialization happens while the later motive is still
    // supplied by an open source let. The original logical domain mentions
    // the preceding runtime x in a proof; callable erasure turns it into Bool.
    let original = Expr::const_(name("annotationMotive"), vec![Level::one()]);
    let canonical = preparation
        .specialize_call(&original, &[])
        .unwrap()
        .unwrap();
    let ExprNode::Const { name, levels } = canonical.node() else {
        panic!("the ground specialization must have a canonical name");
    };
    assert!(levels.is_empty());
    let definition = preparation.specialized_definition(name).unwrap();
    let ExprNode::ForallE { body, .. } = definition.base.type_.node() else {
        panic!("the preceding runtime parameter must remain");
    };
    let ExprNode::ForallE { binder_type, .. } = body.node() else {
        panic!("the later static motive must remain in the logical signature");
    };
    assert!(binder_type.has_loose_bvars());
    canonical
}

fn cycle_input(head: Expr) -> (Expr, Expr) {
    // Outer slots, innermost first: handler, h, fuel, x. Replacing the static
    // motive binding must preserve all four slots and its actual callback.
    let expected = app(head.clone(), [b(3), motive(), b(2), b(1), b(0)]);
    let input = Expr::let_e(
        name("motive"),
        motive_type(),
        motive(),
        app(head, [b(4), b(0), b(3), b(2), b(1)]),
        false,
    );
    assert!(input.has_loose_bvars());
    (input, expected)
}

#[test]
fn a_static_motive_alone_does_not_request_a_runtime_callback_annotation() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let head = canonical_motive(&mut preparation);
    let arguments = [b(3), motive(), b(2), b(1), b(0)];
    assert!(
        preparation
            .has_literal_callable_tail(&arguments[1])
            .unwrap()
    );
    assert!(
        preparation
            .annotate_call(&head, &arguments)
            .unwrap()
            .is_none(),
        "a Sort-valued function must not recreate the let that static erasure removes"
    );
    assert!(preparation.lambdas.is_empty());
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn annotation_uses_real_preceding_arguments_to_classify_dependent_domains() {
    let engine = engine();
    for (universe, domain, value, needs_annotation) in [
        (
            Level::one(),
            pi(c("Nat"), c("Nat")),
            lam(c("Nat"), b(0)),
            true,
        ),
        (
            Level::succ(Level::one()).unwrap(),
            pi(c("Nat"), Expr::sort(Level::one())),
            lam(c("Nat"), c("Nat")),
            false,
        ),
    ] {
        let head = Expr::const_(name("annotationDependent"), vec![universe]);
        let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
        let annotated = preparation
            .annotate_call(&head, &[domain.clone(), value.clone()])
            .unwrap();
        assert_eq!(annotated.is_some(), needs_annotation);
        if let Some(annotated) = annotated {
            let ExprNode::LetE {
                value: first, body, ..
            } = annotated.node()
            else {
                panic!("the leading type argument retains its source position");
            };
            assert_eq!(first, &domain);
            let ExprNode::LetE {
                type_,
                value: second,
                ..
            } = body.node()
            else {
                panic!("the actual callback needs a checked runtime domain");
            };
            assert_eq!(type_, &domain);
            assert_eq!(second, &value);
        }
    }
}

#[test]
fn late_static_motives_no_longer_cycle_in_open_canonical_catalog_bodies() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let bounded = IngressLimits {
        max_nodes: 30_000,
        ..IngressLimits::default()
    };
    let mut preparation = Preparation::new(&engine.environment, bounded);
    let head = canonical_motive(&mut preparation);
    let (input, _) = cycle_input(head.clone());
    let expected = preparation.expression(&input).unwrap();
    let (selected, arguments) = preparation.spine(&expected).unwrap();
    assert_ne!(
        selected, head,
        "the newly concrete static motive must be specialized away"
    );
    assert_eq!(arguments, [b(3), b(2), b(1), b(0)]);
    let ExprNode::Const { name, levels } = selected.node() else {
        panic!("the late specialization must still use an ordinary catalog function");
    };
    assert!(levels.is_empty());
    let derived = preparation.specialized_definition(name).unwrap();
    let mut type_ = &derived.base.type_;
    let mut arity = 0;
    while let ExprNode::ForallE { body, .. } = type_.node() {
        arity += 1;
        type_ = body;
    }
    assert_eq!(
        arity, 4,
        "only the static parameter disappears from the logical telescope"
    );
    assert_eq!(type_, &c("Nat"));
    assert!(
        preparation.lambdas.is_empty(),
        "no runtime interface belongs to the motive"
    );
    // Measure exactly the same complete operation again: the inspection above
    // is deliberately excluded from the runtime preparation budget boundary.
    let mut measured = Preparation::new(&engine.environment, bounded);
    let head = canonical_motive(&mut measured);
    assert_eq!(measured.expression(&cycle_input(head).0).unwrap(), expected);
    let boundary = measured.visited - 1;

    let mut limited = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: boundary,
            ..IngressLimits::default()
        },
    );
    let head = canonical_motive(&mut limited);
    assert!(matches!(
        limited.expression(&cycle_input(head).0),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        }) if limit == boundary && observed == boundary + 1
    ));
    let mut retry = Preparation::new(&engine.environment, bounded);
    let head = canonical_motive(&mut retry);
    assert_eq!(retry.expression(&cycle_input(head).0).unwrap(), expected);
    assert_eq!(retry.visited, measured.visited);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn late_specialization_refuses_runtime_selected_carriers_and_open_type_values() {
    let engine = engine();
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let original = Expr::const_(name("annotationRuntimeDomain"), vec![Level::one()]);
    let head = preparation
        .specialize_call(&original, &[])
        .unwrap()
        .unwrap();
    // This particular call is well typed: when choose=false the motive takes
    // String. But choose remains a runtime argument and cannot choose a global
    // cached type specialization whose key deliberately excludes its value.
    assert!(matches!(
        preparation.specialize_call(
            &head,
            &[
                c("Bool.false"),
                lam(c("String"), c("Nat")),
                nat::literal(42)
            ]
        ),
        Ok(None) | Err(IngressError::UnsupportedNode { .. })
    ));

    let head = canonical_motive(&mut preparation);
    // A surrounding abstract carrier remains open even after the proof-only
    // dependencies of the formal motive have been erased.
    let open = lam(c("Nat"), lam(c("Bool"), b(6)));
    assert!(open.has_loose_bvars());
    assert!(
        preparation
            .specialize_call(&head, &[b(3), open, b(2), b(1), b(0)])
            .unwrap()
            .is_none()
    );
}

#[test]
fn runtime_callbacks_keep_ordered_strict_bindings_and_open_captures() {
    let engine = engine();
    let head = c("annotationConsumer");
    let arguments = [
        app(c("Nat.add"), [b(1), nat::literal(1)]),
        lam(c("Nat"), b(1)),
        app(c("Nat.add"), [b(0), nat::literal(2)]),
    ];
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let annotated = preparation
        .annotate_call(&head, &arguments)
        .unwrap()
        .unwrap();
    let mut body = &annotated;
    for (index, argument) in arguments.iter().enumerate() {
        let ExprNode::LetE {
            type_,
            value,
            body: next,
            ..
        } = body.node()
        else {
            panic!("every original argument must retain one strict binding in order");
        };
        if index == 1 {
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = type_.node()
            else {
                panic!("the callback must retain its checked Nat -> Nat telescope");
            };
            // The parser supplies a hygienic binder name. Its spelling is not
            // part of this nondependent callable's runtime representation.
            assert_eq!(binder_type, &c("Nat"));
            assert_eq!(body, &c("Nat"));
            assert_eq!(*binder_info, BinderInfo::Default);
        } else {
            assert_eq!(type_, &c("Nat"));
        }
        assert_eq!(value, &argument.lift_loose(0, index as u32).unwrap());
        body = next;
    }
    assert_eq!(body, &app(head, [b(2), b(1), b(0)]));
}

#[test]
fn checked_motive_calls_keep_runtime_callback_work_and_replay_their_bytecode() {
    let engine = engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
    let source = |cost| {
        format!(
            "def annotationSpend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => annotationSpend k + 1\n\
         #eval annotationMotive (annotationSpend {cost}) (fun _ _ => Nat) (annotationSpend {cost}) rfl (let paid := annotationSpend {cost}; fun _ _ => 42)"
        )
    };
    let execute = |cost| {
        let source = source(cost);
        let result = engine
            .execute_source_definitions(&[source.as_bytes()], &options, limits)
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
        let execution = result.executions.last().unwrap();
        let VmExit::Returned(returned) = &execution.exit else {
            panic!("the checked callback must run natively");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
            Some("42")
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
            panic!("the canonical artifact must run the same callback");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&replay.value).as_deref(),
            Some("42")
        );
        assert_eq!(replay.usage, returned.usage);
        returned.usage.steps
    };
    let idle = execute(0);
    let busy = execute(30);
    assert!(
        busy > idle + 30,
        "unused runtime argument work was dropped: {idle} vs {busy}"
    );
    let mut bounded = limits;
    bounded.vm.max_steps = idle;
    let source = source(30);
    let stopped = engine
        .execute_source_definitions(&[source.as_bytes()], &options, bounded)
        .unwrap();
    assert!(matches!(
        stopped,
        Outcome::Inconclusive(stop)
            if matches!(&stop.cause,
                fln_core::outcome::InconclusiveCause::ResourceExhausted { usage }
                    if usage.reason == fln_core::diag::ResourceReason::ExecutionSteps
                        && usage.allowed == idle && usage.observed == idle + 1)
    ));
    assert_eq!(engine.logical_root(&options), root);
}
