//! A checked composition can compute a staged callback before a consumer uses it.
use crate::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits,
    IngressError, IngressLimits, KVMap, Outcome, SourceCheckLimits, VmExit,
};

const DECLARATIONS: &str = r#"
def callbackCompose (pure : Nat -> Nat -> Nat) (f : Nat -> Nat) (value : Nat) : Nat -> Nat :=
  pure (f value)
def callbackBind (action : Nat -> Nat) (next : Nat -> Nat -> Nat) (world : Nat) : Nat :=
  next (action world) world
def callbackPure (value world : Nat) : Nat := value + world
def callbackMap (value : Nat) : Nat := value + 1
def callbackGenericCompose {A B C : Type} (pure : B -> C) (f : A -> B) (value : A) : C :=
  pure (f value)
"#;

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn checked(source: &str) -> Engine {
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .expect("the composition and consumer pass both ordinary checkers")
        .engine
}

#[test]
fn computed_composition_callback_reaches_its_consumer_with_real_stages() {
    let engine = checked(DECLARATIONS);
    // The producer's remaining `(value : Nat)` binder and the consumer's
    // anonymous arrow are the same logical type despite different labels.
    let constant = |label: &str| crate::Expr::const_(super::name(label), Vec::new());
    let producer = crate::Expr::app(
        crate::Expr::app(constant("callbackCompose"), constant("callbackPure")),
        constant("callbackMap"),
    );
    let action = crate::Expr::lam(
        crate::Name::anonymous(),
        constant("Nat"),
        crate::Expr::bvar(0).unwrap(),
        crate::BinderInfo::Default,
    );
    assert!(
        super::Preparation::new(engine.environment(), limits().ingress)
            .specialize_computed_callback(
                &constant("callbackBind"),
                &[action, producer, super::nat::literal(3)],
            )
            .unwrap()
            .is_some(),
        "checked binder spelling does not hide the computed callback",
    );
    for source in [
        "#eval callbackBind (fun (world : Nat) => world + 5) (callbackCompose callbackPure callbackMap) 3",
        "#eval callbackBind (fun (world : Nat) => world + 5) (@callbackGenericCompose Nat Nat (Nat -> Nat) callbackPure callbackMap) 3",
    ] {
        assert_nat(&engine, source, "12");
    }
}

#[test]
fn a_computed_producer_is_shared_but_its_first_callback_stage_is_strict() {
    let engine = checked(&format!(
        r#"{DECLARATIONS}
def callbackSpend (n : Nat) : Nat :=
  match n with | .zero => 0 | .succ k => callbackSpend k + 1
def callbackReuse (next : Nat -> Nat -> Nat) : Nat :=
  next 3 5 + next 4 5
def callbackFirstOnly (next : Nat -> Nat -> Nat) : Nat :=
  let ignored : Nat -> Nat := next 3
  0
"#,
    ));
    let reference_idle = assert_nat(&engine, "#eval callbackSpend 0", "0");
    let reference_busy = assert_nat(&engine, "#eval callbackSpend 25", "25");
    let once = reference_busy.checked_sub(reference_idle).unwrap();
    assert!(once > 25, "the witness performs real recursive work");

    let shared = |cost| {
        format!(
            "#eval callbackReuse (let paid := callbackSpend {cost}; callbackCompose callbackPure (fun (value : Nat) => value + paid))"
        )
    };
    let idle = assert_nat(&engine, &shared(0), "17");
    let busy = assert_nat(&engine, &shared(25), "67");
    assert_eq!(
        busy.checked_sub(idle).unwrap(),
        once,
        "two callback uses must share the computed producer's strict initializer",
    );

    let first_only = |cost| {
        format!(
            "#eval callbackFirstOnly (callbackCompose callbackPure (fun (value : Nat) => callbackSpend {cost} + value))"
        )
    };
    let idle = assert_nat(&engine, &first_only(0), "0");
    let busy = assert_nat(&engine, &first_only(25), "0");
    assert_eq!(
        busy.checked_sub(idle).unwrap(),
        once,
        "discarding the returned world-stage closure cannot defer or erase the first stage",
    );
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let mut bounded = limits();
    bounded.vm.max_steps = idle;
    assert!(matches!(
        engine
            .execute_source_commands_with_checks(first_only(25).as_bytes(), &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn computed_callbacks_retain_owned_unicode_captures_through_replay() {
    let engine = checked(
        r#"
def ownedCompose (pure : String -> Nat -> String) (f : String -> String)
    (value : String) : Nat -> String := pure (f value)
def ownedBind (action : Nat -> String) (next : String -> Nat -> String)
    (world : Nat) : String := next (action world) world
def ownedPure (value : String) (world : Nat) : String := value ++ "!"
def ownedRun (suffix : String) : String :=
  ownedBind (fun (world : Nat) => "λ")
    (ownedCompose ownedPure (fun (value : String) => value ++ suffix)) 3
"#,
    );
    let execution = execute(&engine, "#eval ownedRun \"🙂\"");
    for exit in [&execution.exit, &replay(&execution)] {
        assert_eq!(
            crate::closed_vm_value(exit).unwrap(),
            Some(crate::ClosedVmValue::String("λ🙂!".to_owned())),
            "the retained producer and its returned stage own their String captures",
        );
    }
}

#[test]
fn computed_callback_selection_preserves_authority_dynamic_and_resource_boundaries() {
    let engine = checked(DECLARATIONS);
    let options = KVMap::new();
    let query = "#eval callbackBind (fun (world : Nat) => world + 5) (callbackCompose callbackPure callbackMap) 3";
    for target in ["callbackBind", "callbackCompose"] {
        let decorated = Engine::from_environment(
            fln_elab::externs::register(
                engine.environment(),
                &super::name(target),
                vec![fln_elab::externs::ExternEntry::Standard {
                    backend: super::name("all"),
                    symbol: "foreign_computed_callback".to_owned(),
                }],
            )
            .unwrap(),
        );
        let root = decorated.logical_root(&options);
        let mut error = decorated
            .execute_source_commands_with_checks(query.as_bytes(), &options, limits())
            .unwrap_err();
        while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
            error = *inner;
        }
        assert!(
            matches!(
                error,
                EngineExecutionError::Ingress(IngressError::UnsupportedNode {
                    kind: "native extern attribute does not match the supported ABI"
                })
            ),
            "selected {target} metadata must not disappear during specialization: {error:?}",
        );
        assert_eq!(decorated.logical_root(&options), root);
    }

    let constant = |label: &str| crate::Expr::const_(super::name(label), Vec::new());
    let producer = crate::Expr::app(
        crate::Expr::app(constant("callbackCompose"), constant("callbackPure")),
        constant("callbackMap"),
    );
    let arguments = [constant("callbackMap"), producer, super::nat::literal(3)];
    assert!(
        super::Preparation::new(engine.environment(), limits().ingress)
            .specialize_computed_callback(&crate::Expr::bvar(0).unwrap(), &arguments)
            .unwrap()
            .is_none(),
        "a dynamic consumer has no checked body to specialize",
    );
    let dynamic = [
        constant("callbackMap"),
        crate::Expr::app(crate::Expr::bvar(0).unwrap(), super::nat::literal(0)),
        super::nat::literal(3),
    ];
    assert!(
        super::Preparation::new(engine.environment(), limits().ingress)
            .specialize_computed_callback(&constant("callbackBind"), &dynamic)
            .unwrap()
            .is_none(),
        "an unknown computed factory cannot supply guessed stage metadata",
    );
    for ingress in [
        IngressLimits {
            max_nodes: 0,
            ..limits().ingress
        },
        IngressLimits {
            max_application_args: 2,
            ..limits().ingress
        },
        IngressLimits {
            max_context_depth: 1,
            ..limits().ingress
        },
    ] {
        assert!(matches!(
            super::Preparation::new(engine.environment(), ingress)
                .specialize_computed_callback(&constant("callbackBind"), &arguments),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
}

fn execute(engine: &Engine, source: &str) -> crate::DefinitionExecution {
    let result = engine
        .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("a computed composition retains its staged callback interface");
    result.batch.executions.into_iter().next().unwrap()
}

fn replay(execution: &crate::DefinitionExecution) -> VmExit {
    let program =
        fln_comp::flbc::decode_canonical(&execution.flbc_artifact, limits().flbc_codec).unwrap();
    assert_eq!(
        fln_comp::flbc::encode_canonical(&program, limits().flbc_codec).unwrap(),
        execution.flbc_artifact,
    );
    crate::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn assert_nat(engine: &Engine, source: &str, expected: &str) -> u64 {
    let execution = execute(engine, source);
    let VmExit::Returned(value) = &execution.exit else {
        panic!("the callback returns its checked result");
    };
    let steps = value.usage.steps;
    assert_eq!(crate::nat_decimal(&value.value).as_deref(), Some(expected));
    let VmExit::Returned(value) = replay(&execution) else {
        panic!("the preserved callback interface replays");
    };
    assert_eq!(crate::nat_decimal(&value.value).as_deref(), Some(expected));
    steps
}
