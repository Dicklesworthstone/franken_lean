//! Record fields may expose anonymous callbacks only during runtime preparation.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits, KVMap,
    Outcome, VmExit,
};

fn evaluate(source: &str, expected: &str) -> u64 {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let engine = Engine::with_coercion_seed(EngineAdmissionLimits::new(budget))
        .unwrap()
        .into_complete()
        .unwrap();
    let run = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(budget),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("native execution did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
    value.usage.steps
}

#[test]
fn anonymous_record_callback_passes_to_a_generic_consumer() {
    evaluate(
        r#"
structure Callable where
  run : Nat -> Nat
def twice {A : Type} (f : A -> A) (x : A) : A := f (f x)
def boxed : Callable := Callable.mk (fun n => n + 3)
#eval twice boxed.run 36
"#,
        "42",
    );
}

#[test]
fn coe_fun_exposes_the_anonymous_record_callback() {
    evaluate(
        r#"
structure Callable where
  run : Nat -> Nat
instance callable : CoeFun Callable (fun _ => Nat -> Nat) := CoeFun.mk (fun c => c.run)
def twice {A : Type} (f : A -> A) (x : A) : A := f (f x)
def boxed : Callable := Callable.mk (fun n => n + 3)
#eval twice boxed 36
"#,
        "42",
    );
}

#[test]
fn local_consumers_keep_the_projection_callback_annotation() {
    evaluate(
        r#"
structure Callable where
  run : Nat -> Nat
def boxed : Callable := Callable.mk (fun n => n + 3)
def pass (use : (Nat -> Nat) -> Nat) : Nat := use boxed.run
#eval pass (fun f => f 39)
"#,
        "42",
    );
}

#[test]
fn nested_records_and_distinct_callback_signatures_keep_their_types() {
    evaluate(
        r#"
structure Callable where
  run : Nat -> Nat
structure Outer where
  callable : Callable
structure Text where
  measure : String -> Nat
def nested : Outer := { callable := { run := fun n => n + 3 } }
def text : Text := { measure := fun s => String.length s }
def combine (number : Nat -> Nat) (measure : String -> Nat) : Nat := number 36 + measure "abc"
#eval combine nested.callable.run text.measure
"#,
        "42",
    );
}

#[test]
fn dynamic_field_callbacks_keep_owned_captures_and_their_receiver() {
    evaluate(
        r#"
structure Text where
  run : String -> Nat
def make (pfx : String) : Text := { run := fun s => String.length (pfx ++ s) }
def twice (f : String -> Nat) : Nat := f "abc" + f "abcd"
def use (pfx : String) : Nat := twice (make pfx).run
#eval use "hello"
"#,
        "17",
    );
}

#[test]
fn projection_annotation_keeps_strict_sibling_and_argument_work() {
    let definitions = r#"
structure Callable where
  run : Nat -> Nat
  ignored : Nat
def work (n : Nat) : Nat := n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n
def make (n : Nat) : Callable := { run := fun x => x + 2, ignored := n }
def use (f : Nat -> Nat) : Nat := f 40 + f 40
def ignore (n : Nat) (f : Nat -> Nat) : Nat := f 40
def boxed : Callable := { run := fun x => x + 2, ignored := 0 }
"#;
    let idle = evaluate(&format!("{definitions}#eval use (make 0).run"), "84");
    let busy = evaluate(&format!("{definitions}#eval use (make (work 0)).run"), "84");
    let twice = evaluate(
        &format!("{definitions}#eval (make (work 0)).run 40 + (make (work 0)).run 40"),
        "84",
    );
    assert!(busy > idle + 30, "unselected sibling work was erased");
    assert!(
        twice > busy + 30,
        "the receiver was evaluated more than once"
    );
    let idle = evaluate(&format!("{definitions}#eval ignore 0 boxed.run"), "42");
    let busy = evaluate(
        &format!("{definitions}#eval ignore (work 0) boxed.run"),
        "42",
    );
    assert!(busy > idle + 30, "an earlier strict argument was erased");
}

#[test]
fn projection_callback_resources_are_typed_and_retries_are_deterministic() {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let base = Engine::with_coercion_seed(EngineAdmissionLimits::new(budget))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = br#"
structure Callable where
  run : Nat -> Nat
def twice {A : Type} (f : A -> A) (x : A) : A := f (f x)
def boxed : Callable := Callable.mk (fun n => n + 3)
#eval twice boxed.run 36
"#;
    let mut small = EngineExecutionLimits::new(budget);
    small.ingress.max_lambda_bindings = 0;
    let mut error = base
        .execute_source_definitions(&[source], &options, small)
        .unwrap_err();
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    assert!(
        matches!(
            error,
            EngineExecutionError::Ingress(fln_comp::ingress::IngressError::ResourceLimit { .. })
        ),
        "{error:?}"
    );
    small = EngineExecutionLimits::new(budget);
    small.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source], &options, small)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let first = base
        .execute_source_definitions(&[source], &options, EngineExecutionLimits::new(budget))
        .unwrap()
        .into_complete()
        .unwrap();
    let second = base
        .execute_source_definitions(&[source], &options, EngineExecutionLimits::new(budget))
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(
        first.engine.logical_root(&options),
        second.engine.logical_root(&options)
    );
    let VmExit::Returned(value) = &second.executions.last().unwrap().exit else {
        panic!("return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn parameterized_records_preserve_the_selected_callback_type() {
    evaluate(
        r#"
structure Callback (A : Type) where
  run : A -> A
def twice {A : Type} (f : A -> A) (x : A) : A := f (f x)
def boxed : Callback Nat := { run := fun n => n + 3 }
#eval twice boxed.run 36
"#,
        "42",
    );
}
