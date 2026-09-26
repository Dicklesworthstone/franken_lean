//! Concrete templates with more than one closure-producing return stage.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn execute(source: &str, expected: &str) {
    let run = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let execution = run.executions.last().unwrap();
    let VmExit::Returned(value) = &execution.exit else {
        panic!("execution did not return");
    };
    assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
    let replay = fln::execute_flbc_artifact(
        &execution.flbc_artifact,
        &KVMap::new(),
        Default::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let VmExit::Returned(value) = replay else {
        panic!("replay did not return");
    };
    assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
}

const PIPELINE: &str = r#"
def pipeline {A : Type} (initial : A) : (A -> A) -> (A -> A) -> A :=
  let saved : A := initial;
  fun (first : A -> A) =>
    let intermediate : A := first saved;
    fun (second : A -> A) => second intermediate
"#;

#[test]
fn successive_callback_stages_keep_concrete_types_owned_values_and_captures() {
    execute(
        &format!("{PIPELINE}\n#eval pipeline 20 (fun (n : Nat) => n + 1) (fun (n : Nat) => n + n)"),
        "42",
    );
    execute(
        &format!("{PIPELINE}\ndef run (suffix : String) : Nat := String.length (pipeline \"a\" (fun s => s ++ suffix) (fun s => s ++ s))\n#eval run \"bc\""),
        "6",
    );
}

#[test]
fn flat_returned_callbacks_underapply_through_their_existing_suffix_interfaces() {
    execute(
        "def make {A : Type} (saved : A) : Nat -> Nat -> A := let value : A := saved; fun (a b : Nat) => value\n#eval make 42 1 2",
        "42",
    );
}

#[test]
fn unused_intermediate_result_does_not_delay_the_call_that_computed_it() {
    let source = |n| format!(
        "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n{PIPELINE}\n#eval let result : (Nat -> Nat) -> Nat := pipeline {n} spend; 42"
    );
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut bounded = limits();
    bounded.vm.max_steps = 2000;
    bounded.vm.max_stack_depth = 128;
    let expensive = source(100000);
    assert!(matches!(
        base.execute_source_definitions(&[expensive.as_bytes()], &options, bounded)
            .unwrap(),
        fln::Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    execute(&source(0), "42");
}

#[test]
fn invalid_later_callbacks_and_resource_stops_leave_the_engine_reusable() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!("{PIPELINE}\n#eval pipeline 20 (fun n => n + 1) (fun n => n + n)");
    let invalid = format!("{PIPELINE}\n#eval pipeline 20 (fun n => n + 1) (fun (b : Bool) => 42)");
    assert!(
        base.execute_source_definitions(&[invalid.as_bytes()], &options, limits())
            .is_err()
    );
    let mut bounded = limits();
    bounded.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
            .is_err()
    );
    let run = || {
        base.execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    assert_eq!(
        run().executions.last().unwrap().flbc_artifact,
        run().executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}
