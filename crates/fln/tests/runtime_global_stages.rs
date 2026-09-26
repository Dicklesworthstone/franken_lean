//! Real source admission, native closures, strict producers and FLBC replay.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Outcome, VmExit};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn execute(source: &str, expected: &str) -> u64 {
    let run = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let execution = run.executions.last().unwrap();
    let VmExit::Returned(value) = &execution.exit else {
        panic!("not returned");
    };
    assert_eq!(
        fln::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    let replay = fln::execute_flbc_artifact(
        &execution.flbc_artifact,
        &KVMap::new(),
        Default::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let VmExit::Returned(replayed) = replay else {
        panic!("replay did not return");
    };
    assert_eq!(fln::nat_decimal(&replayed.value).as_deref(), Some(expected));
    value.usage.steps
}

#[test]
fn global_overapplication_computes_the_returned_function_before_applying_it() {
    execute(
        "def make (n : Nat) : Nat -> Nat := let paid : Nat := n + 1; fun (x : Nat) => paid + x\n#eval make 20 21",
        "42",
    );
    execute(
        "def make (a b : Nat) : Nat -> Nat := let paid : Nat := a + b; fun (x : Nat) => paid + x\n#eval make 10 20 12",
        "42",
    );
}

#[test]
fn partial_global_stages_return_reusable_closures_with_runtime_captures() {
    execute(
        "def make (a b : Nat) : Nat -> Nat := let paid : Nat := a + b; fun (x : Nat) => paid + x\n#eval let first : Nat -> Nat -> Nat := make 10; let second : Nat -> Nat := first 20; second 5 + second 7",
        "72",
    );
    execute(
        "def make (a b : Nat) : Nat -> Nat := let paid : Nat := a + b; fun (x : Nat) => paid + x\ndef run (n : Nat) : Nat := let first : Nat -> Nat -> Nat := make n; let second : Nat -> Nat := first 20; second 12\n#eval run 10",
        "42",
    );
}

#[test]
fn returned_functions_keep_owned_strings_and_literal_callback_annotations() {
    execute(
        "def make (suffix : String) : String -> String := let shared : String := suffix ++ suffix; fun (s : String) => s ++ shared\n#eval String.length (make \"ab\" \"xy\")",
        "6",
    );
    execute(
        "def consumer (n : Nat) : (Nat -> Nat) -> Nat := let paid : Nat := n + 1; fun (f : Nat -> Nat) => f paid\n#eval consumer 40 (fun (x : Nat) => x + 1)",
        "42",
    );
}

#[test]
fn zero_argument_globals_can_compute_functions_instead_of_fabricating_lambdas() {
    execute(
        "def ready : Nat -> Nat := let paid : Nat := 40; fun (x : Nat) => paid + x\n#eval ready 2",
        "42",
    );
    execute(
        "def make (n : Nat) : Nat -> Nat := let paid : Nat := n + 1; fun (x : Nat) => paid + x\n#eval let f : Nat -> Nat -> Nat := make; let g : Nat -> Nat := f 20; g 21",
        "42",
    );
}

#[test]
fn interleaved_specialization_preserves_the_concrete_function_return_stage() {
    execute(
        "def make (ignored : Nat) {A : Type} (value : A) : Nat -> A := let saved : A := value; fun (n : Nat) => saved\n#eval make 1 42 9",
        "42",
    );
    execute(
        "def make (ignored : Nat) {A : Type} (value : A) : Nat -> A := let saved : A := value; fun (n : Nat) => saved\n#eval String.length (make 1 \"answer\" 9)",
        "6",
    );
}

const SPEND: &str = "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\ndef make (n : Nat) : Nat -> Nat := let paid : Nat := spend n; fun (x : Nat) => x\n";

#[test]
fn ignoring_a_returned_closure_does_not_skip_its_strict_producer() {
    let program = |n| format!("{SPEND}#eval let ignored : Nat -> Nat := make {n}; 42");
    let idle = execute(&program(0), "42");
    let busy = execute(&program(30), "42");
    assert!(busy > idle + 30, "producer was delayed: {idle} vs {busy}");
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut bounded = limits();
    bounded.vm.max_steps = 2000;
    bounded.vm.max_stack_depth = 128;
    let expensive = program(100000);
    assert!(matches!(
        base.execute_source_definitions(&[expensive.as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let cheap = program(0);
    let run = || {
        base.execute_source_definitions(&[cheap.as_bytes()], &options, bounded)
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

#[test]
fn malformed_source_and_resource_stops_never_publish_partial_results() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = "def make (n : Nat) : Nat -> Nat := let saved : Nat := n; fun (x : Nat) => saved + x\n#eval make 20 22";
    let mut bounded = limits();
    bounded.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
            .is_err()
    );
    let invalid = format!("{source}\n#eval make 20 true");
    assert!(
        base.execute_source_definitions(&[invalid.as_bytes()], &options, limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    execute(source, "42");
}
