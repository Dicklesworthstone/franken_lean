//! Concrete type arguments after strict callback-producing stages must reach
//! source admission, FIR/FLBC validation, and the ordinary Golem interpreter.
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

fn run(source: &str, expected: &str) -> u64 {
    let report = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &report.executions.last().unwrap().exit else {
        panic!("execution did not return: {source}");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}

const EXPENSIVE: &str = "def expensive (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) n\n";
const STAGED: &str = "def staged (cost : Nat) : {A : Type} -> A -> A := by let paid := expensive cost; intro A x; exact x\n";

#[test]
fn concrete_types_after_strict_initializers_execute_and_capture_outer_values() {
    run(
        "def make (offset : Nat) : (A : Type) -> A -> Nat := by let ready := offset + 1; intro A x; exact ready\n#eval make 41 Nat 0",
        "42",
    );
    run(
        "def make (offset : Nat) : (A : Type) -> A -> Nat := by let ready := offset + 1; intro A x; exact ready\n#eval let saved : Nat -> Nat := make 41 Nat; saved 0",
        "42",
    );
}

#[test]
fn static_types_across_multiple_strict_stages_rebase_captured_values() {
    run(
        "def first (offset : Nat) : (A : Type) -> A -> (B : Type) -> B -> A := by let ready := offset + 1; intro A x; let second := ready + 1; intro B y; exact x\n#eval first 0 Nat 42 String \"unused\"",
        "42",
    );
    run(
        "def first (offset : Nat) : (A : Type) -> A -> (B : Type) -> B -> A := by let ready := offset + 1; intro A x; let second := ready + 1; intro B y; exact x\n#eval String.length (first 0 String \"answer\" Nat 42)",
        "6",
    );
}

#[test]
fn owned_initializers_are_captured_without_crossing_the_type_telescope() {
    run(
        "def make (prefix : String) : (A : Type) -> A -> Nat -> Nat := by let text := prefix ++ \"abc\"; intro A x n; exact n + String.length text\n#eval let saved : Nat -> Nat := make \"x\" String \"ignored\"; saved 17 + saved 17",
        "42",
    );
}

#[test]
fn discarding_the_specialized_callback_does_not_discard_its_initializer() {
    let source = format!(
        "{EXPENSIVE}{STAGED}def use (cost : Nat) : Nat := let saved : Nat -> Nat := @staged cost Nat; 42\n"
    );
    let cheap = run(&format!("{source}#eval use 0"), "42");
    let costly = run(&format!("{source}#eval use 100"), "42");
    assert!(costly > cheap + 100, "the strict initializer was erased");
}

#[test]
fn repeated_calls_share_the_completed_stage_and_uncalled_lambdas_remain_lazy() {
    let definitions = format!(
        "{EXPENSIVE}{STAGED}def use (cost : Nat) : Nat := let saved : Nat -> Nat := @staged cost Nat; saved 42\n"
    );
    let twice = definitions.replace("saved 42", "saved 20 + saved 22");
    let once_delta = run(&format!("{definitions}#eval use 100"), "42")
        - run(&format!("{definitions}#eval use 0"), "42");
    let twice_delta = run(&format!("{twice}#eval use 100"), "42")
        - run(&format!("{twice}#eval use 0"), "42");
    assert!(once_delta > 100);
    assert_eq!(once_delta, twice_delta, "the initializer was duplicated");

    let lazy = format!(
        "{EXPENSIVE}{STAGED}def use (cost : Nat) : Nat := let later : Nat -> Nat := fun n => @staged cost Nat n; 42\n"
    );
    assert_eq!(
        run(&format!("{lazy}#eval use 0"), "42"),
        run(&format!("{lazy}#eval use 100000"), "42"),
        "specialization executed work inside an uncalled lambda"
    );
}

#[test]
fn failed_admission_and_resource_stops_leave_deterministic_clean_retries() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!("{EXPENSIVE}{STAGED}#eval @staged 5 Nat 42");
    let invalid = source.replace("Nat 42", "Nat true");
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
    let mut bounded = limits();
    bounded.vm.max_steps = 2000;
    bounded.vm.max_stack_depth = 256;
    let costly = source.replace("@staged 5", "@staged 100000");
    assert!(matches!(
        base.execute_source_definitions(&[costly.as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let execute = || {
        base.execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = execute();
    let second = execute();
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}
