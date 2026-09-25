//! First-class recursors use real source admission, FIR, FLBC and Golem.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};
use fln_core::outcome::Outcome;

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
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("execution did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

const FOLD: &str = "#eval let fold : Nat -> Nat := @Nat.rec (fun (_ : Nat) => Nat) 0 (fun (n ih : Nat) => ih + 1); fold 20 + fold 22";

#[test]
fn a_supplied_motive_and_minors_form_a_reusable_native_fold() {
    execute(FOLD, "42");
    execute(
        "def twice (f : Nat -> Nat) (n : Nat) : Nat := f (f n)\n#eval let add : Nat -> Nat := @Nat.rec (fun (_ : Nat) => Nat) 1 (fun (n ih : Nat) => ih + 1); twice add 40",
        "42",
    );
}

#[test]
fn missing_minors_become_typed_callback_parameters() {
    execute(
        "#eval let step (n ih : Nat) : Nat := ih + 1; let fold : Nat -> (Nat -> Nat -> Nat) -> Nat -> Nat := @Nat.rec (fun (_ : Nat) => Nat); fold 0 step 42",
        "42",
    );
    execute(
        "#eval let pick : Nat -> Bool -> Nat := @Bool.rec (fun (_ : Bool) => Nat) 10; pick 32 true + pick 99 false",
        "42",
    );
}

#[test]
fn owned_branch_values_and_outer_captures_survive_repeated_calls() {
    execute(
        "#eval let left : String := \"abc\"; let right : String := \"defg\"; let pick : Bool -> String := @Bool.rec (fun (_ : Bool) => String) left right; String.length (pick false ++ pick true)",
        "7",
    );
    execute(
        "def compute (base delta : Nat) : Nat := let fold : Nat -> Nat := @Nat.rec (fun (_ : Nat) => Nat) base (fun (n ih : Nat) => ih + delta); fold 2 + fold 3\n#eval compute 1 8",
        "42",
    );
}

#[test]
fn user_defined_recursive_families_use_the_same_partial_call_path() {
    execute(
        "inductive Chain where\n | nil\n | cons (value : Nat) (tail : Chain)\n#eval let total : Chain -> Nat := @Chain.rec (fun (_ : Chain) => Nat) 0 (fun (value : Nat) (tail : Chain) (ih : Nat) => value + ih); total (Chain.cons 20 (Chain.cons 22 Chain.nil))",
        "42",
    );
}

#[test]
fn a_literal_minor_still_eliminates_its_unused_induction_hypothesis() {
    let source = "#eval let prior : Nat -> Nat := @Nat.rec (fun (_ : Nat) => Nat) 7 (fun (n ih : Nat) => n); prior 10000000000000000000000000000000000000000";
    let mut bounded = limits();
    bounded.vm.max_steps = 1000;
    bounded.vm.max_stack_depth = 40;
    let run = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), bounded)
        .unwrap()
        .into_complete()
        .expect("an unused IH must not enumerate the predecessor chain");
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("return value");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("9999999999999999999999999999999999999999")
    );
}

#[test]
fn refusal_does_not_publish_and_retries_produce_identical_bytecode() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut bounded = limits();
    bounded.ingress.max_lambda_bindings = 0;
    assert!(
        base.execute_source_definitions(&[FOLD.as_bytes()], &options, bounded)
            .is_err()
    );
    bounded = limits();
    bounded.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[FOLD.as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let run = || {
        base.execute_source_definitions(&[FOLD.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let second = run();
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn an_invalid_minor_is_not_hidden_by_partial_application() {
    let source = b"#eval let fold : Nat -> Nat := @Nat.rec (fun (_ : Nat) => Nat) 0 (fun (n ih : Nat) => true); fold 0";
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    assert!(
        base.execute_source_definitions(&[source], &options, limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
}
