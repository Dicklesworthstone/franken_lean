//! Interleaved static arguments cross source admission, specialization and Golem.
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

const KEEP: &str = "def keep (ignored : Nat) {A : Type} (x : A) : A := x\n";

#[test]
fn late_type_parameters_execute_without_phantom_template_results() {
    let source = format!("{KEEP}#eval keep 9 42");
    let run = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(run.executions.len(), 1, "a template is not a VM execution");
    let VmExit::Returned(value) = &run.executions[0].exit else {
        panic!("execution did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn partial_calls_and_open_runtime_captures_keep_their_values() {
    execute(
        &format!("{KEEP}#eval let saved : Nat -> Nat := @keep 9 Nat; saved 42"),
        "42",
    );
    execute(
        &format!("{KEEP}def pass (n : Nat) : Nat := keep n (n + 1)\n#eval pass 41"),
        "42",
    );
}

#[test]
fn distinct_interleaved_types_and_owned_values_do_not_alias() {
    execute(
        "def first (ignored : Nat) {A : Type} (x : A) {B : Type} (y : B) : A := x\n#eval String.length (@first 0 String \"answer\" Nat 7) + @first 0 Nat 36 String \"unused\"",
        "42",
    );
    execute(
        "def suffix (prefix : String) {A : Type} (ignored : A) (tail : String) : String := prefix ++ tail\n#eval String.length (@suffix \"abc\" Nat 7 \"def\")",
        "6",
    );
}

#[test]
fn callbacks_after_a_late_type_argument_keep_checked_interfaces() {
    execute(
        "def use (ignored : Nat) {A : Type} (f : A -> A) (x : A) : A := f x\n#eval use 0 (fun (x : Nat) => x + 1) 41",
        "42",
    );
}

#[test]
fn concrete_class_dictionaries_after_runtime_arguments_are_specialized_separately() {
    let classes = "class Shift (A : Type) where\n  shift : A -> A\ninstance shiftOne : Shift Nat := { shift := fun n => n + 1 }\ninstance shiftTwo : Shift Nat := { shift := fun n => n + 2 }\ndef act (ignored : Nat) {A : Type} [Shift A] (x : A) : A := Shift.shift x\n";
    execute(
        &format!("{classes}#eval @act 0 Nat shiftOne 20 + @act 0 Nat shiftTwo 19"),
        "42",
    );
    execute(&format!("{classes}#eval act 9 40"), "42");
}

const MONAD: &str = "class Pure (f : Type -> Type) where\n  pure : {A : Type} -> A -> f A\nclass Bind (m : Type -> Type) where\n  bind : {A B : Type} -> m A -> (A -> m B) -> m B\ndef Id (A : Type) : Type := A\ninstance idPure : Pure Id := { pure := fun a => a }\ninstance idBind : Bind Id := { bind := fun a k => k a }\ndef step (ignored : Nat) {M : Type -> Type} [Pure M] [Bind M] (action : M Nat) : M Nat := do\n  let x ← action\n  return (x + 1)\n";

#[test]
fn monadic_operations_with_late_type_and_instance_arguments_run_on_golem() {
    execute(&format!("{MONAD}#eval (step 9 (M := Id) 41 : Id Nat)"), "42");
}

#[test]
fn unused_runtime_arguments_are_not_erased_with_static_arguments() {
    let source = format!(
        "{KEEP}def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n#eval keep (spend 100000) 42"
    );
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut bounded = limits();
    bounded.vm.max_steps = 2000;
    bounded.vm.max_stack_depth = 256;
    assert!(matches!(
        base.execute_source_definitions(&[source.as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    execute(&format!("{KEEP}#eval keep 0 42"), "42");
}

#[test]
fn type_errors_and_resource_stops_leave_a_deterministic_clean_retry() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let invalid = format!("{KEEP}#eval @keep 0 Nat true");
    assert!(
        base.execute_source_definitions(&[invalid.as_bytes()], &options, limits())
            .is_err()
    );
    let valid = format!("{MONAD}#eval (step 9 (M := Id) 41 : Id Nat)");
    let mut bounded = limits();
    bounded.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[valid.as_bytes()], &options, bounded)
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let run = || {
        base.execute_source_definitions(&[valid.as_bytes()], &options, limits())
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
