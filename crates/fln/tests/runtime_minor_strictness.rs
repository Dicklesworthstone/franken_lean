//! Strict local computation in real source recursor branches, through Golem.
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
        Some(expected)
    );
}

const SPEND: &str = "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n";

#[test]
fn strict_function_valued_minors_keep_captured_results_and_accumulators() {
    execute(
        &format!("{SPEND}#eval @Nat.rec (fun _ => Nat -> Nat) (let paid : Nat := spend 8; fun (x : Nat) => paid + x) (fun (k : Nat) (ih : Nat -> Nat) (x : Nat) => ih (x + 1)) 3 31"),
        "42",
    );
}

#[test]
fn branch_local_owned_values_are_shared_and_remain_in_scope() {
    execute(
        "def copies (n : Nat) : String := match n with | .zero => \"\" | .succ k => copies k ++ \"ab\"\n#eval String.length (@Nat.rec (fun _ => String -> String) (let shared : String := copies 3; fun (s : String) => shared ++ s ++ shared) (fun (k : Nat) (ih : String -> String) (s : String) => ih s) 0 \"z\")",
        "13",
    );
}

#[test]
fn an_unused_initializer_still_runs_and_exhaustion_is_not_success() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let program = |cost| format!(
        "{SPEND}def run (cost : Nat) : Nat := @Nat.rec (fun _ => Nat -> Nat) (let paid : Nat := spend cost; fun (x : Nat) => x) (fun (k : Nat) (ih : Nat -> Nat) (x : Nat) => ih x) 0 42\n#eval run {cost}"
    );
    let mut bounded = limits();
    bounded.vm.max_steps = 2000;
    bounded.vm.max_stack_depth = 256;
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
    let first = run();
    let second = run();
    let VmExit::Returned(value) = &first.executions.last().unwrap().exit else {
        panic!("clean retry did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}
