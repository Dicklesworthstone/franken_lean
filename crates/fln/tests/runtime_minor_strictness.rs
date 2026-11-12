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

const SPEND: &str =
    "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n";

#[test]
fn strict_function_valued_minors_keep_captured_results_and_accumulators() {
    execute(
        &format!(
            "{SPEND}#eval @Nat.rec (fun _ => Nat -> Nat) (let paid : Nat := spend 8; fun (x : Nat) => paid + x) (fun (k : Nat) (ih : Nat -> Nat) (x : Nat) => ih (x + 1)) 3 31"
        ),
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
fn unused_initializers_are_cheap_and_used_initializer_exhaustion_is_not_success() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let program = |cost, used| {
        let body = if used { "paid + x" } else { "x" };
        format!(
            "{SPEND}def run (cost : Nat) : Nat := @Nat.rec (fun _ => Nat -> Nat) (let paid : Nat := spend cost; fun (x : Nat) => {body}) (fun (k : Nat) (ih : Nat -> Nat) (x : Nat) => ih x) 0 42\n#eval run {cost}"
        )
    };
    let mut bounded = limits();
    bounded.vm.max_steps = 2000;
    bounded.vm.max_stack_depth = 256;
    // The original pure initializer is dead and must remain cheap even with
    // a large input. Fuel checks below use a value captured by the result.
    let unused = program(100000, false);
    let unused_run = base
        .execute_source_definitions(&[unused.as_bytes()], &options, bounded)
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &unused_run.executions.last().unwrap().exit else {
        panic!("unused initializer did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
    assert_eq!(base.logical_root(&options), root);
    execute(&program(30, true), "72");

    let expensive = program(100000, true);
    assert!(matches!(
        base.execute_source_definitions(&[expensive.as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let cheap = program(0, true);
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
