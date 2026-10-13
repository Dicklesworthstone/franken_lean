//! Macro-inline Prelude conditionals keep only the selected branch executable.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};
use fln_core::outcome::Outcome;

fn limits() -> EngineExecutionLimits {
    let mut limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    limits.vm.max_steps = 2000;
    limits.vm.max_stack_depth = 256;
    limits
}

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}

const SPEND: &str =
    "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n";

#[test]
fn canonical_conditionals_delay_both_branches_and_keep_the_selected_result() {
    let base = engine();
    for query in [
        "#eval ite True 42 (spend 10000)",
        "#eval ite False (spend 10000) 42",
        "#eval dite True (fun _ => 42) (fun _ => spend 10000)",
        "#eval dite False (fun _ => spend 10000) (fun _ => 42)",
        "def choose (b : Bool) : Nat := ite (b = true) 42 (spend 10000)\n#eval choose true",
    ] {
        let source = format!("{SPEND}{query}");
        let execution = base
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
            .unwrap_or_else(|error| panic!("{query}: {error:?}"))
            .into_complete()
            .unwrap_or_else(|error| panic!("{query}: evaluation did not finish: {error:?}"));
        let VmExit::Returned(value) = &execution.executions.last().unwrap().exit else {
            panic!("{query}: no return value");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42"),
            "{query}"
        );
    }
}

#[test]
fn selected_branches_and_ordinary_arguments_still_execute_before_returning() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for query in [
        "#eval ite True (spend 10000) 42",
        "#eval ite False 42 (spend 10000)",
        "def keep (answer ignored : Nat) : Nat := answer\n#eval keep 42 (spend 10000)",
    ] {
        let source = format!("{SPEND}{query}");
        assert!(matches!(
            base.execute_source_definitions(&[source.as_bytes()], &options, limits())
                .unwrap_or_else(|error| panic!("{query}: {error:?}")),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn failed_conditionals_leave_a_deterministic_clean_retry() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    assert!(
        base.execute_source_definitions(&[b"#eval ite True 42 false"], &options, limits())
            .is_err()
    );
    let source = b"#eval ite True 42 0";
    let run = || {
        base.execute_source_definitions(&[source], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let retry = run();
    assert_eq!(
        first.executions[0].flbc_artifact,
        retry.executions[0].flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}
