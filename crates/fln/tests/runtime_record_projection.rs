//! Ground record field access through actual source admission and native execution.
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
    let result = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let execution = result.executions.last().unwrap();
    let VmExit::Returned(value) = &execution.exit else {
        panic!("{execution:?}")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
    value.usage.steps
}

#[test]
fn generic_projections_choose_the_receivers_ground_layout() {
    run(
        "structure Box (A : Type) where\n  value : A\ndef read (b : Box Nat) : Nat := b.value\n#eval read { value := 42 }",
        "42",
    );
    run(
        "structure Box (A : Type) where\n  value : A\ndef read {A : Type} (b : Box A) : A := b.value\n#eval String.length (read { value := \"hello\" }) + read { value := 37 }",
        "42",
    );
}

#[test]
fn nested_projected_updated_and_computed_receivers_keep_exact_types() {
    run(
        "structure Box (A : Type) where\n  value : A\nstructure Entry (A : Type) where\n  item : Box A\n  count : Nat\ndef modify (e : Entry String) : Entry String := { e with item := { e.item with value := e.item.value ++ \"!\" } }\n#eval let e : Entry String := modify { item := { value := \"hello\" }, count := 36 }; String.length e.item.value + e.count",
        "42",
    );
    run(
        "structure Box (A : Type) where\n  value : A\ndef choose (b : Bool) (x y : Box Nat) : Box Nat := if b then x else y\n#eval (choose true { value := 42 } { value := 7 }).value",
        "42",
    );
}

#[test]
fn projection_functions_and_local_receivers_survive_closure_conversion() {
    run(
        "structure Box (A : Type) where\n  value : A\ndef make (offset n : Nat) : Nat := let b : Box Nat := { value := n + offset }; b.value\n#eval List.foldl Nat.add 0 (List.map (make 10) [9, 13])",
        "42",
    );
    run(
        "structure Box (A : Type) where\n  value : A\ndef values : List (Box Nat) := [Box.mk 19, Box.mk 23]\n#eval List.foldl Nat.add 0 (List.map Box.value values)",
        "42",
    );
}

#[test]
fn receiver_evaluation_is_strict_and_shared_across_projections() {
    let prefix = "structure Pair (A : Type) where\n  first : A\n  second : Nat\ndef work (n : Nat) : Nat := match n with | .zero => 0 | .succ k => work k + 1\n";
    let idle = run(&format!("{prefix}#eval (Pair.mk 42 (work 0)).first"), "42");
    let busy = run(&format!("{prefix}#eval (Pair.mk 42 (work 30)).first"), "42");
    assert!(
        busy > idle + 30,
        "discarded field was not evaluated: {idle} vs {busy}"
    );
    let shared = run(
        &format!("{prefix}#eval let p : Pair Nat := Pair.mk (work 30) 0; p.first + p.first"),
        "60",
    );
    let duplicated = run(
        &format!("{prefix}#eval (Pair.mk (work 30) 0).first + (Pair.mk (work 30) 0).first"),
        "60",
    );
    assert!(
        shared < duplicated,
        "receiver duplicated: {shared} vs {duplicated}"
    );
}

#[test]
fn projection_limits_fail_atomically_and_retry_deterministically() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"structure Box (A : Type) where\n  value : A\ndef read (b : Box Nat) : Nat := b.value\n#eval read { value := 42 }";
    let mut small = limits();
    small.ingress.fir.max_constructors = 0;
    assert!(
        base.execute_source_definitions(&[source], &options, small)
            .is_err()
    );
    small = limits();
    small.vm.max_steps = 1;
    assert!(matches!(
        base.execute_source_definitions(&[source], &options, small)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let first = base
        .execute_source_definitions(&[source], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let second = base
        .execute_source_definitions(&[source], &options, limits())
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
}
