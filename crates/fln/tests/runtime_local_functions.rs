//! Let-bound native closures, including captured values and owned results.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn execute(source: &str, expected: &str) {
    let result = engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(result) = &result.executions.last().unwrap().exit else {
        panic!("execution did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected)
    );
}
#[test]
fn local_functions_execute_on_the_native_vm_with_captures() {
    execute(
        "def outer (n : Nat) : Nat := let f (x : Nat) : Nat := n + x; f 2\n#eval outer 40",
        "42",
    );
    execute("#eval let f (x : Nat) : Nat := x + 1; f 41", "42");
}

#[test]
fn nested_helpers_capture_other_closures_and_owned_strings() {
    execute(
        "def outer (n : Nat) : Nat := let f (x : Nat) : Nat := let g (y : Nat) : Nat := n + x + y; g 2; f 3\n#eval outer 37",
        "42",
    );
    execute(
        "def outer (prefix : String) (flag : Bool) : Nat := let message (s : String) : String := prefix ++ s; let choose (b : Bool) : Nat := if b then String.length (message \"x\") else String.length (message \"yz\"); choose flag + choose false\n#eval outer \"abc\" true",
        "9",
    );
}

#[test]
fn structurally_equal_lambdas_at_different_capture_types_remain_distinct() {
    execute(
        "def one (v : Nat) : Nat := let f (x : Nat) : Nat := v; f 0\ndef two (v : Bool) : Bool := let f (x : Nat) : Bool := v; f 0\n#eval if two true then one 42 else 0",
        "42",
    );
}

#[test]
fn existing_let_bound_lambda_syntax_uses_the_same_runtime_path() {
    execute(
        "def outer (n : Nat) : Nat := let f : Nat -> Nat := fun x => n + x; f 2\n#eval outer 40",
        "42",
    );
}

#[test]
fn local_partial_applications_and_function_aliases_execute() {
    execute(
        "#eval let add (x y : Nat) : Nat := x + y; let inc : Nat -> Nat := add 1; inc 41",
        "42",
    );
    execute(
        "#eval let f (x : Nat) : Nat := x + 2; let alias : Nat -> Nat := f; alias 40",
        "42",
    );
}

#[test]
fn deterministic_lowering_does_not_modify_the_checked_snapshot() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"#eval let f (x : Nat) : Nat := if true then x + 1 else 0; f 41";
    let a = base
        .execute_source_definitions(
            &[source],
            &options,
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let b = base
        .execute_source_definitions(
            &[source],
            &options,
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(base.logical_root(&options), root);
    assert_eq!(
        a.executions.last().unwrap().flbc_artifact,
        b.executions.last().unwrap().flbc_artifact
    );
}

#[test]
fn closure_budget_refusal_keeps_the_original_engine_usable() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut small = EngineExecutionLimits::new(limits().kernel);
    small.ingress.max_lambda_bindings = 0;
    assert!(
        base.execute_source_definitions(
            &[b"#eval let f (x : Nat) : Nat := x; f 42"],
            &options,
            small
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let run = base
        .execute_source_definitions(
            &[b"#eval let f (x : Nat) : Nat := x; f 42"],
            &options,
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(
        run.executions.last().unwrap().exit,
        VmExit::Returned(_)
    ));
}
