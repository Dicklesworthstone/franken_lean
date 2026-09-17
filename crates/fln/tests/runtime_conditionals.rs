//! Native runtime control flow, not kernel-only simplification.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};

fn execute(source: &str) -> fln::DefinitionBatchExecution {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits)
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}
fn natural(source: &str, expected: u64) {
    let batch = execute(source);
    let VmExit::Returned(result) = &batch.executions.last().unwrap().exit else {
        panic!("{batch:?}");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected.to_string().as_str())
    );
}
#[test]
fn boolean_cases_execute_inside_functions_and_nested_expressions() {
    natural(
        "def choose (b : Bool) : Nat := if b then 17 else 23\n#eval choose true + choose false",
        40,
    );
    natural(
        "def nested (a b : Bool) : Nat := if a then if b then 1 else 2 else if b then 3 else 4\n#eval nested false true",
        3,
    );
    natural(
        "def choose (b : Bool) (x : Nat) : Nat := let y := x + 4; if b then y * 2 else y * 3\n#eval choose false 10",
        42,
    );
    natural(
        "#eval if (if true then false else true) then 11 else 42",
        42,
    );
}
#[test]
fn boolean_match_executes_and_untaken_work_is_not_evaluated() {
    natural(
        "def pick (b : Bool) : Nat := match b with | true => 17 | false => 23\n#eval pick false",
        23,
    );
    natural(
        "def lazy (b : Bool) : Nat := if b then 42 else 2 ^ 1000000000\n#eval lazy true",
        42,
    );
}
#[test]
fn string_branches_keep_captured_values_and_owned_results() {
    let batch = execute(
        "def choose (b : Bool) (x : String) : String := if b then x ++ \"!\" else x ++ \"?\"\n#eval choose false \"native\"",
    );
    let VmExit::Returned(result) = &batch.executions.last().unwrap().exit else {
        panic!("{batch:?}");
    };
    let (size, _, _, bytes) = result.value.string_view();
    assert_eq!(&bytes[..size - 1], b"native?");
}

#[test]
fn scalar_results_and_nested_captures_survive_bytecode_roundtrip() {
    natural(
        "def outer (a b : Bool) (x : Nat) : Nat := let y := x + 7; let z := y + 10; if a then (if b then z else y) else (if b then y * 2 else x)\n#eval outer true true 25",
        42,
    );
    let big = "#eval if false then 0 else 184467440737095516160000";
    let batch = execute(big);
    let VmExit::Returned(result) = &batch.executions.last().unwrap().exit else {
        panic!("{batch:?}");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("184467440737095516160000")
    );
    let batch =
        execute("def negate (b : Bool) : Bool := if b then false else true\n#eval negate false");
    let VmExit::Returned(result) = &batch.executions.last().unwrap().exit else {
        panic!("{batch:?}");
    };
    assert_eq!(result.value.unbox(), 1);
}

#[test]
fn invalid_untaken_branches_and_resource_stops_publish_nothing() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for source in [
        "def broken : Nat := if true then 42 else \"wrong\"",
        "def broken : Nat := if false then missing else 42",
        "def broken : Nat := if true then 42 else (by exact True.intro)",
    ] {
        assert!(
            engine
                .execute_source_definitions(&[source.as_bytes()], &options, limits)
                .is_err(),
            "{source}"
        );
        assert_eq!(engine.logical_root(&options), root);
    }
    let source = "def pick (b : Bool) : Nat := if b then 42 else 17\n#eval pick true";
    let mut small = limits;
    small.ingress.max_lambda_bindings = 0;
    assert!(
        engine
            .execute_source_definitions(&[source.as_bytes()], &options, small)
            .is_err()
    );
    assert_eq!(engine.logical_root(&options), root);
    let first = engine
        .execute_source_definitions(&[source.as_bytes()], &options, limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let second = engine
        .execute_source_definitions(&[source.as_bytes()], &options, limits)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(engine.logical_root(&options), root);
    assert_eq!(first.result_logical_root, second.result_logical_root);
    for (first, second) in first.executions.iter().zip(&second.executions) {
        assert_eq!(first.flbc_artifact, second.flbc_artifact);
        assert_eq!(first.declaration, second.declaration);
    }
}

#[test]
fn identical_branch_bodies_in_different_capture_contexts_do_not_alias() {
    natural(
        "def keepNat (b : Bool) (x : Nat) : Nat := if b then x else x\ndef keepText (b : Bool) (x : String) : String := if b then x else x\n#eval keepNat true 41 + String.length (keepText false \"a\")",
        42,
    );
}
