//! Higher-order source execution crosses the checked native compiler and VM.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap()
}
fn execute(source: &str, expected: &str) {
    let run = engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("not returned");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}
#[test]
fn callback_parameters_execute_dynamic_closure_calls() {
    execute(
        "def twice (f : Nat -> Nat) (x : Nat) : Nat := f (f x)\n#eval let inc (x : Nat) : Nat := x + 1; twice inc 40",
        "42",
    );
}

#[test]
fn callbacks_capture_owned_values_and_return_owned_strings() {
    execute(
        "def twice (f : String -> String) (s : String) : String := f (f s)\n#eval let suffix : String := \"xyz\"; let append (s : String) : String := s ++ suffix; String.length (twice append \"a\")",
        "7",
    );
}

#[test]
fn callback_arities_and_lazy_branches_share_canonical_interfaces() {
    execute(
        "def applyTwo (f : Nat -> Nat -> Nat) (a b : Nat) : Nat := f a b\n#eval let add (a b : Nat) : Nat := if true then a + b else 0; applyTwo add 20 22",
        "42",
    );
    execute(
        "def select (f : Bool -> Nat) (b : Bool) : Nat := f b\n#eval let pick (b : Bool) : Nat := if b then 42 else 0; select pick true",
        "42",
    );
}

#[test]
fn callbacks_may_themselves_accept_callbacks() {
    execute(
        "def withInc (f : (Nat -> Nat) -> Nat) : Nat := let inc (x : Nat) : Nat := x + 1; f inc\n#eval let consume (g : Nat -> Nat) : Nat := g 41; withInc consume",
        "42",
    );
}

#[test]
fn closures_capture_callbacks_and_support_partial_application() {
    execute(
        "def twice (f : Nat -> Nat) (x : Nat) : Nat := let step (y : Nat) : Nat := f y; step (step x)\n#eval let add (x y : Nat) : Nat := x + y; let inc : Nat -> Nat := add 1; twice inc 40",
        "42",
    );
}

#[test]
fn distinct_interfaces_do_not_alias_when_declaration_order_changes() {
    for definitions in [
        "def runNat (f : Nat -> Nat) : Nat := f 41\ndef runBool (f : Bool -> Nat) : Nat := f true\n",
        "def runBool (f : Bool -> Nat) : Nat := f true\ndef runNat (f : Nat -> Nat) : Nat := f 41\n",
    ] {
        execute(
            &format!(
                "{definitions}#eval let n (x : Nat) : Nat := x + 1; let b (x : Bool) : Nat := if x then 0 else 9; runNat n + runBool b"
            ),
            "42",
        );
    }
}

#[test]
fn callback_lowering_is_deterministic_and_refusal_is_failure_atomic() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"def twice (f : Nat -> Nat) (x : Nat) : Nat := f (f x)\n#eval let inc (x : Nat) : Nat := x + 1; twice inc 40";
    let mut limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    limits.ingress.fir.max_closure_types = 0;
    assert!(
        base.execute_source_definitions(&[source], &options, limits)
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let run = || {
        base.execute_source_definitions(
            &[source],
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
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
fn ill_typed_callbacks_cannot_reach_execution() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"def twice (f : Nat -> Nat) (x : Nat) : Nat := f (f x)\n#eval let wrong (x : Bool) : Nat := 0; twice wrong 40";
    assert!(
        base.execute_source_definitions(
            &[source],
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn recursive_functions_carry_typed_callback_arguments() {
    execute(
        "def repeat (n : Nat) (f : Nat -> Nat) (x : Nat) : Nat := match n with | .zero => x | .succ k => f (repeat k f x)\n#eval let inc (x : Nat) : Nat := x + 1; repeat 42 inc 0",
        "42",
    );
}
