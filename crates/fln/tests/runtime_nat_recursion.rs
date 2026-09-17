//! Real source admission, closure conversion, bytecode validation and native VM.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};

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
    let result = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(result) = &result.executions.last().unwrap().exit else {
        panic!("execution did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

#[test]
fn structural_recursion_executes_instead_of_becoming_an_unknown_constant() {
    execute(
        "def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1\n#eval count 7",
        "7",
    );
    execute(
        "def fact (n : Nat) : Nat := match n with | .zero => 1 | .succ k => fact k * n\n#eval fact 10",
        "3628800",
    );
}
#[test]
fn recursive_root_references_are_rebound_to_each_successor() {
    execute(
        "def sumTo (n : Nat) : Nat := match n with | .zero => n | .succ k => sumTo k + n\n#eval sumTo 10",
        "55",
    );
}
#[test]
fn changing_accumulators_are_flattened_into_native_closure_arguments() {
    execute(
        "def sum (n acc : Nat) : Nat := match n with | .zero => acc | .succ k => sum k (acc + n)\n#eval sum 10 2",
        "57",
    );
    execute(
        "def walk (n a b : Nat) : Nat := match n with | .zero => a + b | .succ k => walk k (a + 1) (b + 2)\n#eval walk 10 1 2",
        "33",
    );
}
#[test]
fn fixed_captures_and_local_helpers_survive_recursive_branch_lifting() {
    execute(
        "def addMany (delta n : Nat) : Nat := match n with | .zero => delta | .succ k => let add (x : Nat) : Nat := x + delta; add (addMany delta k)\n#eval addMany 3 5",
        "18",
    );
}
#[test]
fn owned_strings_and_boolean_results_execute_recursively() {
    execute(
        "def copies (prefix : String) (n : Nat) : String := match n with | .zero => prefix | .succ k => copies prefix k ++ prefix\n#eval String.length (copies \"ab\" 5)",
        "12",
    );
    execute(
        "def even (n : Nat) : Bool := match n with | .zero => true | .succ k => if even k then false else true\n#eval if even 12 then 42 else 0",
        "42",
    );
}
#[test]
fn unused_induction_hypotheses_do_not_force_predecessor_enumeration() {
    execute(
        "def prior (n : Nat) : Nat := match n with | .zero => 7 | .succ k => k\n#eval prior 10000000000000000000000000000000000000000",
        "9999999999999999999999999999999999999999",
    );
    execute(
        "def prior (n : Nat) : Nat := match n with | .zero => 7 | .succ k => k\n#eval prior 0",
        "7",
    );
}
#[test]
fn canonical_nat_constructors_use_the_scalar_representation() {
    execute("#eval Nat.succ (Nat.succ Nat.zero)", "2");
    execute(
        "#eval Nat.succ 18446744073709551615",
        "18446744073709551616",
    );
}
#[test]
fn nested_recursors_and_multiple_uses_of_the_hypothesis_execute() {
    execute(
        "def twice (n : Nat) : Nat := match n with | .zero => 1 | .succ k => twice k + twice k\n#eval twice 8",
        "256",
    );
    execute(
        "def nested (n : Nat) : Nat := match n with | .zero => 1 | .succ k => match k with | .zero => 2 | .succ j => nested k + j\n#eval nested 5",
        "8",
    );
}

#[test]
fn repeated_hypotheses_share_work_and_large_matches_stay_constant_depth() {
    for (source, expected, step_bound, stack_bound) in [
        (
            "def twice (n : Nat) : Nat := match n with | .zero => 1 | .succ k => twice k + twice k\n#eval twice 50",
            "1125899906842624",
            20000,
            300,
        ),
        (
            "def prior (n : Nat) : Nat := match n with | .zero => 7 | .succ k => k\n#eval prior 10000000000000000000000000000000000000000",
            "9999999999999999999999999999999999999999",
            500,
            20,
        ),
    ] {
        let mut bounded = limits();
        bounded.vm.max_steps = step_bound;
        bounded.vm.max_stack_depth = stack_bound;
        let run = engine()
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), bounded)
            .unwrap_or_else(|error| panic!("{source}: {error:?}"))
            .into_complete()
            .expect("bounded execution must finish");
        let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
            panic!("return value");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn limits_are_nonanswers_and_do_not_publish_a_partial_environment() {
    use fln_core::outcome::Outcome;
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1\n#eval count 100";
    let mut small = limits();
    small.vm.max_steps = 50;
    assert!(matches!(
        base.execute_source_definitions(&[source], &options, small)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    small = limits();
    small.vm.max_stack_depth = 5;
    assert!(matches!(
        base.execute_source_definitions(&[source], &options, small)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    small = limits();
    small.ingress.max_lambda_bindings = 0;
    assert!(
        base.execute_source_definitions(&[source], &options, small)
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    assert!(
        !base
            .environment()
            .contains(&fln::Name::from_components(["count"]))
    );
    execute(std::str::from_utf8(source).unwrap(), "100");
}

#[test]
fn invalid_untaken_branches_and_nondecreasing_calls_remain_rejected() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "def bad (n : Nat) : Nat := match n with | .zero => 7 | .succ k => \"wrong\"\n#eval bad 0",
        "def bad (n : Nat) : Nat := match n with | .zero => 7 | .succ k => bad n\n#eval bad 0",
        "def bad (n : Nat) : Nat := match n with | .zero => 7 | .succ k => let unused : Bool := 1; bad k\n#eval bad 0",
    ] {
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn repeated_compilation_is_deterministic_and_retains_the_original_checked_terms() {
    let base = engine();
    let source = b"def sum (n acc : Nat) : Nat := match n with | .zero => acc | .succ k => sum k (acc + n)\n#eval sum 10 2";
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let one = base
        .execute_source_definitions(&[source], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let two = base
        .execute_source_definitions(&[source], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(base.logical_root(&options), root);
    assert_eq!(one.result_logical_root, two.result_logical_root);
    for (one, two) in one.executions.iter().zip(&two.executions) {
        assert_eq!(one.flbc_artifact, two.flbc_artifact);
        assert_eq!(one.declaration, two.declaration);
    }
}
