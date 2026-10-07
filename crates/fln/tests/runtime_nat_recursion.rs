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
        "def copies (pfx : String) (n : Nat) : String := match n with | .zero => pfx | .succ k => copies pfx k ++ pfx\n#eval String.length (copies \"ab\" 5)",
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

/// Bead `fln-golem-ordinary-loops-fbj6`. A loop of ten thousand iterations is an
/// ordinary program, not a resource attack: the pinned Reference prints
/// `50005000` for it. The probe budget (`EngineExecutionLimits::new`) must
/// still stop it with a typed non-answer, and the user-program profile the
/// front doors use must run it. Each half fails if the other's limits are used.
#[test]
fn an_ordinary_loop_runs_under_the_user_program_profile_and_stops_under_the_probe_budget() {
    let source = "def sumTo (n : Nat) : Nat := match n with | .zero => n | .succ k => sumTo k + n\n#eval sumTo 10000";
    let kernel = limits().kernel;

    let probe = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap();
    assert!(
        matches!(probe, fln::Outcome::Inconclusive(_)),
        "the probe budget must stop a 10,000-deep recursion with a typed non-answer"
    );

    let user = EngineExecutionLimits::for_user_program(kernel);
    assert_eq!(user.vm.max_steps, u64::MAX);
    assert!(user.vm.max_stack_depth > limits().vm.max_stack_depth);
    let completed = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), user)
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(result) = &completed.executions.last().unwrap().exit else {
        panic!("the user-program profile did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("50005000")
    );
    assert!(
        result.usage.steps > limits().vm.max_steps / 10,
        "the run should be far past anything the probe budget's depth allows: {:?}",
        result.usage
    );
    assert!(result.usage.peak_stack_depth > limits().vm.max_stack_depth);
}

/// The engine runs its compiled programs through Golem's inline caches. The
/// uncached path (`execute_flbc_artifact`) is the semantic definition, so the
/// two must agree on the value AND on the instruction and frame accounting for
/// the very artifact the engine executed. A cache that changed an answer or
/// skipped charged work fails here.
#[test]
fn the_cached_engine_run_agrees_with_the_uncached_semantic_path() {
    for (source, expected) in [
        (
            "def fact (n : Nat) : Nat := match n with | .zero => 1 | .succ k => fact k * n\n#eval fact 25",
            "15511210043330985984000000",
        ),
        (
            "def sum (n acc : Nat) : Nat := match n with | .zero => acc | .succ k => sum k (acc + n)\n#eval sum 300 2",
            "45152",
        ),
        (
            "def walk (n a b : Nat) : Nat := match n with | .zero => a + b | .succ k => walk k (a + 1) (b + 2)\n#eval walk 200 1 2",
            "603",
        ),
    ] {
        let user = EngineExecutionLimits::for_user_program(limits().kernel);
        let completed = engine()
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), user)
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
        let execution = completed.executions.last().unwrap();
        let VmExit::Returned(cached) = &execution.exit else {
            panic!("cached run did not return: {source}")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&cached.value).as_deref(),
            Some(expected),
            "{source}"
        );

        let uncached_limits = fln::FlbcExecutionLimits {
            vm: user.vm,
            ..fln::FlbcExecutionLimits::default()
        };
        let uncached =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), uncached_limits)
                .unwrap()
                .into_complete()
                .unwrap();
        let VmExit::Returned(uncached) = &uncached else {
            panic!("uncached run did not return: {source}")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&uncached.value).as_deref(),
            Some(expected),
            "{source}"
        );
        assert_eq!(cached.usage, uncached.usage, "{source}");
    }
}
