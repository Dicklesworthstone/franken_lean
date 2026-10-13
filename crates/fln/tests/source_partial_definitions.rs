//! Partial source programs must execute their recursive bodies, never their
//! logical inhabitants; all candidates use ordinary atomic council admission.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    VmExit,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(budget()))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(EngineAdmissionLimits::new(budget())),
    )
    .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
    .into_complete()
    .unwrap()
    .engine
}
fn run(base: &Engine, source: &str, expected: &str) {
    let result = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let [execution] = result.executions.as_slice() else {
        panic!("expected one evaluation")
    };
    let VmExit::Returned(value) = &execution.exit else {
        panic!("{execution:?}")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}
const COUNT: &str = include_str!("../../fln-parse/tests/fixtures/partial_definitions/Opacity.lean");
#[test]
fn partial_recursion_has_both_checked_halves_and_runs_the_body() {
    let base = checked(&engine(), COUNT);
    let name = Name::from_components(["count"]);
    assert!(
        matches!(base.environment().find(&name), Some(ConstantInfo::Opaque(value)) if !value.is_unsafe)
    );
    assert!(
        matches!(base.environment().find(&Name::str(name, "_unsafe_rec")), Some(ConstantInfo::Defn(value)) if value.safety == DefinitionSafety::Partial)
    );
    run(&base, "#eval count 4", "7");
}
#[test]
fn partial_nonrecursive_definition_keeps_ordinary_reduction() {
    let base = checked(
        &engine(),
        "partial def answer : Nat := 42\ntheorem answer_eq : answer = 42 := by rfl",
    );
    run(&base, "#eval answer", "42");
}
#[test]
fn recursive_opaque_does_not_prove_its_computation() {
    let base = checked(&engine(), COUNT);
    assert!(
        base.check_source_files(
            &[b"theorem unsound : count 0 = 7 := by rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(budget()))
        )
        .is_err()
    );
    assert!(
        base.check_source_files(
            &[b"def unsafeLeak : Nat := count._unsafe_rec 0"],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(budget()))
        )
        .is_err()
    );
    run(&base, "#eval count 1", "7");
}
#[test]
fn missing_inhabitant_and_bad_body_publish_neither_half() {
    let base = engine();
    for source in [
        "partial def impossible (n : Nat) : False := impossible n",
        "partial def bad (n : Nat) : Nat := if n == 0 then true else bad n",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(EngineAdmissionLimits::new(budget()))
            )
            .is_err(),
            "{source}"
        );
    }
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["impossible"]))
    );
    checked(&base, COUNT);
}

#[test]
fn mixed_source_stream_admits_the_pair_before_evaluation() {
    run(&engine(), &format!("{COUNT}#eval count 5"), "7");
    run(
        &engine(),
        "partial def gcd' (a b : Nat) : Nat := if b == 0 then a else gcd' b (a % b)\n#eval gcd' 48 18",
        "6",
    );
}

#[test]
fn polymorphic_partial_results_can_use_a_parameter_as_the_inhabitant() {
    run(
        &engine(),
        "partial def keep {α : Type} (x : α) (n : Nat) : α := if n == 0 then x else keep x (n - 1)\n#eval keep 42 3",
        "42",
    );
}

#[test]
fn section_captures_are_fixed_parameters_of_recursive_calls() {
    let source = "section\nvariable (offset : Nat)\npartial def captured (n : Nat) : Nat := if n == 0 then offset else captured (n - 1)\nend\n#eval captured 41 3";
    run(&engine(), source, "41");
}

#[test]
fn namespace_and_leading_lambda_recursion_resolve_the_companion() {
    run(
        &engine(),
        "namespace N\npartial def down : Nat → Nat := fun n => if n == 0 then 9 else down (n - 1)\nend N\n#eval N.down 3",
        "9",
    );
}

#[test]
fn nontermination_is_a_runtime_nonanswer_not_a_logical_default() {
    let base = checked(
        &engine(),
        "partial def spin (n : Nat) : Nat := spin (n + 1)",
    );
    let mut limits = EngineExecutionLimits::new(budget());
    limits.vm.max_steps = 1000;
    assert!(matches!(
        base.execute_source_definitions(&[b"#eval spin 0"], &KVMap::new(), limits)
            .unwrap(),
        fln_core::outcome::Outcome::Inconclusive(_)
    ));
}

#[test]
fn an_existing_companion_prevents_publication_of_the_logical_half() {
    let base = checked(&engine(), "def count._unsafe_rec (n : Nat) : Nat := n");
    let before = base.environment().clone();
    assert!(
        base.check_source_files(
            &[COUNT.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(budget()))
        )
        .is_err()
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["count"]))
    );
    assert_eq!(base.environment(), &before);
    run(&base, "#eval count._unsafe_rec 11", "11");
}

#[test]
fn unsupported_modifiers_and_termination_claims_are_not_silently_ignored() {
    let base = engine();
    for source in [
        "partial def count (n : Nat) : Nat := count n\ntermination_by n",
        "partial def count (n : Nat) : Nat := count n\ndecreasing_by rfl",
        "@[simp] partial def count (n : Nat) : Nat := count n",
        "noncomputable partial def count (n : Nat) : Nat := count n",
        "unsafe partial def count (n : Nat) : Nat := count n",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(EngineAdmissionLimits::new(budget()))
            )
            .is_err(),
            "{source}"
        );
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["count"]))
        );
    }
    checked(&base, COUNT);
}

#[test]
fn support_constants_are_not_reinterpreted_by_namespace_shadowing() {
    let base = checked(
        &engine(),
        "namespace N\ndef default : Bool := true\npartial def down (n : Nat) : Nat := if n == 0 then 9 else down (n - 1)\nend N",
    );
    run(&base, "#eval N.down 3", "9");
}

#[test]
fn a_partial_companion_cannot_launder_noncomputable_execution() {
    let base = engine();
    let source = "noncomputable def hiddenValue (n : Nat) : Nat := n + 23\n\
        partial def disguised (n : Nat) : Nat := \
        if n == 0 then hiddenValue n else disguised (n - 1)";
    let admitted = checked(&base, source);
    assert!(
        admitted
            .execute_source_definitions(
                &[b"#eval disguised 2"],
                &KVMap::new(),
                EngineExecutionLimits::new(budget()),
            )
            .is_err(),
        "the opaque logical witness must not authorize a noncomputable body"
    );
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["disguised"]))
    );
    checked(&base, COUNT);
}
