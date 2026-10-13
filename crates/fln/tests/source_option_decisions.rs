//! Native Option proofs use the real attribute/source-batch/dual-checker path.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    let result =
        Engine::with_source_seed(limits()).expect("source seed must pass both checker seats");
    let Outcome::Complete(engine) = result else {
        panic!("source seed did not complete: {result:?}");
    };
    assert!(
        engine
            .environment()
            .contains(&Name::from_components(["Option", "instDecidableEq"]))
    );
    engine
}

#[test]
fn option_instance_attribute_and_proofs_survive_both_checker_seats() {
    let engine = engine();
    let source = include_bytes!("../../../examples/native_option_decide.lean");
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let result = engine
        .check_source_files(
            &[source.as_slice()],
            &options,
            SourceCheckLimits::new(limits()),
        )
        .expect("native Option example must elaborate and pass both checker seats");
    let Outcome::Complete(checked) = result else {
        panic!("source batch did not complete: {result:?}");
    };
    assert_eq!(checked.theorems, 7);
    for label in [
        "option_same",
        "option_different",
        "option_empty_left",
        "option_empty_right",
        "option_empty_same",
        "option_nested_same",
        "option_nested_different",
        "option_lifted",
    ] {
        assert!(
            checked
                .engine
                .environment()
                .contains(&Name::from_components([label]))
        );
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components([label]))
        );
    }
    assert_eq!(engine.logical_root(&options), before);
}

#[test]
fn false_option_claims_refuse_without_publishing_the_batch_prefix() {
    let engine = engine();
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    for claim in [
        "theorem false_element : (Option.some 0 : Option Nat) = Option.some 1 := by decide",
        "theorem false_constructor : (Option.none : Option Nat) = Option.some 0 := by decide",
        "theorem false_negation : Not ((Option.some 0 : Option Nat) = Option.some 0) := by decide",
        "theorem false_nested : Option.some (Option.none : Option Bool) = Option.some (Option.some Bool.false) := by decide",
    ] {
        let source = format!(
            "attribute [instance] Option.instDecidableEq\ndef unpublished_prefix : Nat := 0\n{claim}\n"
        );
        let result = engine.check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(limits()),
        );
        let error = result.expect_err("a false Option proof must refuse, not succeed or time out");
        let (kind, _, _) = error.disposition();
        assert!(
            matches!(kind, "elaboration" | "kernel-rejection"),
            "{claim}\nunexpected refusal: {error} ({kind})"
        );
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["unpublished_prefix",]))
        );
        assert_eq!(engine.logical_root(&options), before);
    }
}

fn registered_engine() -> Engine {
    let engine = engine();
    engine
        .check_source_files(
            &[b"attribute [instance] Option.instDecidableEq"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect("the ordinary source attribute registers an admitted dictionary")
        .into_complete()
        .expect("registration must complete")
        .engine
}

#[test]
fn registered_option_decisions_infer_generic_and_nested_dictionaries() {
    let engine = registered_engine();
    let source = br#"
        theorem empty : (Option.none : Option Nat) = Option.none := by decide
        theorem same : (Option.some 7 : Option Nat) = Option.some 7 := by decide
        theorem different : Not ((Option.some 7 : Option Nat) = Option.some 9) := by decide
        theorem nested :
          Not (Option.some (Option.none : Option Bool) = Option.some (Option.some Bool.false)) := by decide
        def generic {A : Type 1} [DecidableEq A] (x y : Option A) : Decidable (x = y) := decEq x y
    "#;
    let result = engine
        .check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(limits()))
        .expect("ordinary source registration enables the admitted Option dictionary")
        .into_complete()
        .expect("both checker seats must answer");
    assert_eq!(result.theorems, 4);
    assert!(
        result
            .engine
            .environment()
            .contains(&Name::from_components(["generic"]))
    );
}

#[test]
fn registered_option_decisions_execute_in_native_conditionals() {
    let engine = registered_engine();
    let execution_limits = fln::EngineExecutionLimits::new(limits().kernel);
    let source = br#"
        def compareOptions (a b : Option Nat) : Nat := if a = b then 17 else 25
        #eval compareOptions (Option.some 7) (Option.some 7) + compareOptions Option.none (Option.some 7)
    "#;
    let batch = engine
        .execute_source_definitions(&[source], &KVMap::new(), execution_limits)
        .expect("inferred dictionary must survive native compilation and execution")
        .into_complete()
        .expect("execution must complete");
    let fln::VmExit::Returned(result) = &batch.executions.last().unwrap().exit else {
        panic!("native Option comparison did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("42")
    );
}

fn execute(source: &str, expected: &str) -> u64 {
    let engine = registered_engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let batch = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &options,
            fln::EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("decision computation must answer");
    let fln::VmExit::Returned(result) = &batch.executions.last().unwrap().exit else {
        panic!("decision computation did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected)
    );
    assert_eq!(engine.logical_root(&options), root);
    result.usage.steps
}

#[test]
fn checked_decisions_are_runtime_arguments_and_results_not_only_conditionals() {
    execute(
        r#"
        def decision (a b : Nat) : Decidable (a = b) := Nat.decEq a b
        def consume (a b : Nat) (d : Decidable (a = b)) : Nat :=
          match d with | .isFalse h => 25 | .isTrue h => 17
        #eval consume 3 3 (decision 3 3) + consume 3 4 (decision 3 4)
        "#,
        "42",
    );
}

#[test]
fn decisions_cross_dependent_callable_results_and_local_instance_binders() {
    execute(
        r#"
        def make (a : Nat) : (b : Nat) -> Decidable (a = b) := fun b => Nat.decEq a b
        def consume (a b : Nat) [d : Decidable (a = b)] : Nat := if a = b then 17 else 25
        #eval consume 2 2 (d := make 2 2) + consume 2 3 (d := make 2 3)
        "#,
        "42",
    );
}

#[test]
fn nested_option_decisions_compute_both_constructor_tags_and_negation() {
    execute(
        r#"
        def choose (a b : Option (Option Bool)) : Nat := if Not (a = b) then 25 else 17
        #eval choose (Option.some Option.none) (Option.some Option.none) +
          choose (Option.some Option.none) (Option.some (Option.some false))
        "#,
        "42",
    );
}

#[test]
fn decisions_retain_strict_value_computation_and_lazy_branches() {
    let program = |cost| {
        format!(
            r#"
        def expensive (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih) n
        #eval if (Option.some (expensive {cost}) : Option Nat) = Option.some 0
          then 42 else 2 ^ 1000000000
        "#
        )
    };
    let small = execute(&program(0), "42");
    let large = execute(&program(40), "42");
    assert!(large > small + 100, "decision operands must still execute");
}
