//! Native Option proofs use the real attribute/source-batch/dual-checker path.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    let result = Engine::with_source_seed(limits())
        .expect("source seed must pass both checker seats");
    let Outcome::Complete(engine) = result else {
        panic!("source seed did not complete: {result:?}");
    };
    assert!(engine.environment().contains(&Name::from_components([
        "instDecidableEqOption",
    ])));
    engine
}

#[test]
fn option_instance_attribute_and_proofs_survive_both_checker_seats() {
    let engine = engine();
    let source = include_bytes!("../../../examples/native_option_decide.lean");
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let result = engine
        .check_source_files(&[source.as_slice()], &options, SourceCheckLimits::new(limits()))
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
        assert!(checked.engine.environment().contains(&Name::from_components([label])));
        assert!(!engine.environment().contains(&Name::from_components([label])));
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
            "attribute [instance] instDecidableEqOption\ndef unpublished_prefix : Nat := 0\n{claim}\n"
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
        assert!(!engine.environment().contains(&Name::from_components([
            "unpublished_prefix",
        ])));
        assert_eq!(engine.logical_root(&options), before);
    }
}
