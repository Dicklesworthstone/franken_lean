//! Whole-function motives for structural matches inside ordinary applications.
#![forbid(unsafe_code)]

use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionError,
    EngineExecutionLimits, KVMap, Name, NatDefinitionFrontendError, Outcome, SourceCheckError,
    SourceCheckLimits, VmExit,
};
use fln_elab::{NatDefinitionElabError, source::SourceInferenceError};

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
    execute_on(&engine(), source, expected);
}
fn execute_on(base: &Engine, source: &str, expected: &str) {
    let result = base
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("admission and execution must complete");
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("contextual recursive execution must return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}
fn inference(error: &SourceCheckError) -> &SourceInferenceError {
    let SourceCheckError::Command { error, .. } = error else {
        panic!("expected a semantic elaboration refusal: {error:?}");
    };
    let mut error = error.as_ref();
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = inner;
    }
    let EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
        NatDefinitionElabError::Inference(reason),
    )) = error
    else {
        panic!("expected a semantic elaboration refusal: {error:?}");
    };
    reason
}

#[test]
fn whole_body_induction_hypotheses_prove_and_execute_contextual_recursion() {
    // Exact sources and values independently accepted by Lean v4.32.0/8c9756b.
    for (source, expected) in [
        (
            "def loop (n : Nat) : Nat := (match n with | .zero => 0 | .succ k => loop k) + 1\ntheorem loopThree : loop 3 = 4 := rfl\n#eval loop 3",
            "4",
        ),
        (
            "def throughFunction (n : Nat) : Nat := (match n with | .zero => fun x => x | .succ k => fun x => throughFunction k + x) 7\ntheorem throughFunctionThree : throughFunction 3 = 28 := rfl\n#eval throughFunction 3",
            "28",
        ),
        (
            "def repeated (n : Nat) : String := (match n with | .zero => \"\" | .succ k => repeated k) ++ \"x\"\n#eval String.length (repeated 2)",
            "3",
        ),
    ] {
        execute(source, expected);
    }
    let checked = engine()
        .check_source_files(
            &[b"def loop (n : Nat) : Nat := (match n with | .zero => 0 | .succ k => loop k) + 1"],
            &KVMap::new(),
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let Some(ConstantInfo::Defn(definition)) = checked
        .engine
        .environment()
        .find(&Name::from_components(["loop"]))
    else {
        panic!("an ordinary checked definition is published");
    };
    assert!(!definition.value.has_fvar());
    assert!(!definition.value.has_expr_mvar());
}

#[test]
fn pattern_aliases_do_not_capture_outer_arguments_or_the_current_major() {
    for (source, expected) in [
        (
            "def shadow (k n : Nat) : Nat := (match n with | .zero => k | .succ k => shadow 7 k) + k\ntheorem shadowTwo : shadow 9 2 = 30 := rfl\n#eval shadow 9 2",
            "30",
        ),
        (
            "def sum (n : Nat) : Nat := (match n with | .zero => 0 | .succ n => sum n) + n\ntheorem sumThree : sum 3 = 6 := rfl\n#eval sum 3",
            "6",
        ),
    ] {
        execute(source, expected);
    }
}

#[test]
fn context_distribution_retains_the_original_shared_match_type() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    // Distributing convert into the branches without an original-body typing
    // obligation would instantiate A as Bool and Nat independently and accept.
    let bad = b"def convert {A : Type} (unused : A) : Nat := 0\ndef loop (n : Nat) : Nat := convert (match n with | .zero => true | .succ k => loop k)";
    let error = base
        .check_source_files(
            &[bad],
            &KVMap::new(),
            SourceCheckLimits::new(limits().admission()),
        )
        .expect_err("the original match cannot have both Bool and Nat type");
    assert!(
        matches!(
            inference(&error),
            SourceInferenceError::TypeMismatch { .. } | SourceInferenceError::ConversionRefused(_)
        ),
        "{error:?}"
    );
    assert_eq!(error.disposition(), ("elaboration", false, 1));
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["convert"]))
    );
}

#[test]
fn surrounding_coercion_and_instance_choices_are_shared_by_every_branch() {
    // Lean v4.32.0 selects ConvertToNat Bool once. Re-elaborating convert in
    // each distributed branch would select ConvertToNat Nat in the successor
    // case and silently change loop 3 from 9 to 7.
    let base = Engine::with_coercion_seed(limits().admission())
        .unwrap()
        .into_complete()
        .unwrap();
    execute_on(
        &base,
        "class ConvertToNat (A : Type) where\n  convert : A -> Nat\ninstance convertNat : ConvertToNat Nat := ⟨fun value => 7⟩\ninstance convertBool : ConvertToNat Bool := ⟨fun value => 9⟩\ninstance natToBool : Coe Nat Bool := ⟨fun value => true⟩\ndef convert {A : Type} [ConvertToNat A] (value : A) : Nat := ConvertToNat.convert value\ndef loop (n : Nat) : Nat := convert (match n with | .zero => true | .succ k => loop k)\ntheorem selectedOnce : loop 3 = 9 := rfl\n#eval loop 3",
        "9",
    );
}

#[test]
fn contextual_recursion_cannot_hide_non_decreasing_or_escaping_calls() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for (body, diagnostic) in [
        (
            "(match n with | .zero => 0 | .succ k => loop n) + 1",
            "recursive call is not on an immediate recursive constructor field",
        ),
        (
            "(match n with | .zero => 0 | .succ k => loop (Nat.succ k)) + 1",
            "recursive call is not on an immediate recursive constructor field",
        ),
        (
            "(match n with | .zero => 0 | .succ k => let escaped := loop; escaped k) + 1",
            "recursive function escapes without its structural argument",
        ),
    ] {
        let source = format!("def beforeLoop : Nat := 7\ndef loop (n : Nat) : Nat := {body}");
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits().admission()),
            )
            .expect_err("invalid recursion must not publish any declaration");
        let SourceInferenceError::Recursion(reason) = inference(&error) else {
            panic!("expected a termination refusal: {error:?}");
        };
        assert_eq!(reason.to_string(), diagnostic);
        assert_eq!(error.disposition(), ("elaboration", false, 1));
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["beforeLoop"]))
        );
    }
}

#[test]
fn contextual_execution_stops_with_a_nonanswer_and_recovers_without_publication() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let source = b"def loop (n : Nat) : Nat := (match n with | .zero => 0 | .succ k => loop k) + 1\n#eval loop 100";
    let mut bounded = limits();
    bounded.vm.max_steps = 50;
    assert!(matches!(
        base.execute_source_definitions(&[source], &KVMap::new(), bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["loop"]))
    );
    execute(std::str::from_utf8(source).unwrap(), "101");
}
