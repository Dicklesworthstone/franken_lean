//! Native Option decisions must survive both checker seats at the public facade.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, Name, Outcome};
use fln_elab::check_definition_source;
use fln_kernel::verdict::Verdict;

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn engine() -> Engine {
    let result = Engine::with_source_seed(EngineAdmissionLimits::new(budget()))
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
fn option_decisions_are_available_without_manual_instance_registration() {
    let engine = engine();
    for source in [
        "theorem same : (Option.some 0 : Option Nat) = Option.some 0 := by decide",
        "theorem different : Not ((Option.some 0 : Option Nat) = Option.some 1) := by decide",
        "theorem empty_left : Not ((Option.none : Option Nat) = Option.some 0) := by decide",
        "theorem empty_right : Not ((Option.some 0 : Option Nat) = Option.none) := by decide",
        "theorem empty_same : (Option.none : Option Nat) = Option.none := by decide",
        "theorem nested : Option.some (Option.none : Option Bool) = Option.some (Option.none : Option Bool) := by decide",
        "theorem nested_different : Not (Option.some (Option.none : Option Bool) = Option.some (Option.some Bool.false)) := by decide",
        "def lifted {A : Type 1} [DecidableEq A] (x y : Option A) : Decidable (x = y) := decEq x y",
    ] {
        let checked = check_definition_source(source.as_bytes(), engine.environment(), budget())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        assert!(
            matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}\n{:?}",
            checked.outcome
        );
        let admitted = engine
            .admit_decl(checked.declaration, EngineAdmissionLimits::new(budget()))
            .unwrap_or_else(|error| panic!("{source}\nindependent admission: {error:?}"));
        assert!(
            matches!(admitted, Outcome::Complete(_)),
            "{source}\nindependent admission: {admitted:?}"
        );
    }
}

#[test]
fn false_option_claims_never_reach_a_successful_source_verdict() {
    let engine = engine();
    for source in [
        "theorem false_element : (Option.some 0 : Option Nat) = Option.some 1 := by decide",
        "theorem false_constructor : (Option.none : Option Nat) = Option.some 0 := by decide",
        "theorem false_negation : Not ((Option.some 0 : Option Nat) = Option.some 0) := by decide",
        "theorem false_nested : Option.some (Option.none : Option Bool) = Option.some (Option.some Bool.false) := by decide",
    ] {
        if let Ok(checked) =
            check_definition_source(source.as_bytes(), engine.environment(), budget())
        {
            assert!(
                !matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                "{source}"
            );
        }
    }
}
