//! `{ tacs }` (`tacticSeqBracketed := "{" sepByIndent tactic "; " "}"`), run as the pin's
//! `evalTacticSeqBracketed`. Under `closeUsingOrAdmit`, its tactics run on the main goal alone and
//! must close it, as `·` does. A `by { … }` proof is that one focused block. Every program here was
//! run through the pinned `lean` v4.32.0 first (2026-10-11), over `prelude` + `import Init.Core`; a
//! refusal quotes the pin's message.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) -> Result<(), String> {
    match engine().check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    ) {
        Ok(outcome) => {
            outcome.into_complete().unwrap();
            Ok(())
        }
        Err(error) => Err(error.to_string()),
    }
}

#[test]
fn bracketed_sequences_close_their_focused_goal() {
    for source in [
        "theorem a (p : Prop) (hp : p) : p := by { exact hp }\n",
        "theorem b (p q : Prop) (hp : p) (hq : q) : p ∧ q := by { constructor; exact hp; exact hq }\n",
        "theorem c (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  { exact hp }\n  { exact hq }\n",
        "theorem d (p : Prop) (hp : p) : p := by { exact hp; }\n",
        "theorem e (p q : Prop) (hp : p) (hq : q) : p ∧ q := by {\n    constructor\n    exact hp\n    exact hq\n  }\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn bracketed_sequence_refusals_match_the_pin() {
    for (source, pin) in [
        // The block sees only the main goal: once `p` is closed, `exact hq` has no goal.
        (
            "theorem f (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  { exact hp; exact hq }\n",
            "No goals to be solved",
        ),
        (
            "theorem g (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  { constructor; exact hp }\n",
            "unsolved goals",
        ),
        (
            "theorem h (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  { exact hq }\n  { exact hp }\n",
            "Type mismatch",
        ),
        (
            "theorem i (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  { exact hp }\n",
            "unsolved goals",
        ),
    ] {
        assert!(check(source).is_err(), "accepted {source} (the pin: {pin})");
    }
}
