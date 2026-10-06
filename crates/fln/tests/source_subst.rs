//! `h ▸ e` through the real parser, elaborator, kernel and independent checker (the pin's
//! `elabSubst`, `Lean/Elab/BuiltinNotation.lean:457`).
//!
//! Every verdict and message below was taken from the pinned `lean` (v4.32.0) on the same
//! source, captured 2026-10-06. A message is the pin's own first line.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn check(
    source: &str,
) -> Result<Outcome<fln::SourceFileCheck>, fln::source_check::SourceCheckError> {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
}

/// The pin accepts each of these: the motive abstracts the equality's right side in the
/// expected type, and the operand is checked at its left side.
#[test]
fn substitution_rewrites_the_expected_type_along_the_equality() {
    for source in [
        "theorem t (x y z : Nat) (h1 : x = y) (h2 : y = z) : x = z := h2 ▸ h1",
        "theorem t (p : Nat → Prop) (x y : Nat) (h : x = y) (hp : p x) : p y := h ▸ hp",
        "theorem t (x y : Nat) (h : x = y) : y + 0 = y + 0 := h ▸ rfl",
        "theorem t (p : Nat → Prop) (x y z : Nat) (h1 : x = y) (h2 : y = z) (hp : p x) : p z := h2 ▸ h1 ▸ hp",
    ] {
        assert!(
            matches!(check(source), Ok(Outcome::Complete(_))),
            "{source}: {:?}",
            check(source)
        );
    }
}

/// The pin refuses this with this first line: neither side of the equality occurs in the
/// expected type.
#[test]
fn an_unmentioned_equality_is_refused_with_the_pins_message() {
    let source = "theorem t (x y : Nat) (h : x = y) : 1 = 1 := h ▸ (rfl : 2 = 2)";
    let error = check(source).expect_err(source);
    assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
    assert!(
        error
            .to_string()
            .contains("invalid `▸` notation, expected result type of cast is"),
        "{error}"
    );
}
