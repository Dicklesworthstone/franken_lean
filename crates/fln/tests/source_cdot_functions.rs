//! `·` functions through the real parser, elaborator, kernel and independent checker (bead
//! `franken_lean-z8j.1.10`; the pin's `Term.cdot` and `expandCDot?`,
//! `Lean/Elab/BuiltinNotation.lean:323`).
//!
//! Every verdict and message below was taken from the pinned `lean` (v4.32.0) on the same
//! file, captured 2026-10-05. Each accepted program also proves a computation by `by rfl`, so
//! the expansion's meaning is checked, not only its acceptance.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(
    source: &str,
) -> Result<Outcome<fln::SourceFileCheck>, fln::source_check::SourceCheckError> {
    engine().check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
}

/// The pin accepts each of these.
#[test]
fn cdots_become_functions_scoped_by_the_nearest_parentheses() {
    for source in [
        // one `·`, spelled `·` or `.`
        "def f : Nat → Nat := (· + 1)\ntheorem t : f 2 = 3 := by rfl",
        "def f : Nat → Nat := (. + 1)\ntheorem t : f 2 = 3 := by rfl",
        // several, bound left to right
        "def f : Nat → Nat → Nat := (· - ·)\ntheorem t : f 7 2 = 5 := by rfl",
        // as an application argument
        "def f : Nat → Nat := (Nat.sub · 2)\ntheorem t : f 7 = 5 := by rfl",
        // scoped by a type ascription
        "def f := (· : Nat → Nat)\ntheorem t : f 4 = 4 := by rfl",
        // a nested parenthesis scopes its own `·`
        "def g (h : (Nat → Nat) → Nat → Nat) : Nat → Nat := (h (· + 1) ·)\n\
         theorem t : g (fun k n => k (k n)) 5 = 7 := by rfl",
        // as method arguments
        "def s (xs : List Nat) : Nat := xs.foldl (· + ·) 0\ntheorem t : s [1, 2, 3] = 6 := by rfl",
        "def m : List Nat := [1, 2, 3].map (· * 2)\ntheorem t : m = [2, 4, 6] := by rfl",
        // the identity
        "def f : Nat → Nat := (·)\ntheorem t : f 9 = 9 := by rfl",
    ] {
        assert!(
            matches!(check(source), Ok(Outcome::Complete(_))),
            "{source}: {:?}",
            check(source)
        );
    }
}

/// The binder is hygienic. `fun x => (· - x) 10` is `10 - x`; a binder named plainly `x` would
/// capture the outer `x` and make it `x - x`, so `h 3` would be `0`, not the pin's `7`.
#[test]
fn a_cdot_binder_never_captures_a_source_name() {
    let source = "def h : Nat → Nat := fun x => (· - x) 10\ntheorem t : h 3 = 7 := by rfl";
    assert!(
        matches!(check(source), Ok(Outcome::Complete(_))),
        "{source}: {:?}",
        check(source)
    );
    let captured = "def h : Nat → Nat := fun x => (· - x) 10\ntheorem t : h 3 = 0 := by rfl";
    assert!(check(captured).is_err(), "{captured}");
}

/// The pin refuses a `·` that no parentheses, tuple or ascription scopes, with this message.
#[test]
fn an_unscoped_cdot_is_refused_with_the_pins_message() {
    for source in ["def b : Nat := · + 1", "def c : Nat → Nat := Nat.succ ·"] {
        let error = check(source).expect_err(source);
        assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
        assert!(
            error.to_string().contains(
                "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)"
            ),
            "{source}: {error}"
        );
    }
}
