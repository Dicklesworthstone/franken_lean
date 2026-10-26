//! `h ▸ e` through the real parser, elaborator, kernel and independent checker (the pin's
//! `elabSubst`, `Lean/Elab/BuiltinNotation.lean:457`).
//!
//! Verdicts and messages are checked against pinned `lean` (v4.32.0). The
//! quantified-equality, conversion and rollback cases were checked 2026-10-26.
//! A diagnostic assertion uses the pin's own first line.
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

/// The cast's result supplies the arguments of a quantified equality. The
/// abstraction must unify matching heads, and retain the first successful
/// assignment when another occurrence has different arguments.
#[test]
fn substitution_infers_equality_arguments_from_matching_occurrences() {
    for source in [
        "theorem t (f g : Nat → Nat) (h : ∀ n, f n = g n) (p : Nat → Prop) (a : Nat) (hp : p (f a)) : p (g a) := h .. ▸ hp",
        "theorem t (f g : Nat → Nat) (h : ∀ {n}, f n = g n) (p : Nat → Prop) (a : Nat) (hp : p (f a)) : p (g a) := h ▸ hp",
        "theorem t (f g : Nat → Nat) (h : ∀ {n}, f n = g n) (p : Nat → Prop) (a : Nat) (hp : p (f a)) : p (g a) := (h) ▸ hp",
        "theorem t (f g : Nat → Nat) (h : ∀ {n}, f n = g n) (p : Nat → Prop) (a : Nat) (hp : p (f a)) : p (g a) := @h a ▸ hp",
        "theorem t (f g : Nat → Nat) (h : ∀ n, f n = g n) (p : Nat → Nat → Prop) (a b : Nat) (hp : p (f a) (g b)) : p (g a) (g b) := h .. ▸ hp",
        "theorem t (f g : Nat → Nat) (h : ∀ n, f n = g n) (p : Nat → Nat → Prop) (a : Nat) (hp : p (f a) (f a)) : p (g a) (g a) := h .. ▸ hp",
        "theorem t (f g : Nat → Nat → Nat) (h : ∀ m n, f m n = g m n) (p : Nat → Prop) (a b : Nat) (hp : p (f b a)) : p (g b a) := h _ a ▸ hp",
        "theorem t (f : Nat → Nat) (h : {n : Nat} → f n = n) (p : Nat → Prop) (a : Nat) (hp : p a) : p (f a) := h ▸ hp",
        "theorem t (f g : Nat → Nat) (h : ∀ n, f n = g n) (p : Nat → Prop) (a : Nat) (hp : ∀ x : Nat, p (f a)) : ∀ x : Nat, p (g a) := h _ ▸ hp",
        "def t (f g : Nat → Nat) (h : ∀ n, f n = g n) (p : Nat → Prop) (a : Nat) (hp : p (f a)) := h _ ▸ hp\ntheorem use (f g : Nat → Nat) (h : ∀ n, f n = g n) (p : Nat → Prop) (a : Nat) (hp : p (f a)) : p (g a) := t f g h p a hp",
    ] {
        let result = check(source);
        assert!(
            matches!(result, Ok(Outcome::Complete(_))),
            "{source}: {result:?}"
        );
    }
}

#[test]
fn substitution_preserves_explicit_and_strict_implicit_equality_arguments() {
    for source in [
        "theorem t (f g : Nat → Nat) (h : ∀ {n}, f n = g n) (p : Nat → Prop) (a : Nat) (hp : p (f a)) : p (g a) := @h ▸ hp",
        "theorem t (f g : Nat → Nat) (h : ∀ ⦃n⦄, f n = g n) (p : Nat → Prop) (a : Nat) (hp : p (f a)) : p (g a) := h ▸ hp",
    ] {
        let error = check(source).expect_err(source);
        assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
        assert!(
            error.to_string().contains("invalid `▸` notation, argument"),
            "{source}: {error}"
        );
    }
}

#[test]
fn substitution_rolls_back_failed_matches_and_uses_default_transparency() {
    for source in [
        // Matching `g a b` first assigns n := a, then fails on b. That
        // assignment must roll back so the following g c c can choose c.
        "theorem t (f g : Nat → Nat → Nat) (h : ∀ n, f n n = g n n) (p : Nat → Nat → Prop) (a b c : Nat) (hp : p (g a b) (f c c)) : p (g a b) (g c c) := h _ ▸ hp",
        // A regular definition unfolds inside a matching application.
        "def identity (n : Nat) : Nat := n\ntheorem t (f g : Nat → Nat) (p : Nat → Prop) (a : Nat) (h : f (identity a) = g (identity a)) (hp : p (f a)) : p (g a) := h ▸ hp",
    ] {
        let result = check(source);
        assert!(
            matches!(result, Ok(Outcome::Complete(_))),
            "{source}: {result:?}"
        );
    }
}

#[test]
fn substitution_retains_one_specialization_and_respects_binder_scope() {
    for source in [
        // The first g a fixes n := a; a single equality proof cannot also
        // rewrite the distinct g b occurrence using n := b.
        "theorem t (f g : Nat → Nat) (h : ∀ n, f n = g n) (p : Nat → Nat → Prop) (a b : Nat) (hp : p (f a) (f b)) : p (g a) (g b) := h _ ▸ hp",
        // A closed equality argument cannot capture a surrounding binder.
        "theorem t (f g : Nat → Nat) (h : ∀ n, f n = g n) (p : Nat → Prop) (hp : ∀ x : Nat, p (f x)) : ∀ x : Nat, p (g x) := h _ ▸ hp",
    ] {
        let error = check(source).expect_err(source);
        assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
    }
}

#[test]
fn substitution_does_not_treat_convertible_heads_or_bare_holes_as_occurrences() {
    for source in [
        "def wrap (f : Nat → Nat) (n : Nat) : Nat := f n\ntheorem t (f g : Nat → Nat) (p : Nat → Prop) (a : Nat) (h : f a = g a) (hp : p (f a)) : p (wrap g a) := h ▸ hp",
        "theorem t (f : Nat → Nat) (h : {n : Nat} → f n = n) (p : Nat → Prop) (a : Nat) (hp : p (f a)) : p a := h ▸ hp",
    ] {
        let error = check(source).expect_err(source);
        assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
        assert!(
            error
                .to_string()
                .contains("invalid `▸` notation, expected result type of cast is"),
            "{source}: {error}"
        );
    }
    // The same wrapped result is convertible once an explicit ascription
    // supplies a matching head to the substitution itself.
    let source = "def wrap (f : Nat → Nat) (n : Nat) : Nat := f n\ntheorem t (f g : Nat → Nat) (p : Nat → Prop) (a : Nat) (h : f a = g a) (hp : p (f a)) : p (wrap g a) := ((h ▸ hp) : p (g a))";
    let result = check(source);
    assert!(matches!(result, Ok(Outcome::Complete(_))), "{result:?}");
}
