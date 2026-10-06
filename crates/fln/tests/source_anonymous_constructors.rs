//! `⟨a, b, …⟩` through the real parser, elaborator, kernel and independent checker
//! (bead `franken_lean-z8j.1.10`; the pin's `elabAnonymousCtor`,
//! `Lean/Elab/BuiltinNotation.lean:43`).
//!
//! Every verdict and message below was taken from the pinned `lean` (v4.32.0) on the same
//! file, captured 2026-10-05. A message is the pin's own first line; the pin also prints the
//! expected type inline in some messages, which is omitted here where noted.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

const POINT: &str = "structure Point where\n  x : Nat\n  y : Nat\n";

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
fn anonymous_constructors_expand_to_the_expected_types_constructor() {
    for source in [
        "theorem t (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩".to_string(),
        format!("{POINT}def p : Point := ⟨1, 2,⟩"),
        format!("{POINT}theorem t : (⟨1, 2⟩ : Point).y = 2 := rfl"),
        "structure W (α : Type) where\n  v : α\ndef w : W Nat := ⟨5⟩\ntheorem t : w.v = 5 := rfl"
            .to_string(),
    ] {
        assert!(
            matches!(check(&source), Ok(Outcome::Complete(_))),
            "{source}: {:?}",
            check(&source)
        );
    }
}

/// The pin refuses each of these during elaboration, with this message.
#[test]
fn anonymous_constructor_refusals_carry_the_pins_message() {
    for (source, message) in [
        (
            "def p := ⟨1, 2⟩".to_string(),
            "Invalid `⟨...⟩` notation: The expected type of this term could not be determined",
        ),
        (
            format!("{POINT}def p : Point := ⟨1⟩"),
            "Insufficient number of fields for `⟨...⟩` constructor: Constructor `Point.mk` has 2 explicit field, but only 1 was provided",
        ),
        // The pin: "The expected type `T` has more than one constructor".
        (
            "inductive T where | a | b\ndef p : T := ⟨⟩".to_string(),
            "Invalid `⟨...⟩` notation: The expected type has more than one constructor",
        ),
    ] {
        let error = check(&source).expect_err(&source);
        assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
        assert!(error.to_string().contains(message), "{source}: {error}");
    }
}

/// The pin nests extra arguments into the last field (`⟨1, 2, 3⟩ : Point` is
/// `Point.mk 1 ⟨2, 3⟩`, which it then rejects because `Nat` has more than one constructor).
/// That rewrite is not implemented: it is refused, never approximated.
#[test]
fn extra_arguments_nest_into_the_last_field() {
    // The pin nests `3` with `2` into `y`'s place: `⟨1, ⟨2, 3⟩⟩`. `y : Nat` has two
    // constructors, so the inner `⟨…⟩` is the pin's own refusal for that case.
    let source = format!("{POINT}def p : Point := ⟨1, 2, 3⟩");
    let error = check(&source).expect_err(&source);
    assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
    assert!(
        error.to_string().contains("has more than one constructor"),
        "{error}"
    );
    // A nested structure field takes the extra arguments.
    let source = format!(
        "{POINT}structure Seg where\n  a : Point\n  b : Point\ndef s : Seg := ⟨⟨0, 0⟩, 1, 2⟩"
    );
    assert!(
        matches!(check(&source), Ok(Outcome::Complete(_))),
        "{source}"
    );
}

/// Not yet: `[⟨1, 2⟩, ⟨3, 4⟩] : List Point`. The pin accepts it because `elabAppArgs`
/// propagates the expected type `List Point` into `List.cons`'s `α` before elaborating the
/// arguments (`propagateExpectedType`), and `elabAnonymousCtor` postpones while its expected
/// type is still a metavariable. This elaborator propagates only at the last argument and has
/// no postponement, so `⟨1, 2⟩` meets an unknown expected type and is refused with the pin's
/// own message for that case. A refusal, never an approximation.
#[test]
fn an_unknown_element_type_is_refused_until_expected_types_propagate() {
    let source = format!("{POINT}def k : List Point := [⟨1, 2⟩, ⟨3, 4⟩]");
    let error = check(&source).expect_err(&source);
    assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
    assert!(
        error
            .to_string()
            .contains("The expected type of this term could not be determined"),
        "{error}"
    );
}

/// `e.i` (`Term.proj` with a `fieldIdx`) projects the `i`-th field of `e`'s structure type,
/// counting from one; `h.2.1` is `(h.2).1`. The pin accepts each of these.
#[test]
fn numeric_projections_take_the_indexed_field() {
    for source in [
        "theorem t (p q : Prop) (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩".to_string(),
        "theorem t (p q r : Prop) (h : p ∧ q ∧ r) : q := h.2.1".to_string(),
        format!("{POINT}theorem t : (⟨1, 2⟩ : Point).2 = 2 := rfl"),
        format!("{POINT}def sum (p : Point) : Nat := p.1 + p.2\ntheorem t : sum ⟨3, 4⟩ = 7 := rfl"),
    ] {
        assert!(
            matches!(check(&source), Ok(Outcome::Complete(_))),
            "{source}: {:?}",
            check(&source)
        );
    }
}

/// The pin refuses each of these with this first line.
#[test]
fn numeric_projection_refusals_carry_the_pins_message() {
    for (source, message) in [
        (
            "theorem t (p q : Prop) (h : p ∧ q) : q := h.3",
            "Invalid projection: Index `3` is invalid for this structure; it must be between 1 and 2",
        ),
        (
            "def n (x : Nat) : Nat := x.1",
            "Invalid projection: Projections extract constructor fields for one-constructor inductive types.",
        ),
    ] {
        let error = check(source).expect_err(source);
        assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
        assert!(error.to_string().contains(message), "{source}: {error}");
    }
}

/// `⟨p, …⟩` as a pattern names the matched type's only constructor, in `match` and in
/// equations, nested or not. The pin accepts each of these.
#[test]
fn anonymous_constructor_patterns_match_the_only_constructor() {
    for source in [
        "theorem t (p q : Prop) (h : p ∧ q) : q ∧ p := match h with | ⟨hp, hq⟩ => ⟨hq, hp⟩"
            .to_string(),
        "theorem t (p q r : Prop) (h : p ∧ (q ∧ r)) : r := match h with | ⟨_, ⟨_, hr⟩⟩ => hr"
            .to_string(),
        format!(
            "{POINT}def sum : Point → Nat\n  | ⟨a, b⟩ => a + b\ntheorem t : sum ⟨3, 4⟩ = 7 := rfl"
        ),
        format!(
            "{POINT}def swap (p : Point) : Point := match p with | ⟨a, b⟩ => ⟨b, a⟩\ntheorem t : (swap ⟨1, 2⟩).x = 2 := rfl"
        ),
    ] {
        assert!(
            matches!(check(&source), Ok(Outcome::Complete(_))),
            "{source}: {:?}",
            check(&source)
        );
    }
}

/// The pin: "Invalid `⟨...⟩` notation: The expected type `Nat` has more than one
/// constructor" (the type is omitted here).
#[test]
fn an_anonymous_constructor_pattern_on_a_many_constructor_type_is_refused() {
    let source = "def k (n : Nat) : Nat := match n with | ⟨a⟩ => a";
    let error = check(source).expect_err(source);
    assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
    assert!(
        error
            .to_string()
            .contains("Invalid `⟨...⟩` notation: The expected type has more than one constructor"),
        "{error}"
    );
}
