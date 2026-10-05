//! `.c` through the real parser, elaborator, kernel and independent checker (bead
//! `franken_lean-z8j.1.10`; the pin's `Term.dotIdent` and `resolveDottedIdentFn`,
//! `Lean/Elab/App.lean:1984`).
//!
//! Every verdict and message below was taken from the pinned `lean` (v4.32.0) on the same
//! file, captured 2026-10-05. A message is the pin's own first line; where the pin prints a
//! type or a hint after it, that tail is omitted and the comparison is a prefix.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

const T: &str = "inductive T where\n  | leaf\n  | node (l r : T)\n";

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
fn dotted_identifiers_resolve_in_the_expected_types_namespace() {
    for source in [
        // a value, an application head with nested heads, and a `fun` body
        format!("{T}def x : T := .leaf"),
        format!("{T}def y : T := .node .leaf (.node .leaf .leaf)"),
        format!("{T}def f : Nat → T := fun _ => .leaf"),
        // the namespace of a type applied to arguments
        "def z : Option Nat := .some 1".to_string(),
        // the bodies of the expected type's `∀`s are entered (`withForallBody`)
        "def g : Nat → Option Nat := .some".to_string(),
        // a definition heading the expected type is unfolded (`unfoldDefinition?`)
        format!("{T}def MyT := T\ndef m : MyT := .leaf"),
        // stage-2 target I04's definitions, with its field notation spelled out (`l.size` on
        // a non-structure inductive is the generalized field notation, not yet elaborated);
        // the `rfl` holds only if each `.leaf` is exactly `T.leaf`
        format!(
            "{T}def T.size : T → Nat\n  | .leaf => 1\n  | .node l r => T.size l + T.size r + 1\n\
             theorem t : T.size (T.node .leaf .leaf) = T.size (T.node T.leaf T.leaf) := rfl"
        ),
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
fn dotted_identifier_refusals_carry_the_pins_message() {
    for (source, message) in [
        // The pin also prints a hint naming the constants that would be unambiguous.
        (
            format!("{T}def p := .leaf"),
            "Invalid dotted identifier notation: The expected type of `.leaf` could not be determined",
        ),
        (format!("{T}def q : T := .foo"), "Unknown constant `T.foo`"),
        (
            "def r : Type := .leaf".to_string(),
            "Invalid dotted identifier notation: Not supported on type universe",
        ),
        (
            format!("{T}def s : T := .leaf.x"),
            "Invalid dotted identifier notation: The name `leaf.x` must be atomic",
        ),
    ] {
        let error = check(&source).expect_err(&source);
        assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
        assert!(error.to_string().contains(message), "{source}: {error}");
    }
}

/// The pin refuses `.node .leaf : T` and the spelled-out `T.node T.leaf : T` alike ("Type
/// mismatch": the partial application is a function). This engine refuses both alike too:
/// the dotted head resolves to the same constant, and the mismatch is caught at the same
/// stage as for the spelled-out form (today the kernel, after elaboration).
#[test]
fn a_partially_applied_dotted_head_is_refused_like_its_spelled_out_form() {
    let dotted = format!("{T}def v : T := .node .leaf");
    let spelled = format!("{T}def v : T := T.node T.leaf");
    let dotted = check(&dotted).expect_err(&dotted);
    let spelled = check(&spelled).expect_err(&spelled);
    assert_eq!(
        dotted.disposition().0,
        spelled.disposition().0,
        "{dotted} / {spelled}"
    );
}

/// I04's own `T.size (T.node .leaf .leaf) = 3 := rfl` needs `rfl` to compute through the
/// structural recursion, which this engine's unifier does not yet do: it is refused, and
/// exactly as the spelled-out `T.size (T.node T.leaf T.leaf) = 3` is. The dotted spelling
/// changes nothing about the verdict.
#[test]
fn a_computing_proof_gets_the_same_verdict_dotted_or_spelled_out() {
    let size = "def T.size : T → Nat\n  | .leaf => 1\n  | .node l r => T.size l + T.size r + 1\n";
    let dotted = format!("{T}{size}theorem t : T.size (T.node .leaf .leaf) = 3 := rfl");
    let spelled = format!("{T}{size}theorem t : T.size (T.node T.leaf T.leaf) = 3 := rfl");
    let dotted = check(&dotted)
        .map(|_| ())
        .map_err(|error| error.to_string());
    let spelled = check(&spelled)
        .map(|_| ())
        .map_err(|error| error.to_string());
    assert_eq!(dotted, spelled);
}

/// Not yet: `[.leaf, .node .leaf .leaf] : List T`. As for `⟨…⟩` in a list, the pin
/// propagates `List T` into `List.cons`'s `α` before elaborating the elements, and postpones
/// `.leaf` while its expected type is a metavariable; this elaborator does neither, so the
/// element meets an unknown expected type and is refused with the pin's message for that.
#[test]
fn an_unknown_element_type_is_refused_until_expected_types_propagate() {
    let source = format!("{T}def k : List T := [.leaf, .node .leaf .leaf]");
    let error = check(&source).expect_err(&source);
    assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
    assert!(
        error
            .to_string()
            .contains("The expected type of `.leaf` could not be determined"),
        "{error}"
    );
}
