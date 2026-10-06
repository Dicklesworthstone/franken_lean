//! A term whose type is RIGIDLY not its expected type is refused during elaboration with the
//! pin's "Type mismatch" (bead fln-azxg). "Rigidly" means that, after weak head normalization
//! and with no metavariables, the two heads are distinct constants that never reduce (inductive
//! types and axioms), or two of a sort, a Π-type and such a constant. Every other closed
//! mismatch is still left to the kernel, so refutation moves a refusal to elaboration and can
//! never turn an accept into a reject.
//!
//! Every verdict below is the pinned lean v4.32.0's on the same file, captured 2026-10-06.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
/// No coercion classes: a rigid mismatch is final at once.
fn source_seed() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
/// Coercion classes present: a rigid mismatch is final once no coercion path exists.
fn coercion_seed() -> Engine {
    Engine::with_coercion_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(
    engine: &Engine,
    source: &str,
) -> Result<Outcome<fln::SourceFileCheck>, fln::source_check::SourceCheckError> {
    engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
}

/// The pin refuses each with "Type mismatch"; so does the elaborator, before K1.
#[test]
fn rigid_mismatches_are_refused_at_elaboration() {
    for engine in [source_seed(), coercion_seed()] {
        for source in [
            // `String` is an axiom in the source seed, `Nat` an inductive.
            "def x : Nat := \"hello\"",
            "def f : Nat → Nat := (3 : Nat)",
            "def t : Type := (3 : Nat)",
        ] {
            let error = check(&engine, source).expect_err(source);
            assert_eq!(error.disposition().0, "elaboration", "{source}: {error}");
            assert!(
                error.to_string().contains("Type mismatch"),
                "{source}: {error}"
            );
        }
    }
}

/// The pin accepts each. None is a rigid mismatch: each type reaches its expected type only
/// after unfolding a definition, or differs only in universe levels, or has a coercion.
#[test]
fn types_equal_after_unfolding_or_by_coercion_are_not_refuted() {
    for (engine, source) in [
        (
            source_seed(),
            "def MyNat := Nat\ndef x : MyNat := (3 : Nat)",
        ),
        (
            source_seed(),
            "def A := Nat\ndef B := A\ndef x : B := (3 : Nat)",
        ),
        (
            source_seed(),
            "def F (n : Nat) : Type := Nat\ndef x : F 0 := (3 : Nat)",
        ),
        (
            source_seed(),
            "def Fn := Nat → Nat\ndef h : Fn := fun n => n + 1",
        ),
        (
            source_seed(),
            "universe u v\ndef f (α : Sort u) : Sort u := α\ndef g (β : Sort (max 1 v)) : Sort (max 1 v) := f β",
        ),
        (
            coercion_seed(),
            "structure Meters where\n  val : Nat\ninstance coeInst : Coe Nat Meters := ⟨fun n => ⟨n⟩⟩\ndef m : Meters := (5 : Nat)",
        ),
    ] {
        assert!(
            matches!(check(&engine, source), Ok(Outcome::Complete(_))),
            "{source}: {:?}",
            check(&engine, source)
        );
    }
}
