//! `nat_lit n` (`rawNatLit`), elaborated as the pin's `elabRawNatLit`: `mkRawNatLit n`, a raw literal
//! of type `Nat` with no `OfNat` instance, which is how `OfNat α (nat_lit 0)` names a literal
//! instance. Every program here was run through the pinned `lean` v4.32.0 first (2026-10-11); a
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
fn raw_natural_literals_elaborate_as_at_the_pin() {
    for source in [
        "def a : Nat := nat_lit 3\ntheorem t : a = 3 := rfl\n",
        "def a : Nat := nat_lit 0x10\ntheorem t : a = 16 := rfl\n",
        "theorem t : nat_lit 2 = 2 := rfl\n",
        "class Z (α : Type) where\n  z : α\ninstance (α : Type) [OfNat α (nat_lit 0)] : Z α := ⟨0⟩\ndef w : Nat := Z.z\ntheorem t : w = 0 := rfl\n",
        "inductive S where\n  | zero | one\ninstance : OfNat S (nat_lit 0) where\n  ofNat := .zero\ndef s : S := 0\ntheorem t : s = S.zero := rfl\n",
        "variable (α : Type) [OfNat α (nat_lit 0)]\ndef zero : α := 0\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn raw_natural_literal_refusals_match_the_pin() {
    for (source, pin) in [
        ("def a : String := nat_lit 3\n", "Type mismatch"),
        (
            "theorem t : nat_lit 2 = 3 := rfl\n",
            "Not a definitional equality",
        ),
        (
            "def b := 1\ndef a : Nat := nat_lit b\n",
            "unexpected identifier; expected numeral",
        ),
        // The instance is for the literal 0 only.
        (
            "inductive S where\n  | zero | one\ninstance : OfNat S (nat_lit 0) where\n  ofNat := .zero\ndef s : S := 1\n",
            "failed to synthesize instance of type class",
        ),
    ] {
        assert!(check(source).is_err(), "accepted {source} (the pin: {pin})");
    }
}
