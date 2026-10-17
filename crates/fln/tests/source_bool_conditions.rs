//! `if b then t else e` on a `Bool`, in the seed world: decided as the pin's `ite (b = true) …`,
//! with the branches checked against the same expected type (`b` is never replaced by a
//! constructor in them), and `if h : b` binding `h : b = true`. These are the shapes of `fln-cli`'s
//! `source_bool_conditions`, which runs each program through the pinned `lean` v4.32.0 first, here
//! without imports so they also run where the pin is absent.
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
fn boolean_conditions_choose_their_branch() {
    for source in [
        "def f (b : Bool) : Nat := if b then 1 else 2\ntheorem t : f true = 1 := rfl\ntheorem u : f false = 2 := rfl\n",
        "def g (b : Bool) : Nat := if h : b then 1 else 2\ntheorem t : g false = 2 := rfl\ntheorem u : g true = 1 := rfl\n",
        "def g (b : Bool) : Nat := if h : b then (if h2 : b = true then 3 else 4) else 2\ntheorem t : g true = 3 := rfl\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
    for source in [
        "def f (b : Bool) : Nat := if b then 1 else 2\ntheorem t : f true = 2 := rfl\n",
        "def g (b : Bool) : Nat := if h : b then 1 else 2\ntheorem t : g true = 2 := rfl\n",
    ] {
        assert!(check(source).is_err(), "accepted {source}");
    }
}

/// The pin refuses both ("Type mismatch"): `b` is not known to be `true` in the first branch.
#[test]
fn branches_see_the_condition_unrefined() {
    for source in [
        "def f (b : Bool) : b = true ∨ b = false := if b then Or.inl rfl else Or.inr rfl\n",
        "def k (b : Bool) : (if b then Nat else Bool) := if b then (0 : Nat) else true\n",
    ] {
        assert!(check(source).is_err(), "accepted {source}");
    }
}
