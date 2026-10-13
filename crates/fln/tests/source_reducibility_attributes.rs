//! Reducibility attributes on a declaration, in the seed world: the status they set decides what
//! elaboration unfolds (`rfl` cannot see through an irreducible definition), and the pin's
//! `validate` transitions (vendored Lean/ReducibilityAttrs.lean) are refused as it refuses them.
//! These are the shapes of `fln-cli`'s `source_reducibility_attributes`, which runs each program
//! through the pinned `lean` v4.32.0 first, here without imports so they also run where the pin is
//! absent.
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
fn a_status_decides_what_rfl_unfolds() {
    for source in [
        "def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
        "@[reducible] def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
        "@[implicit_reducible] def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
        "@[irreducible] def g : Nat := 5\ntheorem t : g = g := rfl\n",
        "@[irreducible] def g : Nat := 5\ndef h : Nat := g + 1\n",
        "@[implicit_reducible, irreducible] def g : Nat := 5\n",
        "namespace A\n@[instance_reducible] def g : Nat := 5\nend A\ntheorem t : A.g = 5 := rfl\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
    for source in [
        "@[irreducible] def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
        "@[implicit_reducible, irreducible] def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
    ] {
        assert!(check(source).is_err(), "accepted {source}");
    }
}

#[test]
fn transitions_the_pin_refuses_are_refused() {
    for (source, pin) in [
        (
            "@[irreducible, reducible] def f : Nat := 1\n",
            "`f` is not currently `[semireducible]`",
        ),
        (
            "@[reducible, reducible] def f : Nat := 1\n",
            "`f` is not currently `[semireducible]`",
        ),
        (
            "@[semireducible] def f : Nat := 1\n",
            "declarations are `[semireducible]` by default",
        ),
        (
            "@[reducible] abbrev A := Nat\n",
            "`A` is not currently `[semireducible]`",
        ),
        (
            "@[reducible] theorem t : 1 = 1 := Eq.refl 1\n",
            "`t` is not a definition",
        ),
        ("@[reducible] opaque o : Nat\n", "`o` is not a definition"),
        (
            "@[reducible 3] def f : Nat := 1\n",
            "This attribute takes no arguments",
        ),
        (
            "@[scoped reducible] def f : Nat := 1\n",
            "Scoped attributes must be used inside namespaces",
        ),
    ] {
        assert!(check(source).is_err(), "accepted {source} (the pin: {pin})");
    }
}
