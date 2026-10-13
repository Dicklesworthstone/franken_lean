//! `export Ns (a b …)`, as the pin's `elabExport` (vendored Lean/Elab/BuiltinCommand.lean):
//! - `Ns` resolves as `open` resolves it;
//! - each name must denote one declaration `ns ++ name`;
//! - `currentNamespace ++ name` becomes an alias of it.
//!
//! An export into the current namespace itself is refused. Every program here was run through the
//! pinned `lean` v4.32.0 first (2026-10-11), over `prelude` + `import Init.Core`; a refusal quotes
//! the pin's message.
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
fn exported_names_resolve_through_their_aliases() {
    for source in [
        "namespace Foo\ndef x : Nat := 1\nend Foo\nexport Foo (x)\ntheorem t : x = 1 := rfl\n",
        "namespace Foo\ndef x : Nat := 1\ndef y : Nat := 2\nend Foo\nexport Foo (x y)\ntheorem t : x + y = 3 := rfl\n",
        // The alias is `currentNamespace ++ name`.
        "namespace A\ndef n : Nat := 3\nend A\nnamespace B\nexport A (n)\nend B\ntheorem t : B.n = 3 := rfl\n",
        "class Get (α : Type) where\n  get : α\nexport Get (get)\ninstance : Get Nat := ⟨5⟩\ntheorem t : (get : Nat) = 5 := rfl\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn export_refusals_match_the_pin() {
    for (source, pin) in [
        (
            "namespace Foo\ndef x : Nat := 1\nend Foo\nexport Foo (y)\n",
            "Unknown identifier",
        ),
        (
            "namespace Foo\ndef x : Nat := 1\nexport Foo (x)\nend Foo\n",
            "invalid 'export', self export",
        ),
        ("export Nope (x)\n", "unknown namespace `Nope`"),
        (
            "namespace Foo\ndef x : Nat := 1\nend Foo\nexport Foo (x)\ntheorem t : x = 2 := rfl\n",
            "Not a definitional equality",
        ),
        // Without the export, `x` is not in scope.
        (
            "namespace Foo\ndef x : Nat := 1\nend Foo\ntheorem t : x = 1 := rfl\n",
            "Not a definitional equality (`x` is an auto-bound variable)",
        ),
    ] {
        assert!(check(source).is_err(), "accepted {source} (the pin: {pin})");
    }
}
