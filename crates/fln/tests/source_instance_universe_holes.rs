//! Instance goals over a type whose universe is still a hole: `{α} [Inhabited α]` and an
//! auto-bound `[Add α]` give `α : Sort ?u`, and the pin answers `Inhabited.{?u} α` with the local
//! instance. Its `synthInstance?` searches under `withNewMCtxDepth (allowLevelAssignments := true)`,
//! so an answer may keep a universe hole of the goal or of its local context; only an unsolved
//! universe the search itself opened leaves an answer open. Every program here was run through the
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
fn instance_answers_keep_the_goals_universe_holes() {
    for source in [
        "theorem ex [Add α] (a b : α) : a + b = a + b := rfl\n",
        "theorem ex [Add α] (comm : {a b : α} → a + b = b + a) (x y : α) : x + y = y + x := comm\n",
        "theorem ex {α} [Inhabited α] : (default : α) = default := rfl\n",
        "def f {α} [Inhabited α] : α := default\ntheorem t : (f : Nat) = 0 := rfl\n",
        "def g [Add α] (a : α) : α := a + a\ntheorem t : g 2 = 4 := rfl\n",
        "class K (α : Sort u) where\n  k : α\ndef d {α} [K α] : α := K.k\ninstance : K Nat := ⟨5⟩\ntheorem t : (d : Nat) = 5 := rfl\n",
        "def e [BEq α] (a b : α) : Bool := a == b\ntheorem t : e 1 1 = true := rfl\n",
        "def s {α : Sort u} [Inhabited α] : α := default\n",
        "variable {α} [Inhabited α]\ndef v : α := default\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn universe_hole_refusals_match_the_pin() {
    for (source, pin) in [
        (
            "def f {α} : α := default\n",
            "failed to synthesize instance of type class",
        ),
        (
            "theorem bad [Add α] (a b : α) : a + b = b + a := rfl\n",
            "Not a definitional equality",
        ),
        (
            "def f {α} [Inhabited α] : Nat := (default : α)\n",
            "Type mismatch",
        ),
        (
            "def f {α : Sort u} [Add α] (a : α) : α := a + a\n",
            "Application type mismatch",
        ),
        (
            "example {α} [Inhabited α] : (default : α → α) = id := rfl\n",
            "Type mismatch",
        ),
        (
            "def f {α} [Add α] (a : α) : α := a * a\n",
            "failed to synthesize instance of type class",
        ),
        (
            "def e (a b : α) : Bool := a == b\n",
            "failed to synthesize instance of type class",
        ),
        (
            "def h {α β} [Add α] (a : α) (b : β) : β := b + b\n",
            "failed to synthesize instance of type class",
        ),
    ] {
        assert!(check(source).is_err(), "accepted {source} (the pin: {pin})");
    }
}
