//! Equation-style definitions take a pattern column for every binder of the declared type,
//! implicit and instance ones included. The pin's `expandMatchAltsWhereDecls` (vendored
//! Lean/Elab/Binders.lean:628) wraps the equations' match in one `@fun x =>` per column, and `@fun`
//! binds the type's implicit and instance binders too. A header binder (`def f {n : Nat} : …`) is
//! no column. Every program here was run through the pinned `lean` v4.32.0 first (2026-10-11), over
//! `prelude` + `import Init.Core`; a refusal quotes the pin's message.
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

const VEC: &str = "inductive Vec (α : Type) : Nat → Type where\n  | nil : Vec α 0\n  | cons : α → Vec α n → Vec α (n + 1)\n";

#[test]
fn every_binder_of_the_declared_type_is_a_pattern_column() {
    for source in [
        "def h : {n : Nat} → Nat → Nat\n  | n, m => n + m\ntheorem t : @h 2 3 = 5 := rfl\n"
            .to_string(),
        "def h : {α : Type} → [Inhabited α] → α → α\n  | _, _, a => a\n".to_string(),
        format!(
            "{VEC}def head : {{n : Nat}} → Vec Nat (n + 1) → Nat\n  | _, Vec.cons a _ => a\ntheorem t : head (Vec.cons 7 Vec.nil) = 7 := rfl\n"
        ),
        format!(
            "{VEC}def len : {{n : Nat}} → Vec Nat n → Nat\n  | _, Vec.nil => 0\n  | _, Vec.cons _ v => len v + 1\n"
        ),
        // A header binder is no column.
        format!(
            "{VEC}def len {{n : Nat}} : Vec Nat n → Nat\n  | Vec.nil => 0\n  | Vec.cons _ _ => 1\n"
        ),
    ] {
        check(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn column_count_refusals_match_the_pin() {
    for (source, pin) in [
        (
            "def h : {n : Nat} → Nat → Nat\n  | m => m\n".to_string(),
            "Type mismatch (`m` is the implicit `n`'s column)",
        ),
        (
            "def h : {α : Type} → [Inhabited α] → α → α\n  | a => a\n".to_string(),
            "Type mismatch (`a` is `α`'s column)",
        ),
        (
            format!(
                "{VEC}def len {{n : Nat}} : Vec Nat n → Nat\n  | _, Vec.nil => 0\n  | _, Vec.cons _ _ => 1\n"
            ),
            "Type mismatch (a header binder is no column)",
        ),
        (
            format!(
                "{VEC}def head : {{n : Nat}} → Vec Nat (n + 1) → Nat\n  | _, Vec.cons a _ => a\ntheorem t : head (Vec.cons 7 Vec.nil) = 8 := rfl\n"
            ),
            "Not a definitional equality",
        ),
    ] {
        assert!(
            check(&source).is_err(),
            "accepted {source} (the pin: {pin})"
        );
    }
}
