//! Old-style structures, as the pin reads them: the body opened by `:=` (`" := " <|> " where "`,
//! Lean/Parser/Command.lean), `(x y : T := d)` fields declaring one field per name
//! (`expandFields`, Lean/Elab/Structure.lean), and `structFields`'s `manyIndent`: the first field
//! at any column, every later one at a column from the first one's on. Every program here was run
//! through the pinned `lean` v4.32.0 first (2026-10-11). On a `:=` body the pin only adds a
//! deprecation lint, a warning; a refusal quotes the pin's message.
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
fn old_style_structures_elaborate_as_at_the_pin() {
    for source in [
        // The first field at column 0, under `where` and under `:=`.
        "structure Foo where\nx : Nat\n\ndef f : Foo := ⟨1⟩\ntheorem t : f.x = 1 := rfl\n",
        "structure P where\nx : Nat\ny : Bool\ndef p : P := ⟨1, true⟩\ntheorem t : p.y = true := rfl\n",
        "structure Foo :=\n(x : Nat)\n\ndef f : Foo := ⟨1⟩\n",
        "structure Foo :=\n  (x : Nat)\n  (y : Nat)\ndef f : Foo := ⟨1, 2⟩\ntheorem t : f.y = 2 := rfl\n",
        // Bracketed fields sharing a line, one with a default.
        "structure Foo := (x : Nat) (y : Bool := true)\ndef f : Foo := ⟨1, false⟩\ndef g : Foo := { x := 2 }\ntheorem t : g.y = true := rfl\n",
        "structure Foo :=\n  x : Nat\ndef f : Foo := ⟨1⟩\n",
        "class C (α : Type) := (op : α → α)\ninstance : C Nat := ⟨Nat.succ⟩\ntheorem t : C.op (3 : Nat) = 4 := rfl\n",
        // A bracketed field, then a simple one at the same column or deeper.
        "structure Foo where\n  (x : Nat)\n  y : Nat\ndef f : Foo := ⟨1, 2⟩\n",
        "structure Foo where\n  (x : Nat)\n    y : Nat\ndef f : Foo := ⟨1, 2⟩\n",
        // Several names: one field each, sharing the type and the default.
        "structure Q := (a b : Nat) (c : Bool)\ndef q : Q := ⟨1, 2, true⟩\ntheorem t : q.b = 2 := rfl\n",
        "structure R := (a b : Nat := 5)\ndef r : R := { a := 1 }\ntheorem t : r.b = 5 := rfl\ntheorem u : r.a = 1 := rfl\n",
        "structure S : Type := (n : Nat)\ndef s : S := ⟨0⟩\n",
        "structure Pair (α : Type) := (fst : α) (snd : α)\ndef p : Pair Nat := ⟨1, 2⟩\ntheorem t : p.snd = 2 := rfl\n",
        "structure A := (x : Nat)\nstructure B extends A := (y : Nat)\ndef b : B := { x := 1, y := 2 }\ntheorem t : b.x = 1 := rfl\n",
        "structure E :=\ndef e : E := ⟨⟩\n",
        "structure F :=\n  /-- the x -/\n  (x : Nat)\ndef f : F := ⟨1⟩\n",
        "structure V := (n : Nat) (h : n = n)\ndef v : V := ⟨3, rfl⟩\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn old_style_structure_refusals_match_the_pin() {
    for (source, pin) in [
        // A later field left of the first one ends the command, as `manyIndent` does.
        (
            "structure A := (x : Nat)\n  (y : Nat)\n",
            "unexpected token '('; expected command",
        ),
        (
            "structure A where\n  (x : Nat)\n y : Nat\n",
            "unexpected identifier; expected command",
        ),
        (
            "structure A := (x : Nat) :=\n",
            "unexpected token ':='; expected command",
        ),
        (
            "structure A := (x : Nat) (x : Bool)\n",
            "Field `x` has already been declared",
        ),
        (
            "structure A := (x x : Nat)\n",
            "Field `x` has already been declared",
        ),
        ("structure A := (x : Nat := true)\n", "Type mismatch"),
        (
            "structure A := (x : Nat) (y : Nat)\ndef a : A := ⟨1⟩\n",
            "Insufficient number of fields for `⟨...⟩` constructor",
        ),
        (
            "structure A := (x y : Nat := 5)\ntheorem t : ({} : A).x = 4 := rfl\n",
            "Not a definitional equality",
        ),
    ] {
        assert!(check(source).is_err(), "accepted {source} (the pin: {pin})");
    }
}
