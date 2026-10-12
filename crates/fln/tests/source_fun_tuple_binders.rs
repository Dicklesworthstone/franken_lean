//! `fun (x, y) => e`, a lambda whose binder is a tuple, in the seed world: as the pin's
//! `expandFunBinders`, it is the pattern lambda `fun | (x, y) => e`, the tuple being its macro's
//! `Prod.mk x y` (`expandTuple`). These are the shapes of `fln-cli`'s `source_fun_tuple_binders`,
//! which runs each program through the pinned `lean` v4.32.0 first, here without imports (with
//! the pin's `Prod` declared) so they also run where the pin is absent.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

const PROD: &str = "structure Prod (α β : Type) where\n  fst : α\n  snd : β\n";

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn check(program: &str) -> Result<(), String> {
    let engine = Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let source = format!("{PROD}{program}");
    match engine.check_source_files(
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
fn a_tuple_binder_matches_its_pair() {
    for program in [
        "def f : Prod Nat Nat → Nat := fun (x, y) => x + y\ntheorem t : f (2, 3) = 5 := rfl\n",
        "def g (h : Prod Nat Nat → Nat) : Nat := h (1, 2)\n\
         def f : Nat := g (fun (x, y) => x * 10 + y)\ntheorem t : f = 12 := rfl\n",
        "def f : Prod Nat (Prod Nat Nat) → Nat := fun (x, y, z) => x + y + z\n\
         theorem t : f (1, 2, 3) = 6 := rfl\n",
    ] {
        check(program).unwrap_or_else(|error| panic!("{program}: {error}"));
    }
    for program in [
        "def f : Prod Nat Nat → Nat := fun (x, y) => x + y\ntheorem t : f (2, 3) = 6 := rfl\n",
        // A tuple is a `Prod`, never another structure's anonymous constructor.
        "structure P where\n  a : Nat\n  b : Nat\ndef f : P → Nat := fun (x, y) => x + y\n",
    ] {
        assert!(check(program).is_err(), "accepted {program}");
    }
}
