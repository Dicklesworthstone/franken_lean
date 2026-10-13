//! `noncomputable` in the seed world, through execution, which compiles what it checks: a
//! `noncomputable def` is checked and never compiled, and a computable definition that depends on
//! one is refused, as the pin refuses it ("failed to compile definition, consider marking it as
//! 'noncomputable' because it depends on 'a'"). These are the shapes of `fln-cli`'s
//! `source_noncomputable`, which runs each program through the pinned `lean` v4.32.0 first, here
//! without imports so they also run where the pin is absent.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn execute(source: &str) -> Result<(), String> {
    match engine().execute_source_definitions(
        &[source.as_bytes()],
        &KVMap::new(),
        EngineExecutionLimits::new(limits().kernel),
    ) {
        Ok(outcome) => {
            outcome
                .into_complete()
                .map_err(|_| "not complete".to_string())?;
            Ok(())
        }
        Err(error) => Err(error.to_string()),
    }
}

#[test]
fn noncomputable_definitions_are_checked_and_never_compiled() {
    for source in [
        // The control: without the tag the same dependency compiles and runs.
        "def a : Nat := 1\ndef b : Nat := a + 1\n",
        "noncomputable def a : Nat := 1\ntheorem t : a = 1 := rfl\n",
        "noncomputable def a : Nat := 1\nnoncomputable def b : Nat := a + 1\n",
        "noncomputable abbrev a : Nat := 1\n",
        "noncomputable def a : Nat := 1\ndef b (n : Nat) : Prop := a = n\n",
        "noncomputable def f (n : Nat) : Nat := n + 1\ntheorem t : f 2 = 3 := rfl\n",
    ] {
        execute(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn computable_code_that_depends_on_one_is_refused() {
    for source in [
        "noncomputable def a : Nat := 1\ndef b : Nat := a + 1\n",
        "noncomputable def a : Nat := 1\ndef c : Nat := (fun _ => 2) a\n",
        "namespace A\nnoncomputable def a : Nat := 1\nend A\ndef b : Nat := A.a\n",
        "noncomputable def f (n : Nat) : Nat := n + 1\ndef g (n : Nat) : Nat := f n\n",
        "noncomputable theorem t : 1 = 1 := rfl\n",
    ] {
        assert!(execute(source).is_err(), "accepted {source}");
    }
}
