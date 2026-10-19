//! Data-valued transport must use the same ordinary recursor at every universe.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn check(
    source: &str,
) -> Result<Outcome<fln::SourceFileCheck>, fln::source_check::SourceCheckError> {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
}

#[test]
fn casts_preserve_data_universes_and_inference_only_reverse_orientation() {
    for source in [
        "def t (F : Nat → Type) (a b : Nat) (h : a = b) (x : F b) : F b := h ▸ x",
        "def t (F : Nat → Type) (a b : Nat) (h : a = b) (x : F b) : F a := h ▸ x",
        "def t (F : Nat → Type) (a b : Nat) (h : a = b) (x : F b) := h ▸ x",
        "universe u v\ndef t {A : Sort u} (F : A → Sort v) (a b : A) (h : a = b) (x : F b) : F b := h ▸ x",
    ] {
        let result = check(source);
        assert!(
            matches!(result, Ok(Outcome::Complete(_))),
            "{source}: {result:?}"
        );
    }
}
